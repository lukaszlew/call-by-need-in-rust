pub mod expr;
pub mod expr_parser;

use std::cell::RefCell;
use std::collections::HashMap;

pub use expr::{Expr, Var};

/// Environment mapping variable names to heap pointers.
pub type Env = HashMap<Var, HeapPtr>;

/// Extension trait for convenient Env access in closures.
pub trait EnvExt {
    fn v(&self, name: &str) -> HeapPtr;
}

impl EnvExt for Env {
    fn v(&self, name: &str) -> HeapPtr {
        self[&Var::new(name)]
    }
}

/// The body of a closure - either Rust code or pre-allocated HeapPtr code.
#[derive(Clone)]
pub enum ClosureBody {
    Rust(fn(&Env, &Runtime) -> HeapPtr),
    /// Pre-allocated body with Param holes for variables.
    Code(HeapPtr),
}

/// Runtime representation of a lambda.
///
/// # Lexical Scoping
/// Each closure captures its environment at creation time (the `env` field).
/// When applied, we extend this captured env with the argument - we don't look up
/// variables in the caller's environment. This is lexical (static) scoping.
///
/// # Why No Capture-Avoiding Substitution Needed
/// We never substitute terms into terms. Instead:
/// 1. When a lambda is instantiated, we capture current bindings into `env`
/// 2. When applied, we extend `env` with param→arg and run the body
/// 3. Variable lookup goes through `env`, not through textual substitution
///
/// This environment-based approach sidesteps capture issues entirely.
#[derive(Clone)]
pub struct Closure {
    pub param: Var,
    pub env: Env,
    pub body: ClosureBody,
}

// HeapObj represents unevaluated (App) or evaluated (I32, Closure) lambda calculus terms.
// Evaluation transmutes App into I32 or Closure.
//
// https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/storage/heap-objects
#[derive(Clone)]
pub enum HeapObj {
    App(HeapPtr, HeapPtr),
    I32(i32),
    Closure(Closure),
    /// Variable hole, resolved via env in eval_code.
    Param(Var),
    ReadbackFreeVar {
        /// `{ var: Var("x0"), spine: [a, b] }` represents `x0 a b`
        var: Var,
        spine: Vec<HeapPtr>,
    },
}

impl HeapObj {
    fn unwrap_i32(self) -> i32 {
        match self {
            HeapObj::I32(n) => n,
            _ => panic!("expected i32"),
        }
    }
}

// HeapPtr is an index into Runtime's heap.
#[derive(Clone, Copy, Debug)]
pub struct HeapPtr(usize);

/// Which force implementation to use.
#[derive(Clone, Copy, Debug, Default)]
pub enum ForceMode {
    Recursive,
    #[default]
    Iterative,
}

// =============================================================================
// Runtime
// =============================================================================

/// Runtime for the lambda calculus with explicit heap.
pub struct Runtime {
    objects: RefCell<Vec<HeapObj>>,
    /// Which force implementation to use.
    mode: ForceMode,
}

impl Runtime {
    #[must_use]
    pub fn new(mode: ForceMode) -> Self {
        Runtime {
            objects: RefCell::new(Vec::new()),
            mode,
        }
    }

    /// Number of heap objects allocated.
    #[must_use]
    pub fn heap_size(&self) -> usize {
        self.objects.borrow().len()
    }

    /// Force and extract i32.
    #[must_use]
    pub fn get_i32(&self, ptr: HeapPtr) -> i32 {
        self.force(ptr).unwrap_i32()
    }

    /// Mutate heap object to i32. Breaks referential transparency.
    /// Panics if the existing value is not I32.
    pub fn set_i32(&self, ptr: HeapPtr, val: i32) {
        let mut objects = self.objects.borrow_mut();
        assert!(matches!(objects[ptr.0], HeapObj::I32(_)));
        objects[ptr.0] = HeapObj::I32(val);
    }

    fn force(&self, ptr: HeapPtr) -> HeapObj {
        match self.mode {
            ForceMode::Recursive => self.force_recursive(ptr),
            ForceMode::Iterative => self.force_iter(ptr),
        }
    }

    /// Apply a function to an argument. Handles closures and neutral terms.
    fn apply(&self, closure: HeapObj, arg: HeapPtr) -> HeapPtr {
        match closure {
            HeapObj::Closure(c) => {
                let mut env = c.env;
                let None = env.insert(c.param.clone(), arg) else {
                    panic!("param {:?} shadows capture", c.param)
                };
                match c.body {
                    ClosureBody::Rust(code) => code(&env, self),
                    ClosureBody::Code(body) => self.eval_code(body, &env),
                }
            }
            HeapObj::ReadbackFreeVar { var, mut spine } => {
                spine.push(arg);
                self.alloc(HeapObj::ReadbackFreeVar { var, spine })
            }
            _ => panic!("expected closure"),
        }
    }

    /// Update a thunk with its evaluated result (memoization).
    fn update(&self, thunk: HeapPtr, value: HeapObj) {
        self.objects.borrow_mut()[thunk.0] = value;
    }

    // Lazy call-by-need evaluation: force App(f, arg) by forcing f, applying it to arg,
    // forcing the result, and caching the result in place of the App.
    // Recursive version - simple but can overflow stack on deep thunk chains.
    fn force_recursive(&self, ptr: HeapPtr) -> HeapObj {
        let obj = self.objects.borrow()[ptr.0].clone();
        match obj {
            HeapObj::App(f, arg) => {
                let result_ptr = self.apply(self.force_recursive(f), arg);
                let result = self.force_recursive(result_ptr);
                self.update(ptr, result.clone());
                result
            }
            v => v,
        }
    }

    // Iterative version with explicit stack - handles arbitrary depth.
    // This is closer to STG's eval/apply loop.
    fn force_iter(&self, mut ptr: HeapPtr) -> HeapObj {
        enum UseValueTo {
            ApplyArg(HeapPtr),
            UpdateThunk(HeapPtr),
        }
        let mut stack: Vec<UseValueTo> = vec![];

        loop {
            let obj = self.objects.borrow()[ptr.0].clone();
            match obj {
                HeapObj::App(f, arg) => {
                    stack.push(UseValueTo::UpdateThunk(ptr));
                    stack.push(UseValueTo::ApplyArg(arg));
                    ptr = f
                }
                value => match stack.pop() {
                    None => return value,
                    Some(UseValueTo::UpdateThunk(thunk)) => {
                        self.update(thunk, value.clone());
                        ptr = thunk
                    }
                    Some(UseValueTo::ApplyArg(arg)) => ptr = self.apply(value, arg),
                },
            }
        }
    }

    // -------------------------------------------------------------------------
    // Allocation
    // -------------------------------------------------------------------------

    fn alloc(&self, obj: HeapObj) -> HeapPtr {
        let mut objects = self.objects.borrow_mut();
        let ptr = HeapPtr(objects.len());
        objects.push(obj);
        ptr
    }

    /// Create a Closure with Rust code body.
    /// `param` is the name for the argument when the closure is applied.
    /// `env` is a list of (name, value) pairs to capture.
    /// Access variables in the closure via `env.v("name")`.
    #[must_use]
    pub fn lam(
        &self,
        param: &str,
        env: &[(&str, HeapPtr)],
        f: fn(&Env, &Runtime) -> HeapPtr,
    ) -> HeapPtr {
        self.alloc(HeapObj::Closure(Closure {
            param: Var::new(param),
            env: env.iter().map(|(k, v)| (Var::new(*k), *v)).collect(),
            body: ClosureBody::Rust(f),
        }))
    }

    /// Create HeapPtr for i32.
    #[must_use]
    pub fn i32(&self, n: i32) -> HeapPtr {
        self.alloc(HeapObj::I32(n))
    }

    /// Allocate unevaluated lambda application.
    #[must_use]
    pub fn app(&self, f: HeapPtr, arg: HeapPtr) -> HeapPtr {
        self.alloc(HeapObj::App(f, arg))
    }

    /// plus = \a.\b. a + b (primitive addition for i32)
    #[must_use]
    pub fn plus(&self) -> HeapPtr {
        self.lam("a", &[], |env, rt| {
            rt.lam("b", &[("a", env.v("a"))], |env, rt| {
                rt.i32(rt.get_i32(env.v("a")) + rt.get_i32(env.v("b")))
            })
        })
    }

    // -------------------------------------------------------------------------
    // FOAS: Term execution
    // -------------------------------------------------------------------------

    /// Evaluate pre-allocated code with environment.
    fn eval_code(&self, ptr: HeapPtr, env: &Env) -> HeapPtr {
        let obj = self.objects.borrow()[ptr.0].clone();
        match obj {
            HeapObj::Param(v) => env[&v],
            HeapObj::App(f, g) => {
                let f_ptr = self.eval_code(f, env);
                let g_ptr = self.eval_code(g, env);
                self.app(f_ptr, g_ptr)
            }
            HeapObj::Closure(mut c) => {
                assert!(c.env.is_empty(), "closure env must be empty (from expr_impl)");
                // Capture env into closure
                for (var, val) in env {
                    if var != &c.param {
                        c.env.insert(var.clone(), *val);
                    }
                }
                self.alloc(HeapObj::Closure(c))
            }
            HeapObj::I32(_) | HeapObj::ReadbackFreeVar { .. } => ptr,
        }
    }

    /// Allocate Expr to heap. All Vars become Param holes.
    fn expr_impl(&self, expr: &Expr) -> HeapPtr {
        match expr {
            Expr::Var(v) => self.alloc(HeapObj::Param(v.clone())),
            Expr::Int(n) => self.i32(*n),
            Expr::App { head, spine } => {
                let mut ptr = self.expr_impl(head);
                for arg in spine {
                    ptr = self.app(ptr, self.expr_impl(arg));
                }
                ptr
            }
            Expr::Lam { param, body } => {
                let body_ptr = self.expr_impl(body);
                self.alloc(HeapObj::Closure(Closure {
                    param: param.clone(),
                    env: HashMap::new(),
                    body: ClosureBody::Code(body_ptr),
                }))
            }
            Expr::Plus => self.plus(),
        }
    }

    /// Allocate a Term with the given environment, producing a HeapPtr.
    #[must_use]
    pub fn expr(&self, env: &Env, expr: &Expr) -> HeapPtr {
        self.eval_code(self.expr_impl(expr), env)
    }

    /// Parse and evaluate an expression string.
    #[must_use]
    pub fn run(&self, src: &str) -> HeapPtr {
        self.expr(&HashMap::new(), &expr_parser::parse(src))
    }

    // -------------------------------------------------------------------------
    // Normalization by Evaluation (NbE)
    // -------------------------------------------------------------------------

    /// Convert a runtime value to its β-normal form as an Expr.
    /// `depth` is the current de Bruijn level for fresh variables.
    #[must_use]
    pub fn readback(&self, ptr: HeapPtr, depth: usize) -> Expr {
        let obj = self.force(ptr);
        match obj {
            HeapObj::Closure(_) => {
                let param = Var::new(format!("x{depth}"));
                let free_var = self.alloc(HeapObj::ReadbackFreeVar {
                    var: param.clone(),
                    spine: vec![],
                });
                let body = self.apply(obj, free_var);
                Expr::lam(param, self.readback(body, depth + 1))
            }
            HeapObj::ReadbackFreeVar { var, spine } => Expr::app(
                Expr::Var(var),
                spine.into_iter().map(|arg| self.readback(arg, depth)).collect(),
            ),
            HeapObj::I32(n) => Expr::Int(n),
            HeapObj::App(_, _) => panic!("unevaluated App in readback"),
            HeapObj::Param(v) => panic!("unresolved Param({v:?}) in readback"),
        }
    }

    /// Parse, evaluate, and normalize an expression to β-normal form.
    #[must_use]
    pub fn normalize(&self, src: &str) -> Expr {
        self.readback(self.run(src), 0)
    }
}

// ============================================================================
// Didactic tests: These tests demonstrate key concepts of call-by-need.
// ============================================================================
#[cfg(test)]
mod test {
    use crate::{EnvExt, ForceMode, HeapPtr, Runtime};
    use rstest::rstest;

    /// Create an increment function that increments counter when called.
    fn counted_inc(rt: &Runtime, counter: HeapPtr) -> HeapPtr {
        rt.lam("x", &[("counter", counter)], |env, rt| {
            rt.set_i32(env.v("counter"), rt.get_i32(env.v("counter")) + 1);
            rt.i32(rt.get_i32(env.v("x")) + 1)
        })
    }

    /// Create a thunk that returns `val` and increments counter when forced.
    fn counted_const(rt: &Runtime, counter: HeapPtr, val: i32) -> HeapPtr {
        let val_ptr = rt.i32(val);
        rt.lam("_", &[("counter", counter), ("val", val_ptr)], |env, rt| {
            rt.set_i32(env.v("counter"), rt.get_i32(env.v("counter")) + 1);
            rt.i32(rt.get_i32(env.v("val")))
        })
    }

    // -------------------------------------------------------------------------
    // Basic application: (\x -> x) 5 = 5
    // -------------------------------------------------------------------------
    #[rstest]
    fn identity_applied(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let t = rt.app(rt.lam("x", &[], |env, _rt| env.v("x")), rt.i32(5));
        assert_eq!(rt.get_i32(t), 5);
    }

    // -------------------------------------------------------------------------
    // Primitive addition: plus 3 4 = 7
    // -------------------------------------------------------------------------
    #[rstest]
    fn plus_primitive(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        assert_eq!(
            rt.get_i32(rt.app(rt.app(rt.plus(), rt.i32(3)), rt.i32(4))),
            7
        );
    }

    // -------------------------------------------------------------------------
    // Currying: fst and snd projections.
    // fst = \x.\y.x    snd = \x.\y.y
    // -------------------------------------------------------------------------
    #[rstest]
    fn fst_and_snd(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let fst = rt.lam("x", &[], |env, rt| rt.lam("y", &[("x", env.v("x"))], |env, _rt| env.v("x")));
        let snd = rt.lam("x", &[], |_env, rt| rt.lam("y", &[], |env, _rt| env.v("y")));

        assert_eq!(rt.get_i32(rt.app(rt.app(fst, rt.i32(5)), rt.i32(6))), 5);
        assert_eq!(rt.get_i32(rt.app(rt.app(snd, rt.i32(5)), rt.i32(6))), 6);
    }

    // -------------------------------------------------------------------------
    // Laziness: unused arguments are never evaluated.
    // const 42 expensive = 42, and expensive is never called.
    // -------------------------------------------------------------------------
    #[rstest]
    fn unused_argument_not_evaluated(
        #[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode,
    ) {
        let rt = Runtime::new(mode);
        let counter = rt.i32(0);
        let expensive = counted_const(&rt, counter, 999);

        // const = \x.\y. x (ignores second argument)
        let const_fn = rt.lam("x", &[], |env, rt| rt.lam("y", &[("x", env.v("x"))], |env, _rt| env.v("x")));

        let unused_thunk = rt.app(expensive, rt.i32(0));
        let result = rt.app(rt.app(const_fn, rt.i32(42)), unused_thunk);

        assert_eq!(rt.get_i32(result), 42);
        assert_eq!(rt.get_i32(counter), 0); // expensive was never called!
    }

    // -------------------------------------------------------------------------
    // Memoization: forcing twice doesn't re-evaluate.
    // inc_twice 10 = 12, and inc is called exactly twice (not four times).
    // -------------------------------------------------------------------------
    #[rstest]
    fn verify_call_by_need(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let counter = rt.i32(0);
        let inc = counted_inc(&rt, counter);

        // inc_twice = \n. inc (inc n)
        let inc_twice = rt.lam("n", &[("inc", inc)], |env, rt| {
            rt.app(env.v("inc"), rt.app(env.v("inc"), env.v("n")))
        });
        let hopefully_12 = rt.app(inc_twice, rt.i32(10));

        assert_eq!(rt.get_i32(counter), 0);
        assert_eq!(rt.get_i32(hopefully_12), 12);
        assert_eq!(rt.get_i32(counter), 2);
        assert_eq!(rt.get_i32(hopefully_12), 12);
        assert_eq!(rt.get_i32(counter), 2); // Still 2! Memoization works.
    }

    // -------------------------------------------------------------------------
    // Sharing: a thunk used twice is evaluated only once.
    // add thunk thunk = 2, but thunk's closure runs once.
    // -------------------------------------------------------------------------
    #[rstest]
    fn shared_thunk_evaluated_once(
        #[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode,
    ) {
        let rt = Runtime::new(mode);
        let counter = rt.i32(0);
        let expensive = counted_const(&rt, counter, 1);
        let thunk = rt.app(expensive, rt.i32(0));

        // Use thunk twice: add thunk thunk
        let result = rt.app(rt.app(rt.plus(), thunk), thunk);

        assert_eq!(rt.get_i32(counter), 0);
        assert_eq!(rt.get_i32(result), 2);
        assert_eq!(rt.get_i32(counter), 1); // Called once, not twice!
    }

    // -------------------------------------------------------------------------
    // Church numerals: classic lambda calculus encoding of natural numbers.
    // zero = \f.\x. x
    // succ = \n.\f.\x. f (n f x)
    // -------------------------------------------------------------------------
    #[rstest]
    fn church_numerals(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let zero = rt.lam("f", &[], |_env, rt| rt.lam("x", &[], |env, _rt| env.v("x")));

        let succ = rt.lam("n", &[], |env, rt| {
            rt.lam("f", &[("n", env.v("n"))], |env, rt| {
                rt.lam("x", &[("n", env.v("n")), ("f", env.v("f"))], |env, rt| {
                    rt.app(env.v("f"), rt.app(rt.app(env.v("n"), env.v("f")), env.v("x")))
                })
            })
        });

        // Convert church numeral to i32: apply n to inc and 0
        let inc = rt.lam("x", &[], |env, rt| rt.i32(rt.get_i32(env.v("x")) + 1));
        let to_int =
            |n: &HeapPtr| -> i32 { rt.get_i32(rt.app(rt.app(n.clone(), inc.clone()), rt.i32(0))) };

        let one = rt.app(succ.clone(), zero.clone());
        let two = rt.app(succ.clone(), one.clone());
        let three = rt.app(succ, two.clone());

        assert_eq!(to_int(&zero), 0);
        assert_eq!(to_int(&one), 1);
        assert_eq!(to_int(&two), 2);
        assert_eq!(to_int(&three), 3);
    }

    // -------------------------------------------------------------------------
    // SKI combinators: a complete basis for lambda calculus.
    // I = \x. x
    // K = \x.\y. x
    // S = \x.\y.\z. x z (y z)
    // Notably: S K K = I
    // -------------------------------------------------------------------------
    #[rstest]
    fn ski_combinators(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let i_comb = rt.lam("x", &[], |env, _rt| env.v("x"));
        let k_comb = rt.lam("x", &[], |env, rt| rt.lam("y", &[("x", env.v("x"))], |env, _rt| env.v("x")));
        let s_comb = rt.lam("x", &[], |env, rt| {
            rt.lam("y", &[("x", env.v("x"))], |env, rt| {
                rt.lam("z", &[("x", env.v("x")), ("y", env.v("y"))], |env, rt| {
                    let xz = rt.app(env.v("x"), env.v("z"));
                    let yz = rt.app(env.v("y"), env.v("z"));
                    rt.app(xz, yz)
                })
            })
        });

        // I 5 = 5
        assert_eq!(rt.get_i32(rt.app(i_comb, rt.i32(5))), 5);

        // K 5 6 = 5
        assert_eq!(
            rt.get_i32(rt.app(rt.app(k_comb.clone(), rt.i32(5)), rt.i32(6))),
            5
        );

        // S K K x = x (S K K is identity)
        let skk = rt.app(rt.app(s_comb, k_comb.clone()), k_comb);
        assert_eq!(rt.get_i32(rt.app(skk, rt.i32(42))), 42);
    }

    // -------------------------------------------------------------------------
    // Deep currying: f = \a.\b.\c. a
    // -------------------------------------------------------------------------
    #[rstest]
    fn deep_currying(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let f = rt.lam("a", &[], |env, rt| {
            rt.lam("b", &[("a", env.v("a"))], |env, rt| {
                rt.lam("c", &[("a", env.v("a"))], |env, _rt| env.v("a"))
            })
        });
        assert_eq!(
            rt.get_i32(rt.app(rt.app(rt.app(f, rt.i32(1)), rt.i32(2)), rt.i32(3))),
            1
        );
    }

    // =========================================================================
    // Tests requiring env injection (can't be in txt files)
    // =========================================================================

    use crate::{expr_parser::parse, Var};
    use std::collections::HashMap;

    #[rstest]
    fn foas_free_var(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let env = HashMap::from([(Var::new("x"), rt.i32(42))]);
        assert_eq!(rt.get_i32(rt.expr(&env, &parse("x"))), 42);
    }

    #[rstest]
    fn foas_capture_from_env(
        #[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode,
    ) {
        let rt = Runtime::new(mode);
        let env = HashMap::from([(Var::new("x"), rt.i32(100))]);
        let closure = rt.expr(&env, &parse(r"\y. x"));
        let result = rt.app(closure, rt.i32(999));
        assert_eq!(rt.get_i32(result), 100);
    }

    // =========================================================================
    // Tests requiring exact AST structure (can't be in txt files)
    // =========================================================================

    #[rstest]
    fn nbe_stuck_app(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // \f. f (\x. x) normalizes to \x0. x0 (\x1. x1)
        // This test checks the exact Expr structure, not just equality
        let result = rt.normalize(r"\f. f (\x. x)");
        let expected = crate::Expr::lam(
            Var::new("x0"),
            crate::Expr::App {
                head: Box::new(crate::Expr::Var(Var::new("x0"))),
                spine: vec![crate::Expr::lam(
                    Var::new("x1"),
                    crate::Expr::Var(Var::new("x1")),
                )],
            },
        );
        assert_eq!(result, expected);
    }
}

/// Statistics from running equality tests.
#[derive(Debug, Default)]
pub struct TestStats {
    pub bindings: usize,
    pub tests: usize,
    pub heap_size: usize,
}

/// Run equality tests from a string.
/// Format:
/// - `let NAME = expr` defines a binding (evaluated once, added to env)
/// - `expr === expr` normalizes both and checks equality
/// - Empty lines and lines starting with `//` are skipped.
pub fn run_equality_tests(content: &str, mode: ForceMode) -> Result<TestStats, String> {
    let rt = Runtime::new(mode);
    let mut env = HashMap::new();
    let mut stats = TestStats::default();

    for (line_num, line) in content.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with("//") {
            continue;
        }

        // let binding
        if let Some(rest) = line.strip_prefix("let ") {
            let Some((name, expr)) = rest.split_once('=') else {
                return Err(format!("line {}: invalid let binding: {line}", line_num + 1));
            };
            let ptr = rt.expr(&env, &expr_parser::parse(expr.trim()));
            env.insert(Var::new(name.trim()), ptr);
            stats.bindings += 1;
            continue;
        }

        // equality test (===) or inequality test (/==)
        let (left, right, expect_equal) = if let Some((l, r)) = line.split_once("===") {
            (l, r, true)
        } else if let Some((l, r)) = line.split_once("/==") {
            (l, r, false)
        } else {
            return Err(format!("line {}: expected `===`, `/==`, or `let`: {line}", line_num + 1));
        };
        let left_ptr = rt.expr(&env, &expr_parser::parse(left.trim()));
        let right_ptr = rt.expr(&env, &expr_parser::parse(right.trim()));
        let left_norm = rt.readback(left_ptr, 0);
        let right_norm = rt.readback(right_ptr, 0);
        let are_equal = left_norm == right_norm;
        if are_equal != expect_equal {
            let msg = if expect_equal { "expected equal, got different" } else { "expected different, got equal" };
            return Err(format!(
                "line {}: {msg}\n  left:  {}\n  right: {}\n  left  normalized: {left_norm:?}\n  right normalized: {right_norm:?}",
                line_num + 1, left.trim(), right.trim()
            ));
        }
        stats.tests += 1;
    }
    stats.heap_size = rt.heap_size();
    Ok(stats)
}
