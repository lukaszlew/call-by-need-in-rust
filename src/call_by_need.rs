pub mod expr;
pub mod expr_parser;

use std::cell::RefCell;
use std::collections::HashMap;

pub use expr::{Expr, Var};

/// ExprClosure: runtime representation of a FOAS lambda.
/// Body remains as Expr, evaluated on application.
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
#[derive(Clone, Debug)]
pub struct ExprClosure {
    pub param: Var,
    pub body: Expr,
    pub env: HashMap<Var, HeapPtr>,
}

// HeapObj represents unevaluated (App) or evaluated (I32, Closure) lambda calculus terms.
// Evaluation transmutes App into I32 or Closure.
//
// https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/storage/heap-objects
#[derive(Clone)]
pub enum HeapObj {
    App(HeapPtr, HeapPtr),
    I32(i32),
    RustClosure(RustClosure),
    ExprClosure(ExprClosure),
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
#[derive(Clone, Copy, Default)]
pub enum ForceMode {
    Recursive,
    #[default]
    Iterative,
}

// Closure with explicit environment.
// - env: captured HeapPtrs, explicit instead of relying on Rust's move captures
// - code: plain fn pointer, no dynamic dispatch
#[derive(Clone)]
pub struct RustClosure {
    env: Vec<HeapPtr>,
    code: fn(*const HeapPtr, HeapPtr, &Runtime) -> HeapPtr,
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
            HeapObj::RustClosure(c) => (c.code)(c.env.as_ptr(), arg, self),
            HeapObj::ExprClosure(tc) => {
                let mut env = tc.env;
                let None = env.insert(tc.param.clone(), arg) else {
                    panic!("param {:?} shadows capture", tc.param)
                };
                self.expr(&env, &tc.body)
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

    /// Create HeapPtr for the given fn pointer with explicit environment.
    /// Use array patterns to destructure env: `rt.lambda([a, b], |&[a, b], x, rt| ...)`
    #[must_use]
    pub fn lam<const N: usize>(
        &self,
        env: [HeapPtr; N],
        f: fn(&[HeapPtr; N], HeapPtr, &Runtime) -> HeapPtr,
    ) -> HeapPtr {
        // SAFETY: We store the fn pointer as taking &[HeapPtr] (slice) instead of &[HeapPtr; N].
        // This works because:
        // 1. We pass env.as_ptr() which gives the same raw pointer for both types
        // 2. The calling convention for &[T; N] and *const T is the same (thin pointer)
        // 3. We ensure env.len() == N when calling
        let code: fn(*const HeapPtr, HeapPtr, &Runtime) -> HeapPtr =
            unsafe { std::mem::transmute(f) };
        self.alloc(HeapObj::RustClosure(RustClosure {
            env: env.to_vec(),
            code,
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
        self.lam([], |&[], a, rt| {
            rt.lam([a], |&[a], b, rt| rt.i32(rt.get_i32(a) + rt.get_i32(b)))
        })
    }

    // -------------------------------------------------------------------------
    // FOAS: Term execution
    // -------------------------------------------------------------------------

    /// Allocate a Term with the given environment, producing a HeapPtr.
    /// Signature: (env, expr) mirrors Rust closure calls where env comes first.
    #[must_use]
    pub fn expr(&self, env: &HashMap<Var, HeapPtr>, expr: &Expr) -> HeapPtr {
        match expr {
            // Lexical scoping: look up in the provided env, not any "current" env.
            Expr::Var(v) => env[v],
            Expr::Int(n) => self.i32(*n),
            Expr::App { head, spine } => {
                let mut ptr = self.expr(env, head);
                for arg in spine {
                    let arg_ptr = self.expr(env, arg);
                    ptr = self.app(ptr, arg_ptr);
                }
                ptr
            }
            // Capture current bindings into closure's env - this is where
            // lexical scoping happens. The closure remembers its definition site.
            Expr::Lam { param, body } => {
                let closure_env: HashMap<Var, HeapPtr> = body
                    .free_vars()
                    .into_iter()
                    .filter(|v| v != param)
                    .map(|v| (v.clone(), env[&v]))
                    .collect();
                self.alloc(HeapObj::ExprClosure(ExprClosure {
                    param: param.clone(),
                    body: (**body).clone(),
                    env: closure_env,
                }))
            }
            Expr::Plus => self.plus(),
        }
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
            HeapObj::RustClosure(_) | HeapObj::ExprClosure(_) => {
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
    use crate::{ForceMode, HeapPtr, Runtime};
    use rstest::rstest;

    /// Create an increment function that increments counter when called.
    fn counted_inc(rt: &Runtime, counter: HeapPtr) -> HeapPtr {
        rt.lam([counter], |&[counter], x, rt| {
            rt.set_i32(counter, rt.get_i32(counter) + 1);
            rt.i32(rt.get_i32(x) + 1)
        })
    }

    /// Create a thunk that returns `val` and increments counter when forced.
    fn counted_const(rt: &Runtime, counter: HeapPtr, val: i32) -> HeapPtr {
        let val_ptr = rt.i32(val);
        rt.lam([counter, val_ptr], |&[counter, val_ptr], _, rt| {
            rt.set_i32(counter, rt.get_i32(counter) + 1);
            rt.i32(rt.get_i32(val_ptr))
        })
    }

    // -------------------------------------------------------------------------
    // Basic application: (\x -> x) 5 = 5
    // -------------------------------------------------------------------------
    #[rstest]
    fn identity_applied(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let t = rt.app(rt.lam([], |&[], x, _rt| x), rt.i32(5));
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
        let fst = rt.lam([], |&[], x, rt| rt.lam([x], |&[x], _y, _rt| x));
        let snd = rt.lam([], |&[], _x, rt| rt.lam([], |&[], y, _rt| y));

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
        let const_fn = rt.lam([], |&[], x, rt| rt.lam([x], |&[x], _y, _rt| x));

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
        let inc_twice = rt.lam([inc], |&[inc], n, rt| rt.app(inc, rt.app(inc, n)));
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
        let zero = rt.lam([], |&[], _f, rt| rt.lam([], |&[], x, _rt| x));

        let succ = rt.lam([], |&[], n, rt| {
            rt.lam([n], |&[n], f, rt| {
                rt.lam([n, f], |&[n, f], x, rt| rt.app(f, rt.app(rt.app(n, f), x)))
            })
        });

        // Convert church numeral to i32: apply n to inc and 0
        let inc = rt.lam([], |&[], x, rt| rt.i32(rt.get_i32(x) + 1));
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
        let i_comb = rt.lam([], |&[], x, _rt| x);
        let k_comb = rt.lam([], |&[], x, rt| rt.lam([x], |&[x], _y, _rt| x));
        let s_comb = rt.lam([], |&[], x, rt| {
            rt.lam([x], |&[x], y, rt| {
                rt.lam([x, y], |&[x, y], z, rt| {
                    let xz = rt.app(x, z);
                    let yz = rt.app(y, z);
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
    // With explicit env, no more awkward cloning!
    // -------------------------------------------------------------------------
    #[rstest]
    fn deep_currying(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let f = rt.lam([], |&[], a, rt| {
            rt.lam([a], |&[a], _b, rt| rt.lam([a], |&[a], _c, _rt| a))
        });
        assert_eq!(
            rt.get_i32(rt.app(rt.app(rt.app(f, rt.i32(1)), rt.i32(2)), rt.i32(3))),
            1
        );
    }

    // =========================================================================
    // FOAS tests: parsed lambda calculus expressions
    // =========================================================================

    use crate::{expr_parser::parse, Var};
    use std::collections::HashMap;

    #[rstest]
    fn foas_identity(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        assert_eq!(rt.get_i32(rt.run(r"(\x. x) 5")), 5);
    }

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

    #[rstest]
    fn foas_plus(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        assert_eq!(rt.get_i32(rt.run("+ 3 4")), 7);
    }

    #[rstest]
    fn foas_fst_snd(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        assert_eq!(rt.get_i32(rt.run(r"(\x. \y. x) 5 6")), 5);
        assert_eq!(rt.get_i32(rt.run(r"(\x. \y. y) 5 6")), 6);
    }

    #[rstest]
    fn foas_laziness(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // const 42 (+ 1 2) - second arg never evaluated
        assert_eq!(rt.get_i32(rt.run(r"(\x. \y. x) 42 (+ 1 2)")), 42);
    }

    #[rstest]
    fn foas_ski(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // S K K 42 = 42
        let s = r"\x. \y. \z. x z (y z)";
        let k = r"\x. \y. x";
        assert_eq!(rt.get_i32(rt.run(&format!("({s}) ({k}) ({k}) 42"))), 42);
    }

    // =========================================================================
    // NbE tests: normalization by evaluation
    // =========================================================================

    #[rstest]
    fn nbe_identity(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // Different variable names, same identity function
        assert_eq!(rt.normalize(r"\x. x"), rt.normalize(r"\y. y"));
    }

    #[rstest]
    fn nbe_int(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        assert_eq!(rt.normalize("42"), crate::Expr::Int(42));
    }

    #[rstest]
    fn nbe_plus(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        assert_eq!(rt.normalize("+ 1 2"), crate::Expr::Int(3));
    }

    #[rstest]
    fn nbe_church_2(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // Church 2 applied to (+1) and 0 gives 2
        let church_2 = r"\f. \x. f (f x)";
        assert_eq!(
            rt.normalize(&format!("({church_2}) (+ 1) 0")),
            crate::Expr::Int(2)
        );
    }

    #[rstest]
    fn nbe_skk_is_i(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // S K K = I (both normalize to \x. x)
        let s = r"\x. \y. \z. x z (y z)";
        let k = r"\x. \y. x";
        let i = r"\x. x";
        assert_eq!(rt.normalize(&format!("({s}) ({k}) ({k})")), rt.normalize(i));
    }

    #[rstest]
    fn nbe_stuck_app(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // \f. f (\x. x) normalizes to \x0. x0 (\x1. x1)
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

    // Church numeral definitions for tests
    const ZERO: &str = r"\f. \x. x";
    const SUCC: &str = r"\n. \f. \x. f (n f x)";
    const PLUS: &str = r"\m. \n. \f. \x. m f (n f x)";
    const MULT: &str = r"\m. \n. \f. m (n f)";
    const TRUE: &str = r"\x. \y. x";
    const FALSE: &str = r"\x. \y. y";

    fn church(n: usize) -> String {
        let mut s = ZERO.to_string();
        for _ in 0..n {
            s = format!("({SUCC}) ({s})");
        }
        s
    }

    #[rstest]
    fn nbe_church_add(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // 2 + 3 = 5
        let two = church(2);
        let three = church(3);
        let five = church(5);
        assert_eq!(
            rt.normalize(&format!("({PLUS}) ({two}) ({three})")),
            rt.normalize(&five)
        );
    }

    #[rstest]
    fn nbe_church_mult(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // 2 * 3 = 6
        let two = church(2);
        let three = church(3);
        let six = church(6);
        assert_eq!(
            rt.normalize(&format!("({MULT}) ({two}) ({three})")),
            rt.normalize(&six)
        );
    }

    #[rstest]
    fn nbe_compose(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // compose f g x = f (g x)
        // compose id id = id
        let compose = r"\f. \g. \x. f (g x)";
        let id = r"\x. x";
        assert_eq!(
            rt.normalize(&format!("({compose}) ({id}) ({id})")),
            rt.normalize(id)
        );
    }

    #[rstest]
    fn nbe_flip(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // flip f x y = f y x
        // flip (flip f) = f
        let flip = r"\f. \x. \y. f y x";
        // flip (flip K) should equal K
        let k = r"\x. \y. x";
        assert_eq!(
            rt.normalize(&format!("({flip}) (({flip}) ({k}))")),
            rt.normalize(k)
        );
    }

    #[rstest]
    fn nbe_church_booleans(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // not true = false, not false = true
        let not = r"\b. \x. \y. b y x";
        assert_eq!(
            rt.normalize(&format!("({not}) ({TRUE})")),
            rt.normalize(FALSE)
        );
        assert_eq!(
            rt.normalize(&format!("({not}) ({FALSE})")),
            rt.normalize(TRUE)
        );
    }

    #[rstest]
    fn nbe_and_or(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let and = r"\a. \b. a b a";
        let or = r"\a. \b. a a b";

        // true && false = false
        assert_eq!(
            rt.normalize(&format!("({and}) ({TRUE}) ({FALSE})")),
            rt.normalize(FALSE)
        );
        // true && true = true
        assert_eq!(
            rt.normalize(&format!("({and}) ({TRUE}) ({TRUE})")),
            rt.normalize(TRUE)
        );
        // false || true = true
        assert_eq!(
            rt.normalize(&format!("({or}) ({FALSE}) ({TRUE})")),
            rt.normalize(TRUE)
        );
        // false || false = false
        assert_eq!(
            rt.normalize(&format!("({or}) ({FALSE}) ({FALSE})")),
            rt.normalize(FALSE)
        );
    }

    #[rstest]
    fn nbe_pair(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let pair = r"\a. \b. \f. f a b";
        let fst = r"\p. p (\a. \b. a)";
        let snd = r"\p. p (\a. \b. b)";
        let id = r"\x. x";
        let k = r"\x. \y. x";

        // fst (pair id k) = id
        assert_eq!(
            rt.normalize(&format!("({fst}) (({pair}) ({id}) ({k}))")),
            rt.normalize(id)
        );
        // snd (pair id k) = k
        assert_eq!(
            rt.normalize(&format!("({snd}) (({pair}) ({id}) ({k}))")),
            rt.normalize(k)
        );
    }

    #[rstest]
    fn nbe_y_fragment(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // Not full Y combinator (would diverge), but test its building blocks
        // (\x. x x) applied to K gives K K which normalizes
        let omega_half = r"\x. x x";
        let k = r"\x. \y. x";
        // (\x. x x) K = K K = \y. K
        assert_eq!(
            rt.normalize(&format!("({omega_half}) ({k})")),
            rt.normalize(&format!("({k}) ({k})"))
        );
    }

    #[rstest]
    fn nbe_s_combinator_partial(
        #[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode,
    ) {
        let rt = Runtime::new(mode);
        // S K = \y.\z. K z (y z) = \y.\z. z
        let s = r"\x. \y. \z. x z (y z)";
        let k = r"\x. \y. x";
        // S K anything = I
        let i = r"\x. x";
        assert_eq!(rt.normalize(&format!("({s}) ({k}) ({k})")), rt.normalize(i));
        // Also S K S = I
        assert_eq!(rt.normalize(&format!("({s}) ({k}) ({s})")), rt.normalize(i));
    }

    #[rstest]
    fn nbe_b_combinator(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // B = S (K S) K (composition)
        // B f g x = f (g x)
        let s = r"\x. \y. \z. x z (y z)";
        let k = r"\x. \y. x";
        let b_via_sk = format!("({s}) (({k}) ({s})) ({k})");
        let b_direct = r"\f. \g. \x. f (g x)";
        assert_eq!(rt.normalize(&b_via_sk), rt.normalize(b_direct));
    }

    #[rstest]
    fn nbe_c_combinator(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // C = flip = \f.\x.\y. f y x
        // C (C f) = f
        let c = r"\f. \x. \y. f y x";
        let f = r"\a. \b. a"; // K
        assert_eq!(
            rt.normalize(&format!("({c}) (({c}) ({f}))")),
            rt.normalize(f)
        );
    }

    #[rstest]
    fn nbe_church_exp(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // exp m n = n m (Church exponentiation)
        // 2^3 = 8
        let two = church(2);
        let three = church(3);
        let eight = church(8);
        // exp = \m.\n. n m
        assert_eq!(
            rt.normalize(&format!("({three}) ({two})")),
            rt.normalize(&eight)
        );
    }

    #[rstest]
    fn nbe_nested_stuck(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        // \f.\g. f (g f) (\x. g x)
        // Tests deeply nested stuck applications
        let expr1 = r"\f. \g. f (g f) (\x. g x)";
        let expr2 = r"\a. \b. a (b a) (\y. b y)";
        assert_eq!(rt.normalize(expr1), rt.normalize(expr2));
    }
}
