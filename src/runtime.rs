pub mod expr;
pub mod expr_parser;
pub mod heap;

#[cfg(test)]
mod common;
#[cfg(test)]
mod runtime_tests;
#[cfg(test)]
mod system_tests;

use std::collections::HashMap;

pub use expr::Expr;
pub use heap::{Heap, HeapPtr, HeapStats};

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct Var(pub String);

impl Var {
    pub fn new(name: impl Into<String>) -> Self {
        Var(name.into())
    }
}

impl From<&str> for Var {
    fn from(s: &str) -> Self {
        Var::new(s)
    }
}

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

/// Closure with Rust function body. Uses Var-based env for ergonomic API.
#[derive(Clone)]
pub struct RustClosure {
    pub param: Var,
    pub env: Env,
    pub body: fn(&Env, &Runtime) -> HeapPtr,
}

/// Closure from parsed Expr. Uses HeapPtr-based env for efficient lookup.
/// `param` points to the Param placeholder in `body`.
#[derive(Clone)]
pub struct ExprClosure {
    pub param: HeapPtr,
    pub env: HashMap<HeapPtr, HeapPtr>,
    pub body: HeapPtr,
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
    /// Parameter placeholder, resolved via HeapPtr lookup in eval_code.
    Param,
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
    heap: Heap<HeapObj>,
    /// Which force implementation to use.
    mode: ForceMode,
}

impl Runtime {
    #[must_use]
    pub fn new(mode: ForceMode) -> Self {
        Runtime {
            heap: Heap::new(),
            mode,
        }
    }

    /// Number of heap objects allocated.
    #[must_use]
    pub fn heap_size(&self) -> usize {
        self.heap.len()
    }

    /// Heap operation statistics.
    #[must_use]
    pub fn stats(&self) -> HeapStats {
        self.heap.stats()
    }

    /// Force and extract i32.
    #[must_use]
    pub fn get_i32(&self, ptr: HeapPtr) -> i32 {
        self.force(ptr).unwrap_i32()
    }

    /// Mutate heap object to i32. Breaks referential transparency.
    /// Panics if the existing value is not I32.
    pub fn set_i32(&self, ptr: HeapPtr, val: i32) {
        assert!(matches!(self.heap.get(ptr), HeapObj::I32(_)));
        self.heap.update(ptr, HeapObj::I32(val));
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
            HeapObj::RustClosure(c) => {
                let mut env = c.env;
                let None = env.insert(c.param.clone(), arg) else {
                    panic!("param {:?} shadows capture", c.param)
                };
                (c.body)(&env, self)
            }
            HeapObj::ExprClosure(c) => {
                let mut env = c.env;
                assert!(
                    env.insert(c.param, arg).is_none(),
                    "param shadows capture"
                );
                self.eval_code(c.body, &env)
            }
            HeapObj::ReadbackFreeVar { var, mut spine } => {
                spine.push(arg);
                self.heap.alloc(HeapObj::ReadbackFreeVar { var, spine })
            }
            _ => panic!("expected closure"),
        }
    }

    // Lazy call-by-need evaluation: force App(f, arg) by forcing f, applying it to arg,
    // forcing the result, and caching the result in place of the App.
    // Recursive version - simple but can overflow stack on deep thunk chains.
    fn force_recursive(&self, ptr: HeapPtr) -> HeapObj {
        let obj = self.heap.get(ptr);
        match obj {
            HeapObj::App(f, arg) => {
                let result_ptr = self.apply(self.force_recursive(f), arg);
                let result = self.force_recursive(result_ptr);
                self.heap.update(ptr, result.clone());
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
            let obj = self.heap.get(ptr);
            match obj {
                HeapObj::App(f, arg) => {
                    stack.push(UseValueTo::UpdateThunk(ptr));
                    stack.push(UseValueTo::ApplyArg(arg));
                    ptr = f
                }
                value => match stack.pop() {
                    None => return value,
                    Some(UseValueTo::UpdateThunk(thunk)) => {
                        self.heap.update(thunk, value.clone());
                        ptr = thunk
                    }
                    Some(UseValueTo::ApplyArg(arg)) => ptr = self.apply(value, arg),
                },
            }
        }
    }

    /// Allocate a heap object.
    #[must_use]
    pub fn alloc(&self, obj: HeapObj) -> HeapPtr {
        self.heap.alloc(obj)
    }

    /// Create a RustClosure with Rust code body.
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
        self.heap.alloc(HeapObj::RustClosure(RustClosure {
            param: Var::new(param),
            env: env.iter().map(|(k, v)| (Var::new(*k), *v)).collect(),
            body: f,
        }))
    }

    /// Create HeapPtr for i32.
    #[must_use]
    pub fn i32(&self, n: i32) -> HeapPtr {
        self.heap.alloc(HeapObj::I32(n))
    }

    /// Allocate unevaluated lambda application.
    #[must_use]
    pub fn app(&self, f: HeapPtr, arg: HeapPtr) -> HeapPtr {
        self.heap.alloc(HeapObj::App(f, arg))
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

    /// Evaluate pre-allocated code with HeapPtr-keyed environment.
    fn eval_code(&self, ptr: HeapPtr, env: &HashMap<HeapPtr, HeapPtr>) -> HeapPtr {
        let obj = self.heap.get(ptr);
        match obj {
            HeapObj::Param => env[&ptr],
            HeapObj::App(f, g) => {
                let f_ptr = self.eval_code(f, env);
                let g_ptr = self.eval_code(g, env);
                self.app(f_ptr, g_ptr)
            }
            HeapObj::ExprClosure(mut c) => {
                assert!(c.env.is_empty(), "closure env must be empty (from to_heap)");
                // Capture env into closure, excluding our own param
                for (&var, &val) in env {
                    if var != c.param {
                        c.env.insert(var, val);
                    }
                }
                self.heap.alloc(HeapObj::ExprClosure(c))
            }
            HeapObj::I32(_) | HeapObj::ReadbackFreeVar { .. } | HeapObj::RustClosure(_) => ptr,
        }
    }

    /// Allocate a Term with the given environment, producing a HeapPtr.
    #[must_use]
    pub fn expr(&self, env: &Env, expr: &Expr) -> HeapPtr {
        expr.to_heap(self, env)
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
                let free_var = self.heap.alloc(HeapObj::ReadbackFreeVar {
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
            HeapObj::Param => panic!("unresolved Param in readback"),
        }
    }

    /// Parse, evaluate, and normalize an expression to β-normal form.
    #[must_use]
    pub fn normalize(&self, src: &str) -> Expr {
        self.readback(self.run(src), 0)
    }
}
