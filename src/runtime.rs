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

pub use expr::{Expr, Pat};
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

/// Pattern on the heap. Maps to Param placeholders in the closure body.
#[derive(Clone, Debug)]
pub enum HeapPat {
    /// Variable pattern - points to Param placeholder.
    Var(HeapPtr),
    /// Tuple pattern.
    Tuple(Vec<HeapPat>),
}

impl HeapPat {
    /// Collect all Param HeapPtrs in this pattern.
    pub fn params(&self) -> Vec<HeapPtr> {
        match self {
            HeapPat::Var(ptr) => vec![*ptr],
            HeapPat::Tuple(pats) => pats.iter().flat_map(HeapPat::params).collect(),
        }
    }
}

// =============================================================================
// Tagged Heap Objects (GHC-style uniform representation)
// =============================================================================

/// Object tag - discriminates heap object types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tag {
    /// App(f, arg) - unevaluated function application
    App,
    /// Int value (field 0 is Int)
    Int,
    /// Tuple of n elements (all fields are Ptr)
    Tuple,
    /// Closure (has ClosureData)
    Closure,
    /// Parameter placeholder
    Param,
    /// Neutral term for readback: head applied to spine
    Neutral,
}

/// Field in a heap object - either pointer or immediate.
#[derive(Clone, Copy, Debug)]
pub enum Field {
    Ptr(HeapPtr),
    Int(i32),
}

impl Field {
    fn unwrap_ptr(self) -> HeapPtr {
        match self {
            Field::Ptr(p) => p,
            Field::Int(_) => panic!("expected Ptr, got Int"),
        }
    }

    fn unwrap_int(self) -> i32 {
        match self {
            Field::Int(n) => n,
            Field::Ptr(_) => panic!("expected Int, got Ptr"),
        }
    }
}

/// Closure-specific data (only present when tag == Closure).
#[derive(Clone)]
pub enum ClosureData {
    Rust {
        param: Var,
        env: HashMap<Var, HeapPtr>,
        body: fn(&Env, &Runtime) -> HeapPtr,
    },
    Expr {
        param: HeapPat,
        env: HashMap<HeapPtr, HeapPtr>,
        body: HeapPtr,
    },
}

/// Heap object with uniform tagged representation.
/// https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/storage/heap-objects
#[derive(Clone)]
pub struct HeapObj {
    pub tag: Tag,
    pub fields: Vec<Field>,
    /// Closure-specific data (only for Tag::Closure)
    pub closure: Option<ClosureData>,
    /// Variable name for Neutral (readback free var)
    pub var: Option<Var>,
}

impl HeapObj {
    // Constructors
    fn app(f: HeapPtr, arg: HeapPtr) -> Self {
        HeapObj { tag: Tag::App, fields: vec![Field::Ptr(f), Field::Ptr(arg)], closure: None, var: None }
    }

    fn int(n: i32) -> Self {
        HeapObj { tag: Tag::Int, fields: vec![Field::Int(n)], closure: None, var: None }
    }

    fn tuple(elems: Vec<HeapPtr>) -> Self {
        HeapObj { tag: Tag::Tuple, fields: elems.into_iter().map(Field::Ptr).collect(), closure: None, var: None }
    }

    fn rust_closure(param: Var, env: HashMap<Var, HeapPtr>, body: fn(&Env, &Runtime) -> HeapPtr) -> Self {
        HeapObj {
            tag: Tag::Closure,
            fields: vec![],
            closure: Some(ClosureData::Rust { param, env, body }),
            var: None,
        }
    }

    fn expr_closure(param: HeapPat, env: HashMap<HeapPtr, HeapPtr>, body: HeapPtr) -> Self {
        HeapObj {
            tag: Tag::Closure,
            fields: vec![],
            closure: Some(ClosureData::Expr { param, env, body }),
            var: None,
        }
    }

    fn param() -> Self {
        HeapObj { tag: Tag::Param, fields: vec![], closure: None, var: None }
    }

    fn neutral(var: Var, spine: Vec<HeapPtr>) -> Self {
        HeapObj {
            tag: Tag::Neutral,
            fields: spine.into_iter().map(Field::Ptr).collect(),
            closure: None,
            var: Some(var),
        }
    }

    // Accessors
    fn ptr(&self, i: usize) -> HeapPtr {
        self.fields[i].unwrap_ptr()
    }

    fn ptrs(&self) -> Vec<HeapPtr> {
        self.fields.iter().map(|f| f.unwrap_ptr()).collect()
    }

    fn unwrap_i32(&self) -> i32 {
        assert!(self.tag == Tag::Int, "expected Int, got {:?}", self.tag);
        self.fields[0].unwrap_int()
    }

    fn unwrap_tuple(&self) -> Vec<HeapPtr> {
        assert!(self.tag == Tag::Tuple, "expected Tuple, got {:?}", self.tag);
        self.ptrs()
    }

    fn fmt_short(&self) -> String {
        match self.tag {
            Tag::App => format!("App({:?}, {:?})", self.ptr(0), self.ptr(1)),
            Tag::Int => format!("Int({})", self.unwrap_i32()),
            Tag::Tuple => format!("Tuple({:?})", self.ptrs()),
            Tag::Closure => match &self.closure {
                Some(ClosureData::Rust { param, .. }) => format!("RustClosure({})", param.0),
                Some(ClosureData::Expr { param, body, .. }) => format!("ExprClosure({:?}, body={:?})", param, body),
                None => "Closure(?)".to_string(),
            },
            Tag::Param => "Param".to_string(),
            Tag::Neutral => format!("Neutral({}, {:?})", self.var.as_ref().unwrap().0, self.ptrs()),
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

    /// Dump all heap objects for debugging.
    pub fn dump_heap(&self) {
        for (ptr, obj) in self.heap.iter() {
            println!("{:?}: {}", ptr, obj.fmt_short());
        }
    }

    /// Force and extract i32.
    #[must_use]
    pub fn get_i32(&self, ptr: HeapPtr) -> i32 {
        self.force(ptr).unwrap_i32()
    }

    /// Mutate heap object to i32. Breaks referential transparency.
    /// Panics if the existing value is not Int.
    pub fn set_i32(&self, ptr: HeapPtr, val: i32) {
        assert!(self.heap.get(ptr).tag == Tag::Int);
        self.heap.update(ptr, HeapObj::int(val));
    }

    fn force(&self, ptr: HeapPtr) -> HeapObj {
        match self.mode {
            ForceMode::Recursive => self.force_recursive(ptr),
            ForceMode::Iterative => self.force_iter(ptr),
        }
    }

    /// Apply a function to an argument. Handles closures and neutral terms.
    fn apply(&self, closure: HeapObj, arg: HeapPtr) -> HeapPtr {
        match closure.tag {
            Tag::Closure => match closure.closure.unwrap() {
                ClosureData::Rust { param, mut env, body } => {
                    let None = env.insert(param.clone(), arg) else {
                        panic!("param {:?} shadows capture", param)
                    };
                    (body)(&env, self)
                }
                ClosureData::Expr { param, mut env, body } => {
                    self.match_pattern(&param, arg, &mut env);
                    self.eval_code(body, &env)
                }
            },
            Tag::Neutral => {
                let var = closure.var.clone().unwrap();
                let mut spine = closure.ptrs();
                spine.push(arg);
                self.heap.alloc(HeapObj::neutral(var, spine))
            }
            _ => panic!("expected closure, got {:?}", closure.tag),
        }
    }

    /// Match a pattern against an argument, adding bindings to env.
    /// Forces tuple structure lazily (only when pattern requires it).
    fn match_pattern(
        &self,
        pat: &HeapPat,
        arg: HeapPtr,
        env: &mut HashMap<HeapPtr, HeapPtr>,
    ) {
        match pat {
            HeapPat::Var(param_ptr) => {
                assert!(env.insert(*param_ptr, arg).is_none(), "param shadows capture");
            }
            HeapPat::Tuple(pats) => {
                // Force arg to get tuple structure
                let tuple = self.force(arg).unwrap_tuple();
                assert_eq!(pats.len(), tuple.len(), "tuple pattern arity mismatch");
                for (p, a) in pats.iter().zip(tuple) {
                    self.match_pattern(p, a, env);
                }
            }
        }
    }

    // Lazy call-by-need evaluation: force App(f, arg) by forcing f, applying it to arg,
    // forcing the result, and caching the result in place of the App.
    // Recursive version - simple but can overflow stack on deep thunk chains.
    fn force_recursive(&self, ptr: HeapPtr) -> HeapObj {
        let obj = self.heap.get(ptr);
        match obj.tag {
            Tag::App => {
                let f = obj.ptr(0);
                let arg = obj.ptr(1);
                let result_ptr = self.apply(self.force_recursive(f), arg);
                let result = self.force_recursive(result_ptr);
                self.heap.update(ptr, result.clone());
                result
            }
            _ => obj,
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
        let mut cached: Option<HeapObj> = None;

        loop {
            let obj = cached.take().unwrap_or_else(|| self.heap.get(ptr));
            match obj.tag {
                Tag::App => {
                    let f = obj.ptr(0);
                    let arg = obj.ptr(1);
                    stack.push(UseValueTo::UpdateThunk(ptr));
                    stack.push(UseValueTo::ApplyArg(arg));
                    ptr = f;
                }
                _ => match stack.pop() {
                    None => return obj,
                    Some(UseValueTo::UpdateThunk(thunk)) => {
                        self.heap.update(thunk, obj.clone());
                        cached = Some(obj);
                    }
                    Some(UseValueTo::ApplyArg(arg)) => {
                        ptr = self.apply(obj, arg);
                    }
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
        self.heap.alloc(HeapObj::rust_closure(
            Var::new(param),
            env.iter().map(|(k, v)| (Var::new(*k), *v)).collect(),
            f,
        ))
    }

    /// Create HeapPtr for i32.
    #[must_use]
    pub fn i32(&self, n: i32) -> HeapPtr {
        self.heap.alloc(HeapObj::int(n))
    }

    /// Allocate unevaluated lambda application.
    #[must_use]
    pub fn app(&self, f: HeapPtr, arg: HeapPtr) -> HeapPtr {
        self.heap.alloc(HeapObj::app(f, arg))
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
        match obj.tag {
            Tag::Param => env[&ptr],
            Tag::App => {
                let f = obj.ptr(0);
                let g = obj.ptr(1);
                let f_ptr = self.eval_code(f, env);
                let g_ptr = self.eval_code(g, env);
                self.app(f_ptr, g_ptr)
            }
            Tag::Tuple => {
                let elems = obj.ptrs();
                let copied: Vec<_> = elems.iter().map(|e| self.eval_code(*e, env)).collect();
                self.heap.alloc(HeapObj::tuple(copied))
            }
            Tag::Closure => {
                match obj.closure.unwrap() {
                    ClosureData::Rust { .. } => ptr, // RustClosure passes through
                    ClosureData::Expr { param, env: cenv, body } => {
                        assert!(cenv.is_empty(), "closure env must be empty (from to_heap)");
                        // Capture env into closure, excluding our own params
                        let params = param.params();
                        let mut new_env = HashMap::new();
                        for (&var, &val) in env {
                            if !params.contains(&var) {
                                new_env.insert(var, val);
                            }
                        }
                        self.heap.alloc(HeapObj::expr_closure(param, new_env, body))
                    }
                }
            }
            Tag::Int | Tag::Neutral => ptr,
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
        match obj.tag {
            Tag::Closure => {
                match obj.closure.as_ref().unwrap() {
                    ClosureData::Rust { .. } => {
                        let param = Var::new(format!("x{depth}"));
                        let free_var = self.heap.alloc(HeapObj::neutral(param.clone(), vec![]));
                        let body = self.apply(obj, free_var);
                        Expr::lam(param, self.readback(body, depth + 1))
                    }
                    ClosureData::Expr { param, .. } => {
                        // Create free variable(s) matching the pattern structure
                        let (pat, arg, new_depth) = self.readback_pattern(param, depth);
                        let body = self.apply(obj, arg);
                        Expr::lam_pat(pat, self.readback(body, new_depth))
                    }
                }
            }
            Tag::Neutral => {
                let var = obj.var.clone().unwrap();
                let spine = obj.ptrs();
                Expr::app(
                    Expr::Var(var),
                    spine.into_iter().map(|arg| self.readback(arg, depth)).collect(),
                )
            }
            Tag::Tuple => {
                let elems = obj.ptrs();
                Expr::Tuple(elems.into_iter().map(|e| self.readback(e, depth)).collect())
            }
            Tag::Int => Expr::Int(obj.unwrap_i32()),
            Tag::App => panic!("unevaluated App in readback"),
            Tag::Param => panic!("unresolved Param in readback"),
        }
    }

    /// Create a pattern and matching free argument for readback.
    /// Returns (pattern for Expr, heap argument to apply, new depth).
    fn readback_pattern(&self, pat: &HeapPat, depth: usize) -> (Pat, HeapPtr, usize) {
        match pat {
            HeapPat::Var(_) => {
                let var = Var::new(format!("x{depth}"));
                let free_var = self.heap.alloc(HeapObj::neutral(var.clone(), vec![]));
                (Pat::Var(var), free_var, depth + 1)
            }
            HeapPat::Tuple(pats) => {
                let mut new_depth = depth;
                let mut expr_pats = Vec::with_capacity(pats.len());
                let mut heap_args = Vec::with_capacity(pats.len());
                for p in pats {
                    let (expr_pat, heap_arg, d) = self.readback_pattern(p, new_depth);
                    expr_pats.push(expr_pat);
                    heap_args.push(heap_arg);
                    new_depth = d;
                }
                let tuple = self.heap.alloc(HeapObj::tuple(heap_args));
                (Pat::Tuple(expr_pats), tuple, new_depth)
            }
        }
    }

    /// Parse, evaluate, and normalize an expression to β-normal form.
    #[must_use]
    pub fn normalize(&self, src: &str) -> Expr {
        self.readback(self.run(src), 0)
    }
}
