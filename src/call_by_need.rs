use std::cell::RefCell;

// HeapObj represents unevaluated (App) or evaluated (I32, Closure) lambda calculus terms.
// Evaluation transmutes App into I32 or Closure.
//
// https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/storage/heap-objects
#[derive(Clone)]
enum HeapObj {
    App(HeapPtr, HeapPtr),
    I32(i32),
    Closure(Closure),
}

impl HeapObj {
    fn unwrap_i32(self) -> i32 {
        match self {
            HeapObj::I32(n) => n,
            _ => panic!("expected i32"),
        }
    }

    fn unwrap_closure(self) -> Closure {
        match self {
            HeapObj::Closure(c) => c,
            _ => panic!("expected closure"),
        }
    }
}

// HeapPtr is an index into Runtime's heap.
#[derive(Clone, Copy)]
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
struct Closure {
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

    // Lazy call-by-need evaluation: force App(f, arg) by forcing f, applying it to arg,
    // forcing the result, and caching the result in place of the App.
    // Recursive version - simple but can overflow stack on deep thunk chains.
    fn force_recursive(&self, ptr: HeapPtr) -> HeapObj {
        let obj = self.objects.borrow()[ptr.0].clone();
        match obj {
            HeapObj::App(f, arg) => {
                let closure = self.force(f).unwrap_closure();
                let result = self.force((closure.code)(closure.env.as_ptr(), arg, self));
                self.objects.borrow_mut()[ptr.0] = result.clone();
                result
            }
            v => v,
        }
    }

    // Iterative version with explicit stack - handles arbitrary depth.
    // This is closer to STG's eval/apply loop.
    fn force_iter(&self, mut ptr: HeapPtr) -> HeapObj {
        enum Frame {
            Apply(HeapPtr),
            Update(HeapPtr),
        }
        let mut stack: Vec<Frame> = vec![];

        loop {
            let obj = self.objects.borrow()[ptr.0].clone();
            match obj {
                HeapObj::App(f, arg) => {
                    stack.push(Frame::Update(ptr));
                    stack.push(Frame::Apply(arg));
                    ptr = f;
                }
                value => match stack.pop() {
                    None => return value,
                    Some(Frame::Update(thunk)) => {
                        self.objects.borrow_mut()[thunk.0] = value.clone();
                        ptr = thunk;
                    }
                    Some(Frame::Apply(arg)) => {
                        let closure = value.unwrap_closure();
                        ptr = (closure.code)(closure.env.as_ptr(), arg, self);
                    }
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
        self.alloc(HeapObj::Closure(Closure {
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
}

// So what did we learn?
// - (I believe that) Haskell's lambda-lifting (supercombinator synthesis) is very close to Rust's closure forming.
// - The code of Rust lambdas that are passed to `lambda` are compiled by Rust. This is similar to what Haskell's G-machine is doing to super-combinators.
// - `lambda` allocates a closure, not a function on the heap, it is a struct containing HeapPtrs to all referenced variables.
// - Closures use Rc<dyn Fn> to enable cloning for memoization of shared values.
// - `ap` does not call a function but allocates unevaluated object on the heap.
