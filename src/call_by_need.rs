// Reference counting is our GC replacement.
use std::rc::Rc;

use std::cell::{Cell, RefCell};

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

// Finally we learn that Closure is an ordinary Rust closure.
// Unfortunately it does not have a static size, which depends on the number of captured variables (HeapPtrs).
// We use Rc because closures need to be cloneable (for memoization when values are shared).
// Closures take both the argument and a reference to Runtime for allocation.
type Closure = Rc<dyn Fn(HeapPtr, &Runtime) -> HeapPtr>;

// =============================================================================
// Runtime
// =============================================================================

/// Runtime for the lambda calculus with explicit heap.
pub struct Runtime {
    objects: RefCell<Vec<HeapObj>>,
    /// Debug counter for tracking function calls in tests.
    counter: Cell<i32>,
    /// Which force implementation to use.
    mode: ForceMode,
}

impl Runtime {
    #[must_use]
    pub fn new(mode: ForceMode) -> Self {
        Runtime {
            objects: RefCell::new(Vec::new()),
            counter: Cell::new(0),
            mode,
        }
    }

    /// Increment the debug counter (for testing).
    pub fn tick(&self) {
        self.counter.set(self.counter.get() + 1);
    }

    /// Get the debug counter value (for testing).
    pub fn count(&self) -> i32 {
        self.counter.get()
    }

    /// Force and extract i32.
    #[must_use]
    pub fn get_i32(&self, ptr: HeapPtr) -> i32 {
        self.force(ptr).unwrap_i32()
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
                let result = self.force(closure(arg, self));
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
                        ptr = value.unwrap_closure()(arg, self);
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

    /// Create HeapPtr for the given Rust closure.
    #[must_use]
    pub fn lambda(&self, f: impl Fn(HeapPtr, &Runtime) -> HeapPtr + 'static) -> HeapPtr {
        self.alloc(HeapObj::Closure(Rc::new(f)))
    }

    /// Create HeapPtr for i32.
    #[must_use]
    pub fn i32(&self, n: i32) -> HeapPtr {
        self.alloc(HeapObj::I32(n))
    }

    /// Allocate unevaluated lambda application.
    #[must_use]
    pub fn ap(&self, f: HeapPtr, arg: HeapPtr) -> HeapPtr {
        self.alloc(HeapObj::App(f, arg))
    }

    /// plus = \a.\b. a + b (primitive addition for i32)
    #[must_use]
    pub fn plus(&self) -> HeapPtr {
        self.lambda(|a, rt| rt.lambda(move |b, rt| rt.i32(rt.get_i32(a) + rt.get_i32(b))))
    }
}

// ============================================================================
// Didactic tests: These tests demonstrate key concepts of call-by-need.
// ============================================================================
#[cfg(test)]
mod test {
    use crate::{ForceMode, HeapPtr, Runtime};
    use rstest::rstest;

    /// Create an increment function that ticks the counter when called.
    fn counted_inc(rt: &Runtime) -> HeapPtr {
        rt.lambda(move |x, rt| {
            rt.tick();
            rt.i32(rt.get_i32(x) + 1)
        })
    }

    /// Create a thunk that returns `val` and ticks the counter when forced.
    fn counted_const(rt: &Runtime, val: i32) -> HeapPtr {
        rt.lambda(move |_, rt| {
            rt.tick();
            rt.i32(val)
        })
    }

    // -------------------------------------------------------------------------
    // Basic application: (\x -> x) 5 = 5
    // -------------------------------------------------------------------------
    #[rstest]
    fn identity_applied(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let t = rt.ap(rt.lambda(|x, _rt| x), rt.i32(5));
        assert_eq!(rt.get_i32(t), 5);
    }

    // -------------------------------------------------------------------------
    // Primitive addition: plus 3 4 = 7
    // -------------------------------------------------------------------------
    #[rstest]
    fn plus_primitive(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        assert_eq!(rt.get_i32(rt.ap(rt.ap(rt.plus(), rt.i32(3)), rt.i32(4))), 7);
    }

    // -------------------------------------------------------------------------
    // Currying: fst and snd projections.
    // fst = \x.\y.x    snd = \x.\y.y
    // -------------------------------------------------------------------------
    #[rstest]
    fn fst_and_snd(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let fst = rt.lambda(move |x, rt| rt.lambda(move |_y, _rt| x.clone()));
        let snd = rt.lambda(move |_x, rt| rt.lambda(move |y, _rt| y.clone()));

        assert_eq!(rt.get_i32(rt.ap(rt.ap(fst, rt.i32(5)), rt.i32(6))), 5);
        assert_eq!(rt.get_i32(rt.ap(rt.ap(snd, rt.i32(5)), rt.i32(6))), 6);
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
        let expensive = counted_const(&rt, 999);

        // const = \x.\y. x (ignores second argument)
        let const_fn = rt.lambda(|x, rt| rt.lambda(move |_y, _rt| x.clone()));

        let unused_thunk = rt.ap(expensive, rt.i32(0));
        let result = rt.ap(rt.ap(const_fn, rt.i32(42)), unused_thunk);

        assert_eq!(rt.get_i32(result), 42);
        assert_eq!(rt.count(), 0); // expensive was never called!
    }

    // -------------------------------------------------------------------------
    // Memoization: forcing twice doesn't re-evaluate.
    // inc_twice 10 = 12, and inc is called exactly twice (not four times).
    // -------------------------------------------------------------------------
    #[rstest]
    fn verify_call_by_need(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let inc = counted_inc(&rt);

        // inc_twice = \n. inc (inc n)
        let inc_twice = rt.lambda(move |n, rt| rt.ap(inc, rt.ap(inc, n)));
        let hopefully_12 = rt.ap(inc_twice, rt.i32(10));

        assert_eq!(rt.count(), 0);
        assert_eq!(rt.get_i32(hopefully_12), 12);
        assert_eq!(rt.count(), 2);
        assert_eq!(rt.get_i32(hopefully_12), 12);
        assert_eq!(rt.count(), 2); // Still 2! Memoization works.
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
        let expensive = counted_const(&rt, 1);
        let thunk = rt.ap(expensive, rt.i32(0));

        // Use thunk twice: add thunk thunk
        let result = rt.ap(rt.ap(rt.plus(), thunk), thunk);

        assert_eq!(rt.count(), 0);
        assert_eq!(rt.get_i32(result), 2);
        assert_eq!(rt.count(), 1); // Called once, not twice!
    }

    // -------------------------------------------------------------------------
    // Church numerals: classic lambda calculus encoding of natural numbers.
    // zero = \f.\x. x
    // succ = \n.\f.\x. f (n f x)
    // -------------------------------------------------------------------------
    #[rstest]
    fn church_numerals(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
        let rt = Runtime::new(mode);
        let zero = rt.lambda(|_f, rt| rt.lambda(|x, _rt| x));

        let succ = rt.lambda(|n, rt| {
            rt.lambda(move |f, rt| {
                let n = n.clone();
                rt.lambda(move |x, rt| {
                    let n = n.clone();
                    let f = f.clone();
                    rt.ap(f.clone(), rt.ap(rt.ap(n, f), x))
                })
            })
        });

        // Convert church numeral to i32: apply n to inc and 0
        let inc = rt.lambda(|x, rt| rt.i32(rt.get_i32(x) + 1));
        let to_int =
            |n: &HeapPtr| -> i32 { rt.get_i32(rt.ap(rt.ap(n.clone(), inc.clone()), rt.i32(0))) };

        let one = rt.ap(succ.clone(), zero.clone());
        let two = rt.ap(succ.clone(), one.clone());
        let three = rt.ap(succ, two.clone());

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
        let i_comb = rt.lambda(|x, _rt| x);
        let k_comb = rt.lambda(|x, rt| rt.lambda(move |_y, _rt| x.clone()));
        let s_comb = rt.lambda(|x, rt| {
            rt.lambda(move |y, rt| {
                let x = x.clone();
                rt.lambda(move |z, rt| {
                    let x = x.clone();
                    let y = y.clone();
                    let xz = rt.ap(x, z.clone());
                    let yz = rt.ap(y, z);
                    rt.ap(xz, yz)
                })
            })
        });

        // I 5 = 5
        assert_eq!(rt.get_i32(rt.ap(i_comb, rt.i32(5))), 5);

        // K 5 6 = 5
        assert_eq!(
            rt.get_i32(rt.ap(rt.ap(k_comb.clone(), rt.i32(5)), rt.i32(6))),
            5
        );

        // S K K x = x (S K K is identity)
        let skk = rt.ap(rt.ap(s_comb, k_comb.clone()), k_comb);
        assert_eq!(rt.get_i32(rt.ap(skk, rt.i32(42))), 42);
    }

    // -------------------------------------------------------------------------
    // Deep currying is awkward in Rust due to manual cloning.
    // f = \a.\b.\c. a
    // -------------------------------------------------------------------------
    #[rstest]
    fn deep_currying_is_awkward(
        #[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode,
    ) {
        let rt = Runtime::new(mode);
        let _f = rt.lambda(move |a, rt| {
            rt.lambda(move |_b, rt| {
                let a = a.clone();
                rt.lambda(move |_c, _rt| a.clone())
            })
        });
    }
}

// So what did we learn?
// - (I believe that) Haskell's lambda-lifting (supercombinator synthesis) is very close to Rust's closure forming.
// - The code of Rust lambdas that are passed to `lambda` are compiled by Rust. This is similar to what Haskell's G-machine is doing to super-combinators.
// - `lambda` allocates a closure, not a function on the heap, it is a struct containing HeapPtrs to all referenced variables.
// - Closures use Rc<dyn Fn> to enable cloning for memoization of shared values.
// - `ap` does not call a function but allocates unevaluated object on the heap.
