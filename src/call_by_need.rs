#![allow(unused_variables)]
// Reference counting is our GC replacement.
use std::rc::Rc;

// We use RefCell to mutate heap objects in-place when forcing lambda evaluation.
use std::cell::RefCell;

// Value enum makes it easier to add more types to the calculus.
// Right now we have just Closures and i32.
// If our calculus was typed, we could use union instead of enum, since we would always know which enum case it is.
#[derive(Clone)]
enum Value {
    I32(i32),
    Closure(Closure),
}

// HeapObj represents unevaluated (App) or evaluated lambda calculus terms.
// When in heap memory, HeapObj will be in RefCell and can be mutated in place when the terms are evaluated.
// Evaluation transmutes App into Value.
//
// HeapObj::App tag corresponds to PAP and AP Haskell heap objects tags.
// HeapObj::Value(Value::Closure) tag corresponds to FUN and THUNK Haskell heap object tags.
// I'm not sure what is the i32 representation. Maybe CONSTR?
// https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/storage/heap-objects
#[derive(Clone)]
enum HeapObj {
    App(HeapPtr, HeapPtr),
    Value(Value),
}

// HeapObj is to be allocated on our "heap" and the memory is managed through reference counting.
// We do nothing about cycles.
// Thanks to the use of RefCell, when any HeapPtr forces evaluation of HeapObj, all of them will see the change.
// This allows implementation of sharing and call-by-need.
#[derive(Clone)]
pub struct HeapPtr {
    rc: Rc<RefCell<HeapObj>>,
}

impl HeapPtr {
    fn new(obj: HeapObj) -> Self {
        HeapPtr {
            rc: Rc::new(RefCell::new(obj)),
        }
    }

    /// Extract i32 if this is a forced Value::I32.
    #[must_use]
    pub fn get_i32(&self) -> Option<i32> {
        match &*self.rc.borrow() {
            HeapObj::Value(Value::I32(n)) => Some(*n),
            _ => None,
        }
    }

    fn set(&self, obj: HeapObj) {
        *self.rc.borrow_mut() = obj;
    }

    fn get(&self) -> HeapObj {
        self.rc.borrow().clone()
    }

    // This function implements the core of lazy call-by-need evaluation.
    // If HeapObj::Value is forced, nothing happens, but when HeapObj::App(f, arg) is forced:
    // - we force f first,
    // - we assume that f is now a Closure, (i32 would be a 'type' error),
    // - we apply the closure to the (unforced) argument,
    // - we continue forcing (the result) until we get a value,
    // - and finally we overwrite App(f, arg) in-place with the result.
    // At this point the result (i32 or closure) can be inspected.
    pub fn force(&self) {
        // Extract t1, t2 if this is an App, otherwise return early.
        let (t1, t2) = match &*self.rc.borrow() {
            HeapObj::App(t1, t2) => (t1.clone(), t2.clone()),
            HeapObj::Value(_) => return,
        };

        t1.force();
        // t2.force();
        // Forcing the argument would effectively implement call by value, but there are better implementations of CBV.

        // Borrow t1 to call its closure - no need to clone the closure itself.
        let new_ptr = match &*t1.rc.borrow() {
            HeapObj::Value(Value::Closure(closure)) => closure(t2),
            _ => panic!("expected closure after forcing"),
        };

        new_ptr.force();
        self.set(new_ptr.get());
        // Replacing the overwrite (last line) with force returning new_ptr.get(), would result in call-by-name.
    }
}

// Finally we learn that Closure is an ordinary Rust closure.
// Unfortunately it does not have a static size, which depends on the number of captured variables (HeapPtrs).
// We use Rc because closures need to be cloneable (for memoization when values are shared).
type Closure = Rc<dyn Fn(HeapPtr) -> HeapPtr>;

// With the lambda calculus runtime implemented, we move on to examples.
// We start with some helpers to ease on the rust verboseness (compared to textual lambda calculus).

/// Create HeapPtr for the given Rust closure.
#[must_use]
pub fn lambda(f: impl Fn(HeapPtr) -> HeapPtr + 'static) -> HeapPtr {
    HeapPtr::new(HeapObj::Value(Value::Closure(Rc::new(f))))
}

/// Create HeapPtr for i32.
#[must_use]
pub fn i32(n: i32) -> HeapPtr {
    HeapPtr::new(HeapObj::Value(Value::I32(n)))
}

/// Allocate unevaluated lambda application.
#[must_use]
pub fn ap(f: HeapPtr, arg: HeapPtr) -> HeapPtr {
    HeapPtr::new(HeapObj::App(f, arg))
}
// We don't have helpers for "lambda" and "var" constructs in the lambda calculus, because
// we use Rust syntax for that. This is the so-called Higher-Order-Abstract-Syntax (HOAS) technique.

/// Helper for tests: force and extract i32.
#[must_use]
pub fn force_expect_i32(ptr: &HeapPtr) -> i32 {
    ptr.force();
    ptr.get_i32().unwrap()
}

// ============================================================================
// Didactic tests: These tests demonstrate key concepts of call-by-need.
// ============================================================================
#[cfg(test)]
mod test {
    use crate::{ap, force_expect_i32, i32, lambda, HeapPtr};

    // -------------------------------------------------------------------------
    // Basic application: (\x -> x) 5 = 5
    // -------------------------------------------------------------------------
    #[test]
    fn identity_applied() {
        let t = ap(lambda(|x| x), i32(5));
        assert_eq!(force_expect_i32(&t), 5);
    }

    // -------------------------------------------------------------------------
    // Currying: fst and snd projections.
    // fst = \x.\y.x    snd = \x.\y.y
    // -------------------------------------------------------------------------
    #[test]
    fn fst_and_snd() {
        let fst = lambda(move |x| lambda(move |_y| x.clone()));
        let snd = lambda(move |_x| lambda(move |y| y.clone()));
        // Note: we need to clone 'x' because inner lambda might be called multiple times.

        assert_eq!(force_expect_i32(&ap(ap(fst, i32(5)), i32(6))), 5);
        assert_eq!(force_expect_i32(&ap(ap(snd, i32(5)), i32(6))), 6);
    }

    // -------------------------------------------------------------------------
    // Laziness: unused arguments are never evaluated.
    // const 42 expensive = 42, and expensive is never called.
    // -------------------------------------------------------------------------
    #[test]
    fn unused_argument_not_evaluated() {
        static mut CALL_COUNT: i32 = 0;

        let expensive = lambda(|_| {
            unsafe { CALL_COUNT += 1; }
            i32(999)
        });

        // const = \x.\y. x (ignores second argument)
        let const_fn = lambda(|x| lambda(move |_y| x.clone()));

        let unused_thunk = ap(expensive, i32(0));
        let result = ap(ap(const_fn, i32(42)), unused_thunk);

        assert_eq!(force_expect_i32(&result), 42);
        assert_eq!(unsafe { CALL_COUNT }, 0); // expensive was never called!
    }

    // -------------------------------------------------------------------------
    // Memoization: forcing twice doesn't re-evaluate.
    // inc_twice 10 = 12, and inc is called exactly twice (not four times).
    // -------------------------------------------------------------------------
    #[test]
    fn verify_call_by_need() {
        static mut CALL_COUNT: i32 = 0;
        fn get_call_count() -> i32 {
            unsafe { CALL_COUNT }
        }

        // inc = \n. n + 1
        let inc = lambda(|x| {
            unsafe { CALL_COUNT += 1; }
            i32(force_expect_i32(&x) + 1)
        });

        // inc_twice = \n. inc (inc n)
        let inc_twice = lambda(move |n| ap(inc.clone(), ap(inc.clone(), n)));
        let hopefully_12 = ap(inc_twice, i32(10));

        assert_eq!(get_call_count(), 0);
        assert_eq!(force_expect_i32(&hopefully_12), 12);
        assert_eq!(get_call_count(), 2);
        assert_eq!(force_expect_i32(&hopefully_12), 12);
        assert_eq!(get_call_count(), 2); // Still 2! Memoization works.
    }

    // -------------------------------------------------------------------------
    // Sharing: a thunk used twice is evaluated only once.
    // add thunk thunk = 2, but thunk's closure runs once.
    // -------------------------------------------------------------------------
    #[test]
    fn shared_thunk_evaluated_once() {
        static mut CALL_COUNT: i32 = 0;

        let expensive = lambda(|_| {
            unsafe { CALL_COUNT += 1; }
            i32(1)
        });

        let thunk = ap(expensive, i32(0));

        // add = \a.\b. a + b
        let add = lambda(|a| {
            lambda(move |b| {
                let a = a.clone();
                i32(force_expect_i32(&a) + force_expect_i32(&b))
            })
        });

        // Use thunk twice: add thunk thunk
        let result = ap(ap(add, thunk.clone()), thunk);

        assert_eq!(unsafe { CALL_COUNT }, 0);
        assert_eq!(force_expect_i32(&result), 2);
        assert_eq!(unsafe { CALL_COUNT }, 1); // Called once, not twice!
    }

    // -------------------------------------------------------------------------
    // Church numerals: classic lambda calculus encoding of natural numbers.
    // zero = \f.\x. x
    // succ = \n.\f.\x. f (n f x)
    // -------------------------------------------------------------------------
    #[test]
    fn church_numerals() {
        let zero = lambda(|_f| lambda(|x| x));

        let succ = lambda(|n| {
            lambda(move |f| {
                let n = n.clone();
                lambda(move |x| {
                    let n = n.clone();
                    let f = f.clone();
                    ap(f.clone(), ap(ap(n, f), x))
                })
            })
        });

        // Convert church numeral to i32: apply n to inc and 0
        let inc = lambda(|x| i32(force_expect_i32(&x) + 1));
        let to_int = |n: &HeapPtr| -> i32 {
            force_expect_i32(&ap(ap(n.clone(), inc.clone()), i32(0)))
        };

        let one = ap(succ.clone(), zero.clone()); // zero used in to_int below
        let two = ap(succ.clone(), one.clone());  // one used in to_int below
        let three = ap(succ, two.clone());        // succ's last use, two used below

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
    #[test]
    fn ski_combinators() {
        let i_comb = lambda(|x| x);
        let k_comb = lambda(|x| lambda(move |_y| x.clone()));
        let s_comb = lambda(|x| {
            lambda(move |y| {
                let x = x.clone();
                lambda(move |z| {
                    let x = x.clone();
                    let y = y.clone();
                    let xz = ap(x, z.clone());
                    let yz = ap(y, z);
                    ap(xz, yz)
                })
            })
        });

        // I 5 = 5
        assert_eq!(force_expect_i32(&ap(i_comb, i32(5))), 5);

        // K 5 6 = 5
        assert_eq!(force_expect_i32(&ap(ap(k_comb.clone(), i32(5)), i32(6))), 5);

        // S K K x = x (S K K is identity)
        let skk = ap(ap(s_comb, k_comb.clone()), k_comb); // k_comb used twice
        assert_eq!(force_expect_i32(&ap(skk, i32(42))), 42);
    }

    // -------------------------------------------------------------------------
    // Deep currying is awkward in Rust due to manual cloning.
    // f = \a.\b.\c. a
    // -------------------------------------------------------------------------
    #[test]
    fn deep_currying_is_awkward() {
        let _f = lambda(move |a| {
            lambda(move |_b| {
                let a = a.clone(); // This clone is needed for the next level.
                lambda(move |_c| a.clone())
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
//

// What could we do next?
// - Closure must be Rc<dyn Fn>, not Box. Box<dyn Fn> isn't Clone, but cloning is needed when
//   memoizing shared values (e.g., identity returns its argument, which may be shared elsewhere).
// - How to change enum Value to union Value? Rc is in a way. ManualDrop?
// - We are verbose. How to write a macro that would synthesise the code for the lambdas, including the awkward clones.
// - Runtime `force` has two recursive calls, so Rust stack is a part of the runtime.
// - Simplest GC is not hard in itself and would be cool to see it. But it would need explicit access to closure captured variables, wouldn't it?
// - Can we turn `force` calls into tail calls (jmp)? It would be nice to be closer to Haskell "jmp continuations".
// - Would be very cool to have some runtime benchmarks and maybe compute number of allocations.
// - Would be even cooler to use [Haskell's benchmarks](https://gitlab.haskell.org/ghc/ghc/-/wikis/building/running-tests/performance-tests)
// - How could be print body of the lambdas? Abstract interpretation?
// - It would be very interesting to have explicit weakening and contraction (instead of Rc?) and be closer to linear lambda calculus.
