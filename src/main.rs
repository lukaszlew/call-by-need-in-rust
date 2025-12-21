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
// HeapObj::Valu(Value::Closure) tag corresponds to FUN and THUNK Haskell heap object tags.
// I'm not sure sure what is the i32 representation. Maybe CONSTR?
// https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/storage/heap-objects
#[derive(Clone)]
enum HeapObj {
    App(HeapPtr, HeapPtr),
    Value(Value),
}

// HeapObj is to be allocated on our "heap" and the memory is managed through reference counting.
// We do nothing about cycles.
// Thanks to the use of RefCell, when any HeapPtr forces evaluation of HeapObj, all of them will see the change.
// This allows of implementation of sharing and call-by-need.
#[derive(Clone)]
struct HeapPtr {
    rc: Rc<RefCell<HeapObj>>,
}

impl HeapPtr {
    fn new(obj: HeapObj) -> Self {
        HeapPtr {
            rc: Rc::new(RefCell::new(obj)),
        }
    }

    // Extract i32 if this is a forced Value::I32.
    fn get_i32(&self) -> Option<i32> {
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
    fn force(&self) {
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

// Create HeapPtr for the given Rust closure.
fn lambda(f: impl Fn(HeapPtr) -> HeapPtr + 'static) -> HeapPtr {
    HeapPtr::new(HeapObj::Value(Value::Closure(Rc::new(f))))
}

// Create HeapPtr for i32. We only boxed integers.
fn i32(n: i32) -> HeapPtr {
    HeapPtr::new(HeapObj::Value(Value::I32(n)))
}

// Allocate unevaluated lambda application.
fn ap(f: &HeapPtr, arg: &HeapPtr) -> HeapPtr {
    HeapPtr::new(HeapObj::App(f.clone(), arg.clone()))
}
// We don't have helpers for for "lambda" and "var" constructs in the lambda calculus, because,
// we use Rust syntax for that. This is so-called to Higher-Order-Abstract-Syntax (HOAS) techique.

// This module has examples of usage of the machinery above.
#[cfg(test)]
mod test {
    use crate::ap;
    use crate::i32;
    use crate::lambda;
    use crate::HeapPtr;

    // Since most our examples or tests should evaluate to int, this helper reduces the verboseness as well.
    fn force_expect_i32(ptr: &HeapPtr) -> i32 {
        ptr.force();
        ptr.get_i32().unwrap()
    }

    // Simplest application.
    #[test]
    fn identity_applied() {
        // (\x -> x) 5
        let t = ap(&lambda(|x| x), &i32(5));
        // assert_eq!(t.get(), 5);
        assert_eq!(force_expect_i32(&t), 5);
    }

    // Test that identity doesn't corrupt shared arguments.
    #[test]
    fn identity_preserves_sharing() {
        let arg = i32(42);
        let result = ap(&lambda(|x| x), &arg);
        result.force();
        // arg should still be 42, not corrupted
        assert_eq!(arg.get_i32().unwrap(), 42);
    }

    // Test that a shared thunk is evaluated only once.
    #[test]
    fn shared_thunk_evaluated_once() {
        static mut CALL_COUNT: i32 = 0;

        let expensive = lambda(|_| {
            unsafe { CALL_COUNT += 1; }
            i32(1)
        });

        // Create a thunk
        let thunk = ap(&expensive, &i32(0));

        // Use the same thunk twice: add thunk thunk
        let add = lambda(|a| {
            lambda(move |b| {
                let a = a.clone();
                i32(force_expect_i32(&a) + force_expect_i32(&b))
            })
        });

        let result = ap(&ap(&add, &thunk), &thunk);

        assert_eq!(unsafe { CALL_COUNT }, 0);
        assert_eq!(force_expect_i32(&result), 2);
        assert_eq!(unsafe { CALL_COUNT }, 1);  // Should be 1, not 2!
    }

    // Currying on Rust HOAS.
    #[test]
    fn fst_and_snd() {
        // fst = \x.\y.x
        let fst = lambda(move |x| lambda(move |y| x.clone()));
        // snd = \x.\y.y
        let snd = lambda(move |x| lambda(move |y| y.clone()));
        // we need to clone 'x' because inner lambda might be called multiple times.

        // fst 5 6 == 5
        assert_eq!(force_expect_i32(&ap(&ap(&fst, &i32(5)), &i32(6))), 5);
        // snd 5 6 == 6
        assert_eq!(force_expect_i32(&ap(&ap(&snd, &i32(5)), &i32(6))), 6);
    }

    // Verify laziness and call-by-need's memoization.
    #[test]
    fn verify_call_by_need() {
        static mut CALL_COUNT: i32 = 0;
        fn get_call_count() -> i32 {
            // safety: single-threaded.
            unsafe {
                return CALL_COUNT;
            }
        }
        // We define here what in Haskell could be a "build-in" "+1" function.
        // inc = \n.n + 1
        let inc = lambda(|x| {
            // Tracking call count for test needs.
            // safety: single-threaded.
            unsafe {
                CALL_COUNT += 1;
            }
            // We are lazy, so there is no guarantee that x is a value. Need to force first.
            i32(force_expect_i32(&x) + 1)
        });

        // inc_twice = \n.inc (inc x)
        let inc_twice = lambda(move |n| ap(&inc, &ap(&inc, &n)));
        // hopefully_12 = inc_twice 10
        let hopefully_12 = &ap(&inc_twice, &i32(10));

        assert_eq!(get_call_count(), 0);
        assert_eq!(force_expect_i32(&hopefully_12), 12);
        assert_eq!(get_call_count(), 2);
        assert_eq!(force_expect_i32(&hopefully_12), 12);
        assert_eq!(get_call_count(), 2);
        // Indeed nothing happens on second call of force.
    }

    #[test]
    fn deep_curring_is_awkward() {
        // f = \a.\b.\c.a
        let f = lambda(move |a| {
            lambda(move |b| {
                let a = a.clone(); // This is needed.
                lambda(move |c| a.clone())
            })
        });
    }
}
// So what did we learn?
// - (I believe that) Haskell's lambda-lifting (supercombinator synthesis) is very close to Rust's closure forming.
// - The code of Rust lambdas that are passed to `lambda` are compiled by Rust. This is similar to what Haskell's G-machine is doing to super-combinators.
// - `lambda` allocates a closure, not a function on the heap, it is a struct containing HeapPtrs to all referenced variables.
// - Closures use Rc<dyn Fn> to enable cloning for memoization of shared values.
// - `ap` does not call a function but allocates unvaluated object on the heap.
//

fn main() {
    // Silence 'dead code warnings'.
    let t = ap(&lambda(|x| x), &i32(5));
    t.force();
    let _i = t.get_i32().unwrap();
}

// What could we do next?
// - Closure must be Rc<dyn Fn>, not Box. Box<dyn Fn> isn't Clone, but cloning is needed when
//   memoizing shared values (e.g., identity returns its argument, which may be shared elsewhere).
// - How to change enum Value to union Value? Rc is in a way. ManualDrop?
// - We are verbose. How to write a macro that would synthesise the code for the lambdas, including the awkward clones.
// - Runtime `force` have two recursive calles, so Rust stack is a part of the runtime.
// - Simplest GC is not hard in itself and would be cool to see it. But it would need an explicit acccess to closure captrued variables, wouldn't it?
// - Would Can we turn `force` calls into tail calls (jmp)? It would be nice to be closer to Haskell "jmp continuations".
// - Would be very cool to have some runtime benchmarks and maybe compute number of allocations.
// - Would be even cooler to use [Haskell's benchmarks](https://gitlab.haskell.org/ghc/ghc/-/wikis/building/running-tests/performance-tests)
// - How could be print body of the lambdas? Abstract interpretation?
// - It would be very interesting to have explicit weakening and contraction (instead of Rc?) and be closer to linear lambda calculus.
