use std::cell::RefCell;
use std::rc::Rc;

// Value enum makes it easier to add more types to the calculus.
// Right now we have just Closures and i32.
// If our calculus was typed, we could use union instead of enum, since we would always know which enum case it is.
enum Value {
    I32(i32),
    Closure(Box<dyn Fn(HeapPtr, &Runtime) -> HeapPtr>),
}

// HeapObj represents unevaluated (App) or evaluated lambda calculus terms.
// When in heap memory, HeapObj will be in RefCell and can be mutated in place when the terms are evaluated.
// Evaluation transmutes App into Ind (pointing to the result).
//
// Why Ind? After forcing App(f,x), we must cache the result. We can't copy it into App's slot
// because Box<dyn Fn> isn't Clone. So we point to it instead.
//
// HeapObj::App tag corresponds to PAP and AP Haskell heap objects tags.
// HeapObj::Value(Value::Closure) tag corresponds to FUN and THUNK Haskell heap object tags.
// I'm not sure what is the i32 representation. Maybe CONSTR?
// https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/storage/heap-objects
enum HeapObj {
    App(HeapPtr, HeapPtr),
    Ind(HeapPtr),
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
}

// =============================================================================
// Runtime
// =============================================================================

/// Runtime for the lambda calculus. Will hold the heap in the future.
pub struct Runtime {
    // Empty for now - heap will be added here
}

impl Runtime {
    #[must_use]
    pub fn new() -> Self {
        Runtime {}
    }

    // -------------------------------------------------------------------------
    // Heap access (will change when heap moves into Runtime)
    // -------------------------------------------------------------------------

    fn set(&self, ptr: &HeapPtr, obj: HeapObj) {
        *ptr.rc.borrow_mut() = obj;
    }

    fn follow_ind(&self, ptr: &HeapPtr) -> HeapPtr {
        let mut current = ptr.clone();
        loop {
            let next = match &*current.rc.borrow() {
                HeapObj::Ind(target) => Some(target.clone()),
                _ => None,
            };
            match next {
                Some(target) => current = target,
                None => return current,
            }
        }
    }

    /// Extract i32 if this is a forced Value::I32.
    #[must_use]
    pub fn get_i32(&self, ptr: &HeapPtr) -> Option<i32> {
        let target = self.follow_ind(ptr);
        let result = match &*target.rc.borrow() {
            HeapObj::Value(Value::I32(n)) => Some(*n),
            _ => None,
        };
        result
    }

    // This function implements the core of lazy call-by-need evaluation.
    // If HeapObj::Value is forced, nothing happens, but when HeapObj::App(f, arg) is forced:
    // - we force f first,
    // - we assume that f is now a Closure, (i32 would be a 'type' error),
    // - we apply the closure to the (unforced) argument,
    // - we continue forcing (the result) until we get a value,
    // - and finally we overwrite App(f, arg) in-place with Ind pointing to result.
    // At this point the result (i32 or closure) can be inspected.
    pub fn force(&self, ptr: &HeapPtr) {
        let target = self.follow_ind(ptr);

        // Extract t1, t2 if this is an App, otherwise return early.
        let (t1, t2) = match &*target.rc.borrow() {
            HeapObj::App(t1, t2) => (t1.clone(), t2.clone()),
            HeapObj::Value(_) => return,
            HeapObj::Ind(_) => unreachable!("follow_ind should have resolved this"),
        };

        self.force(&t1);

        let t1_target = self.follow_ind(&t1);
        // Borrow t1 to call its closure - no need to clone the closure itself.
        let new_ptr = match &*t1_target.rc.borrow() {
            HeapObj::Value(Value::Closure(closure)) => closure(t2, self),
            HeapObj::Value(Value::I32(_)) => panic!("expected closure, got i32"),
            _ => panic!("expected value after forcing"),
        };

        self.force(&new_ptr);
        // Short-circuit: point directly to Value, not to another Ind. Avoids Ind chains.
        self.set(&target, HeapObj::Ind(self.follow_ind(&new_ptr)));
    }

    // -------------------------------------------------------------------------
    // Allocation
    // -------------------------------------------------------------------------

    /// Create HeapPtr for the given Rust closure.
    #[must_use]
    pub fn lambda(&self, f: impl Fn(HeapPtr, &Runtime) -> HeapPtr + 'static) -> HeapPtr {
        HeapPtr::new(HeapObj::Value(Value::Closure(Box::new(f))))
    }

    /// Create HeapPtr for i32.
    #[must_use]
    pub fn i32(&self, n: i32) -> HeapPtr {
        HeapPtr::new(HeapObj::Value(Value::I32(n)))
    }

    /// Allocate unevaluated lambda application.
    #[must_use]
    pub fn ap(&self, f: HeapPtr, arg: HeapPtr) -> HeapPtr {
        HeapPtr::new(HeapObj::App(f, arg))
    }

    /// plus = \a.\b. a + b (primitive addition for i32)
    #[must_use]
    pub fn plus(&self) -> HeapPtr {
        self.lambda(|a, rt| {
            rt.lambda(move |b, rt| {
                let a = a.clone();
                rt.i32(force_expect_i32(&a, rt) + force_expect_i32(&b, rt))
            })
        })
    }
}

impl Default for Runtime {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper for tests: force and extract i32.
#[must_use]
pub fn force_expect_i32(ptr: &HeapPtr, rt: &Runtime) -> i32 {
    rt.force(ptr);
    rt.get_i32(ptr).unwrap()
}

// ============================================================================
// Didactic tests: These tests demonstrate key concepts of call-by-need.
// ============================================================================
#[cfg(test)]
mod test {
    use crate::{force_expect_i32, HeapPtr, Runtime};
    use std::cell::Cell;
    use std::rc::Rc;

    /// Shared counter for tracking function calls in tests.
    type Counter = Rc<Cell<i32>>;

    fn counter() -> Counter {
        Rc::new(Cell::new(0))
    }

    /// Create an increment function that counts how many times it's called.
    fn counted_inc(rt: &Runtime, c: &Counter) -> HeapPtr {
        let c = c.clone();
        rt.lambda(move |x, rt| {
            c.set(c.get() + 1);
            rt.i32(force_expect_i32(&x, rt) + 1)
        })
    }

    /// Create a thunk that returns `val` and increments counter when forced.
    fn counted_const(rt: &Runtime, c: &Counter, val: i32) -> HeapPtr {
        let c = c.clone();
        rt.lambda(move |_, rt| {
            c.set(c.get() + 1);
            rt.i32(val)
        })
    }

    // -------------------------------------------------------------------------
    // Basic application: (\x -> x) 5 = 5
    // -------------------------------------------------------------------------
    #[test]
    fn identity_applied() {
        let rt = Runtime::new();
        let t = rt.ap(rt.lambda(|x, _rt| x), rt.i32(5));
        assert_eq!(force_expect_i32(&t, &rt), 5);
    }

    // -------------------------------------------------------------------------
    // Primitive addition: plus 3 4 = 7
    // -------------------------------------------------------------------------
    #[test]
    fn plus_primitive() {
        let rt = Runtime::new();
        assert_eq!(force_expect_i32(&rt.ap(rt.ap(rt.plus(), rt.i32(3)), rt.i32(4)), &rt), 7);
    }

    // -------------------------------------------------------------------------
    // Currying: fst and snd projections.
    // fst = \x.\y.x    snd = \x.\y.y
    // -------------------------------------------------------------------------
    #[test]
    fn fst_and_snd() {
        let rt = Runtime::new();
        let fst = rt.lambda(move |x, rt| {
            rt.lambda(move |_y, _rt| x.clone())
        });
        let snd = rt.lambda(move |_x, rt| {
            rt.lambda(move |y, _rt| y.clone())
        });

        assert_eq!(force_expect_i32(&rt.ap(rt.ap(fst, rt.i32(5)), rt.i32(6)), &rt), 5);
        assert_eq!(force_expect_i32(&rt.ap(rt.ap(snd, rt.i32(5)), rt.i32(6)), &rt), 6);
    }

    // -------------------------------------------------------------------------
    // Laziness: unused arguments are never evaluated.
    // const 42 expensive = 42, and expensive is never called.
    // -------------------------------------------------------------------------
    #[test]
    fn unused_argument_not_evaluated() {
        let rt = Runtime::new();
        let c = counter();
        let expensive = counted_const(&rt, &c, 999);

        // const = \x.\y. x (ignores second argument)
        let const_fn = rt.lambda(|x, rt| {
            rt.lambda(move |_y, _rt| x.clone())
        });

        let unused_thunk = rt.ap(expensive, rt.i32(0));
        let result = rt.ap(rt.ap(const_fn, rt.i32(42)), unused_thunk);

        assert_eq!(force_expect_i32(&result, &rt), 42);
        assert_eq!(c.get(), 0); // expensive was never called!
    }

    // -------------------------------------------------------------------------
    // Memoization: forcing twice doesn't re-evaluate.
    // inc_twice 10 = 12, and inc is called exactly twice (not four times).
    // -------------------------------------------------------------------------
    #[test]
    fn verify_call_by_need() {
        let rt = Runtime::new();
        let c = counter();
        let inc = counted_inc(&rt, &c);

        // inc_twice = \n. inc (inc n)
        let inc_twice = rt.lambda(move |n, rt| {
            rt.ap(inc.clone(), rt.ap(inc.clone(), n))
        });
        let hopefully_12 = rt.ap(inc_twice, rt.i32(10));

        assert_eq!(c.get(), 0);
        assert_eq!(force_expect_i32(&hopefully_12, &rt), 12);
        assert_eq!(c.get(), 2);
        assert_eq!(force_expect_i32(&hopefully_12, &rt), 12);
        assert_eq!(c.get(), 2); // Still 2! Memoization works.
    }

    // -------------------------------------------------------------------------
    // Sharing: a thunk used twice is evaluated only once.
    // add thunk thunk = 2, but thunk's closure runs once.
    // -------------------------------------------------------------------------
    #[test]
    fn shared_thunk_evaluated_once() {
        let rt = Runtime::new();
        let c = counter();
        let expensive = counted_const(&rt, &c, 1);
        let thunk = rt.ap(expensive, rt.i32(0));

        // Use thunk twice: add thunk thunk
        let result = rt.ap(rt.ap(rt.plus(), thunk.clone()), thunk);

        assert_eq!(c.get(), 0);
        assert_eq!(force_expect_i32(&result, &rt), 2);
        assert_eq!(c.get(), 1); // Called once, not twice!
    }

    // -------------------------------------------------------------------------
    // Church numerals: classic lambda calculus encoding of natural numbers.
    // zero = \f.\x. x
    // succ = \n.\f.\x. f (n f x)
    // -------------------------------------------------------------------------
    #[test]
    fn church_numerals() {
        let rt = Runtime::new();
        let zero = rt.lambda(|_f, rt| {
            rt.lambda(|x, _rt| x)
        });

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
        let inc = rt.lambda(|x, rt| {
            rt.i32(force_expect_i32(&x, rt) + 1)
        });
        let to_int = |n: &HeapPtr| -> i32 {
            force_expect_i32(&rt.ap(rt.ap(n.clone(), inc.clone()), rt.i32(0)), &rt)
        };

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
    #[test]
    fn ski_combinators() {
        let rt = Runtime::new();
        let i_comb = rt.lambda(|x, _rt| x);
        let k_comb = rt.lambda(|x, rt| {
            rt.lambda(move |_y, _rt| x.clone())
        });
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
        assert_eq!(force_expect_i32(&rt.ap(i_comb, rt.i32(5)), &rt), 5);

        // K 5 6 = 5
        assert_eq!(force_expect_i32(&rt.ap(rt.ap(k_comb.clone(), rt.i32(5)), rt.i32(6)), &rt), 5);

        // S K K x = x (S K K is identity)
        let skk = rt.ap(rt.ap(s_comb, k_comb.clone()), k_comb);
        assert_eq!(force_expect_i32(&rt.ap(skk, rt.i32(42)), &rt), 42);
    }

    // -------------------------------------------------------------------------
    // Deep currying is awkward in Rust due to manual cloning.
    // f = \a.\b.\c. a
    // -------------------------------------------------------------------------
    #[test]
    fn deep_currying_is_awkward() {
        let rt = Runtime::new();
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
