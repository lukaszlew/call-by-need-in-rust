// Reference counting is our GC replacement.
use std::rc::Rc;

// We use UnsafeCell to mutate heap objects in-place when forcing lambda evaluation.
use std::cell::UnsafeCell;

// Only the call counter in one of the examples needs Cell.
#[cfg(test)]
use std::cell::Cell;

// Value enum makes it easier to add more types to the calculus.
// Right now we have just Closures and i32.
// If our calculus was typed, we could use union instead of enum, since we would always know which enum case it is.
#[derive(Clone)]
enum Value {
    I32(i32),
    Closure(Closure),
}

// These are just some accessors that make the code less messy.
impl Value {
    fn expect_i32(self: Value) -> i32 {
        if let Value::I32(i) = self {
            return i;
        }
        panic!("Not i32.")
    }

    fn expect_closure(self: Value) -> Closure {
        if let Value::Closure(c) = self {
            return c;
        }
        panic!("Not a closure.")
    }
}

// HeapObj represents unevaluated (App) or evaluated lambda calculus terms.
// When in heap memory, HeapObj will be in UnsafeCell and can be mutated in place when the terms are evaluated.
// Evaluation transmutes App into Value.
//
// HeapObj::App tag corresponds to PAP and AP Haskell heap objects tags.
// HeapObj::Value(Value::Closure) tag corresponds to FUN and THUNK Haskell heap object tags.
// I'm not sure what the i32 representation is. Maybe CONSTR?
// https://gitlab.haskell.org/ghc/ghc/-/wikis/commentary/rts/storage/heap-objects
#[derive(Clone)]
enum HeapObj {
    App(HeapPtr, HeapPtr),
    Value(Value),
}

// HeapObj is to be allocated on our "heap" and the memory is managed through reference counting.
// We do nothing about cycles.
// Thanks to the use of UnsafeCell, when any HeapPtr forces evaluation of HeapObj, all of them will see the change.
// This allows the implementation of sharing and call-by-need.
#[derive(Clone)]
pub struct HeapPtr {
    rc: Rc<UnsafeCell<HeapObj>>,
}

impl HeapPtr {
    fn new(obj: HeapObj) -> Self {
        HeapPtr {
            rc: Rc::new(UnsafeCell::new(obj)),
        }
    }

    // Another helper.
    fn expect_value(&self) -> Value {
        match self.get() {
            HeapObj::Value(v) => v.clone(),
            _ => panic!("Not a value."),
        }
    }

    // Accessing the HeapObj self is pointing to. It is safe because we return cloned Rc.
    fn get(&self) -> HeapObj {
        unsafe { (*self.rc.as_ref().get()).clone() }
    }

    // set encapsulates the unsafeness of accessing and mutating the HeapObj inside of the UnsafeCell.
    fn set(&self, obj: HeapObj) {
        unsafe {
            *self.rc.as_ref().get() = obj;
        }
    }

    // This function implements the core of lazy call-by-need evaluation.
    // If HeapObj::Value is forced, nothing happens, but when HeapObj::App(f, arg) is forced:
    // - we force f first,
    // - we assume that f is now a Closure, (i32 would be a 'type' error),
    // - we apply the closure to the (unforced) argument,
    // - we continue forcing (the result) until we get a value,
    // - and finally we overwrite App(f, arg) in-place with the result.
    // At this point the result (i32 or closure) can be inspected.
    //
    // "First", "continue" and "finally" need a stack. We keep our own instead of recursing on the Rust one,
    // so the depth of evaluation is limited by the heap. This is the stack of Haskell's STG machine.
    fn force(&self) {
        let mut stack: Vec<Frame> = Vec::new();
        // The object we are evaluating right now.
        let mut ptr: HeapPtr = self.clone();
        loop {
            match ptr.get() {
                HeapObj::App(f, arg) => {
                    // Skipping the Update frame would result in call-by-name.
                    stack.push(Frame::Update(ptr));
                    // Forcing arg before the application would effectively implement call by value,
                    // but there are better implementations of CBV.
                    stack.push(Frame::ApplyTo(arg));
                    ptr = f;
                }
                HeapObj::Value(value) => match stack.pop() {
                    Some(Frame::ApplyTo(arg)) => ptr = value.expect_closure()(arg),
                    // ptr stays on the value, which now goes to the next frame.
                    Some(Frame::Update(app)) => app.set(HeapObj::Value(value)),
                    None => return,
                },
            }
        }
    }
}

// Frame says what to do with a value once `force` gets one.
enum Frame {
    // Apply it (it has to be a closure) to this unforced argument and evaluate the result.
    ApplyTo(HeapPtr),
    // Overwrite this App in-place with it.
    Update(HeapPtr),
}

// Finally we learn that Closure is an ordinary Rust closure.
// Unfortunately it does not have a static size, which depends on the number of captured variables (HeapPtrs).
// Because of that I was forced to Rc it as well.
// This additional pointer jumping is probably "the biggest" inefficiency of this implementation.
type Closure = Rc<dyn Fn(HeapPtr) -> HeapPtr>;

// With the lambda calculus runtime implemented, we move on to examples.
// We start with some helpers to ease the Rust verboseness (compared to textual lambda calculus).

// Create HeapPtr for the given Rust closure.
pub fn lambda(f: impl Fn(HeapPtr) -> HeapPtr + 'static) -> HeapPtr {
    HeapPtr::new(HeapObj::Value(Value::Closure(Rc::new(f))))
}

// Create HeapPtr for i32. We only have boxed integers.
pub fn i32(n: i32) -> HeapPtr {
    HeapPtr::new(HeapObj::Value(Value::I32(n)))
}

// Allocate unevaluated lambda application.
pub fn ap(f: &HeapPtr, arg: &HeapPtr) -> HeapPtr {
    HeapPtr::new(HeapObj::App(f.clone(), arg.clone()))
}
// We don't have helpers for "lambda" and "var" constructs in the lambda calculus, because
// we use Rust syntax for that. This is the so-called Higher-Order Abstract Syntax (HOAS) technique.

// Since most our examples or tests should evaluate to i32, this helper reduces the verboseness as well.
pub fn force_expect_i32(ptr: &HeapPtr) -> i32 {
    ptr.force();
    ptr.expect_value().expect_i32()
}

// Simplest application.
#[test]
fn identity_applied() {
    // (\x -> x) 5
    let t = ap(&lambda(|x| x), &i32(5));
    // assert_eq!(t.get(), 5);
    assert_eq!(force_expect_i32(&t), 5);
}

// Currying on Rust HOAS.
#[test]
fn fst_and_snd() {
    // fst = \x.\y.x
    let fst = lambda(move |x| lambda(move |_y| x.clone()));
    // snd = \x.\y.y
    let snd = lambda(move |_x| lambda(move |y| y.clone()));
    // we need to clone 'x' because inner lambda might be called multiple times.

    // fst 5 6 == 5
    assert_eq!(force_expect_i32(&ap(&ap(&fst, &i32(5)), &i32(6))), 5);
    // snd 5 6 == 6
    assert_eq!(force_expect_i32(&ap(&ap(&snd, &i32(5)), &i32(6))), 6);
}

// Verify laziness and call-by-need's memoization.
#[test]
fn verify_call_by_need() {
    // The counter is ordinary Rust state, captured by the Rust closure below next to its HeapPtrs.
    let inc_call_count = Rc::new(Cell::new(0));
    let counter = inc_call_count.clone();
    // We define here what in Haskell could be a "built-in" "+1" function.
    // inc = \n.n + 1
    let inc = lambda(move |x| {
        // Tracking call count for test needs.
        counter.set(counter.get() + 1);
        // We are lazy, so there is no guarantee that x is a value. Need to force first.
        i32(force_expect_i32(&x) + 1)
    });

    // inc_twice = \n.inc (inc n)
    let inc_twice = lambda(move |n| ap(&inc, &ap(&inc, &n)));
    // hopefully_12 = inc_twice 10
    let hopefully_12 = &ap(&inc_twice, &i32(10));

    assert_eq!(inc_call_count.get(), 0);
    assert_eq!(force_expect_i32(&hopefully_12), 12);
    assert_eq!(inc_call_count.get(), 2);
    assert_eq!(force_expect_i32(&hopefully_12), 12);
    assert_eq!(inc_call_count.get(), 2);
    // Indeed nothing happens on second call of force.
}

#[test]
fn deep_currying_is_awkward() {
    // f = \a.\b.\c.a
    let f = lambda(move |a| {
        lambda(move |_b| {
            let a = a.clone(); // This is needed.
            lambda(move |_c| a.clone())
        })
    });
    // f 1 2 3 == 1
    assert_eq!(
        force_expect_i32(&ap(&ap(&ap(&f, &i32(1)), &i32(2)), &i32(3))),
        1
    );
}

// The calculus is untyped, so nothing stops us from applying a number.
#[test]
#[should_panic(expected = "Not a closure.")]
fn applying_i32_is_a_type_error() {
    // 5 6
    force_expect_i32(&ap(&i32(5), &i32(6)));
}

// `force` keeps its own stack on the heap, so a long chain of delayed applications does not overflow the Rust stack.
#[test]
fn deep_application_chain_does_not_overflow_the_stack() {
    // id = \x.x
    let id = lambda(|x| x);
    // id (id (... (id 5)))
    let mut t = i32(5);
    for _ in 0..1_000_000 {
        t = ap(&id, &t);
    }
    assert_eq!(force_expect_i32(&t), 5);
}

// So what did we learn?
// - (I believe that) Haskell's lambda-lifting (supercombinator synthesis) is very close to Rust's closure forming.
// - The code of Rust lambdas that is passed to `lambda` is compiled by Rust. This is similar to what Haskell's G-machine is doing to super-combinators.
// - `lambda` allocates a closure, not a function on the heap, it is a struct containing HeapPtrs to all referenced variables.
// - This implementation has additional indirection to closures (Rc in Closure), which Rust asks for, but probably is not needed.
// - `ap` does not call a function but allocates an unevaluated object on the heap.
//

// What could we do next?
// - Why do we need dyn/Rc in Closure? Isn't Box enough? How to avoid double pointer chasing?
//   Relevant: https://github.com/rust-lang/rust/issues/24000#issuecomment-479425396
// - How to change enum Value to union Value? Rc is in the way. ManualDrop?
// - We are verbose. How to write a macro that would synthesize the code for the lambdas, including the awkward clones.
// - `force` does not recurse, but a Rust closure that forces its argument (like `inc`) still does, so Rust stack is a part of the runtime.
// - Simplest GC is not hard in itself and would be cool to see it. But it would need explicit access to closure captured variables, wouldn't it?
// - Can we turn `force` calls into tail calls (jmp)? It would be nice to be closer to Haskell "jmp continuations".
// - Would be very cool to have some runtime benchmarks and maybe compute number of allocations.
// - Would be even cooler to use [Haskell's benchmarks](https://gitlab.haskell.org/ghc/ghc/-/wikis/building/running-tests/performance-tests)
// - How could we print the body of the lambdas? Abstract interpretation?
// - It would be very interesting to have explicit weakening and contraction (instead of Rc?) and be closer to linear lambda calculus.
