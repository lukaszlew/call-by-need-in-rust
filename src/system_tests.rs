//! System tests for call-by-need implementation correctness.
//! These tests verify internal invariants and edge cases.

use crate::common::{add, counted_const, counted_inc, run_equality_tests, TestStats};
use crate::{EnvExt, ForceMode, HeapStats, Runtime};
use rstest::rstest;

// Test that identity doesn't corrupt shared arguments.
#[rstest]
fn identity_preserves_sharing(
    #[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode,
) {
    let rt = Runtime::new(mode);
    let arg = rt.i32(42);
    let result = rt.app(rt.lam("x", &[], |env, _rt| env.v("x")), arg);
    let _ = rt.get_i32(result); // force
    assert_eq!(rt.get_i32(arg), 42);
}

// Diamond dependency: result depends on left and right, both depend on shared base.
// base should be evaluated only once.
#[rstest]
fn diamond_sharing(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    let counter = rt.i32(0);
    let inc = counted_inc(&rt, counter);

    // base = inc 10 (shared)
    let base = rt.app(inc, rt.i32(10));
    // left = inc base
    let inc2 = counted_inc(&rt, counter);
    let left = rt.app(inc2, base);
    // right = inc base
    let inc3 = counted_inc(&rt, counter);
    let right = rt.app(inc3, base);
    // result = left + right = (base+1) + (base+1) = 11+1 + 11+1 = 24
    let result = rt.app(rt.app(add(&rt), left), right);

    assert_eq!(rt.get_i32(counter), 0);
    assert_eq!(rt.get_i32(result), 24);
    // inc called 3 times: once for base, once for left, once for right
    assert_eq!(rt.get_i32(counter), 3);
}

// Nested thunks: outer thunk contains inner thunk, both memoized correctly.
// Uses separate counters to verify each function called exactly once.
#[rstest]
fn nested_thunks(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    let outer_count = rt.i32(0);
    let inner_count = rt.i32(0);

    let inner_fn = rt.lam("x", &[("inner_count", inner_count)], |env, rt| {
        rt.set_i32(env.v("inner_count"), rt.get_i32(env.v("inner_count")) + 1);
        rt.i32(rt.get_i32(env.v("x")) * 2)
    });

    let outer_fn = rt.lam(
        "x",
        &[("outer_count", outer_count), ("inner_fn", inner_fn)],
        |env, rt| {
            rt.set_i32(env.v("outer_count"), rt.get_i32(env.v("outer_count")) + 1);
            rt.app(env.v("inner_fn"), env.v("x"))
        },
    );

    let thunk = rt.app(outer_fn, rt.i32(5));

    // Force multiple times
    assert_eq!(rt.get_i32(thunk), 10);
    assert_eq!(rt.get_i32(thunk), 10);
    assert_eq!(rt.get_i32(thunk), 10);

    // Each function called exactly once
    assert_eq!(rt.get_i32(outer_count), 1);
    assert_eq!(rt.get_i32(inner_count), 1);
}

// Partial application creates shared closure.
// Uses separate counter to track outer lambda only.
#[rstest]
fn partial_application_sharing(
    #[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode,
) {
    let rt = Runtime::new(mode);
    let counter = rt.i32(0);

    // add = \x.\y. x + y (but tracks when outer lambda is called)
    let counted_add = rt.lam("x", &[("counter", counter)], |env, rt| {
        rt.set_i32(env.v("counter"), rt.get_i32(env.v("counter")) + 1);
        rt.lam("y", &[("x", env.v("x"))], |env, rt| {
            rt.i32(rt.get_i32(env.v("x")) + rt.get_i32(env.v("y")))
        })
    });

    // add5 = add 5 (partial application)
    let add5 = rt.app(counted_add, rt.i32(5));

    // Use add5 twice
    let r1 = rt.app(add5, rt.i32(10));
    let r2 = rt.app(add5, rt.i32(20));

    assert_eq!(rt.get_i32(counter), 0);
    assert_eq!(rt.get_i32(r1), 15);
    // add's outer lambda called once to produce the closure
    assert_eq!(rt.get_i32(counter), 1);
    assert_eq!(rt.get_i32(r2), 25);
    // Still 1 - add5 thunk was already forced, closure is shared
    assert_eq!(rt.get_i32(counter), 1);
}

// Multiple levels of sharing.
#[rstest]
fn deep_sharing(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    let counter = rt.i32(0);
    let inc = counted_inc(&rt, counter);
    let inc2 = counted_inc(&rt, counter);
    let inc3 = counted_inc(&rt, counter);

    // Create a chain: a -> b -> c, all shared
    let a = rt.app(inc, rt.i32(0)); // 1
    let b = rt.app(inc2, a); // 2
    let c_thunk = rt.app(inc3, b); // 3

    // (a + a) + (b + b) + (c + c)
    let add_fn = add(&rt);
    let aa = rt.app(rt.app(add_fn, a), a);
    let add_fn = add(&rt);
    let bb = rt.app(rt.app(add_fn, b), b);
    let add_fn = add(&rt);
    let cc = rt.app(rt.app(add_fn, c_thunk), c_thunk);
    let add_fn = add(&rt);
    let aabb = rt.app(rt.app(add_fn, aa), bb);
    let add_fn = add(&rt);
    let result = rt.app(rt.app(add_fn, aabb), cc);

    assert_eq!(rt.get_i32(counter), 0);
    assert_eq!(rt.get_i32(result), 2 + 4 + 6); // 12
                                               // inc called exactly 3 times (once for a, once for b, once for c)
    assert_eq!(rt.get_i32(counter), 3);
}

// Verify that forcing a value multiple times is idempotent.
#[rstest]
fn force_is_idempotent(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    let val = rt.i32(42);
    assert_eq!(rt.get_i32(val), 42);
    assert_eq!(rt.get_i32(val), 42);
    assert_eq!(rt.get_i32(val), 42);

    let thunk = rt.app(rt.lam("x", &[], |env, _rt| env.v("x")), rt.i32(99));
    assert_eq!(rt.get_i32(thunk), 99);
    assert_eq!(rt.get_i32(thunk), 99);
    assert_eq!(rt.get_i32(thunk), 99);
}

// Test closure that captures and uses multiple variables.
#[rstest]
fn closure_captures_multiple(
    #[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode,
) {
    let rt = Runtime::new(mode);
    let counter = rt.i32(0);

    let a = rt.app(counted_const(&rt, counter, 10), rt.i32(0));
    let b = rt.app(counted_const(&rt, counter, 20), rt.i32(0));
    let c_thunk = rt.app(counted_const(&rt, counter, 30), rt.i32(0));

    // Closure that captures a, b, c
    let sum_abc = rt.lam("_", &[("a", a), ("b", b), ("c", c_thunk)], |env, rt| {
        rt.i32(rt.get_i32(env.v("a")) + rt.get_i32(env.v("b")) + rt.get_i32(env.v("c")))
    });

    let result = rt.app(sum_abc, rt.i32(0));

    assert_eq!(rt.get_i32(counter), 0);
    assert_eq!(rt.get_i32(result), 60);
    assert_eq!(rt.get_i32(counter), 3);

    // Force again - should not re-evaluate
    assert_eq!(rt.get_i32(result), 60);
    assert_eq!(rt.get_i32(counter), 3);
}

/// Run nbe.txt with both force modes.
#[rstest]
fn nbe_equality_tests(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let content = include_str!("nbe.txt");
    let stats = run_equality_tests(content, mode).unwrap();
    assert_eq!(stats, TestStats {
        bindings: 51,
        tests: 148,
        heap_size: 3584,
        heap_stats: HeapStats { allocs: 3584, reads: 4686, writes: 755 },
    });
}

// Captured values not used in body should not be copied.
// \x. \y. x  applied to large App chain: chain is captured in env, not copied.
#[rstest]
fn captured_app_chain_not_copied(
    #[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode,
) {
    let rt = Runtime::new(mode);

    // Build large app chain: id (id (id ... (id 42)))
    // 100 App nodes + 100 closures + 1 i32
    let depth = 100;
    let id = rt.run(r"\z. z");
    let mut big = rt.i32(42);
    for _ in 0..depth {
        big = rt.app(id, big);
    }
    let heap_after_big = rt.heap_size();

    // Two closures: \x. \y. x  and  \a. \b. a
    // Inner body is just a Param, not the captured value
    let f = rt.run(r"\x. \y. x");
    let g = rt.run(r"\a. \b. a");

    // Apply both to big, then to dummy
    // f big 0 = big,  g big 0 = big
    let r1 = rt.app(rt.app(f, big), rt.i32(0));
    let r2 = rt.app(rt.app(g, big), rt.i32(0));

    let heap_after_apply = rt.heap_size();

    // Overhead: 14 nodes (closures + apps + params + inds)
    // NOT 2 * depth (200) which would indicate chain was copied
    assert_eq!(heap_after_apply - heap_after_big, 14);

    // Verify correctness: forcing should yield 42
    assert_eq!(rt.get_i32(r1), 42);
    assert_eq!(rt.get_i32(r2), 42);
}

// Tuple elements are lazy (not forced until pattern demands it).
// This test uses counters to verify laziness, which can't be expressed in nbe.txt.
#[rstest]
fn tuple_elements_lazy(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    let counter = rt.i32(0);
    let inc = counted_inc(&rt, counter);

    // Create tuple with thunk as second element
    let thunk = rt.app(inc, rt.i32(10));
    // Build tuple manually with thunk as second element
    let fst_val = rt.i32(1);
    let tuple_ptr = rt.alloc(crate::HeapObj::Tuple(vec![fst_val, thunk]));

    // Access first element only - thunk should not be forced
    let get_fst = rt.run(r"\(x, y). x");
    let result = rt.app(get_fst, tuple_ptr);
    assert_eq!(rt.get_i32(result), 1);
    assert_eq!(rt.get_i32(counter), 0); // thunk not forced

    // Now access second element
    let get_snd = rt.run(r"\(x, y). y");
    let result = rt.app(get_snd, tuple_ptr);
    assert_eq!(rt.get_i32(result), 11);
    assert_eq!(rt.get_i32(counter), 1); // now forced
}
