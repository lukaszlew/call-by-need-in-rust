//! System tests for call-by-need implementation correctness.
//! These tests verify internal invariants and edge cases.

mod common;

use call_by_need_in_rust::{ForceMode, Runtime};
use common::{add, counted_const, counted_inc};
use rstest::rstest;

// Test that identity doesn't corrupt shared arguments.
#[rstest]
fn identity_preserves_sharing(
    #[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode,
) {
    let rt = Runtime::new(mode);
    let arg = rt.i32(42);
    let result = rt.ap(rt.lambda([], |&[], x, _rt| x), arg);
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
    let base = rt.ap(inc, rt.i32(10));
    // left = inc base
    let inc2 = counted_inc(&rt, counter);
    let left = rt.ap(inc2, base);
    // right = inc base
    let inc3 = counted_inc(&rt, counter);
    let right = rt.ap(inc3, base);
    // result = left + right = (base+1) + (base+1) = 11+1 + 11+1 = 24
    let result = rt.ap(rt.ap(add(&rt), left), right);

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

    let inner_fn = rt.lambda([inner_count], |&[inner_count], x, rt| {
        rt.set_i32(inner_count, rt.get_i32(inner_count) + 1);
        rt.i32(rt.get_i32(x) * 2)
    });

    let outer_fn = rt.lambda(
        [outer_count, inner_fn],
        |&[outer_count, inner_fn], x, rt| {
            rt.set_i32(outer_count, rt.get_i32(outer_count) + 1);
            rt.ap(inner_fn, x)
        },
    );

    let thunk = rt.ap(outer_fn, rt.i32(5));

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
    let counted_add = rt.lambda([counter], |&[counter], x, rt| {
        rt.set_i32(counter, rt.get_i32(counter) + 1);
        rt.lambda([x], |&[x], y, rt| rt.i32(rt.get_i32(x) + rt.get_i32(y)))
    });

    // add5 = add 5 (partial application)
    let add5 = rt.ap(counted_add, rt.i32(5));

    // Use add5 twice
    let r1 = rt.ap(add5, rt.i32(10));
    let r2 = rt.ap(add5, rt.i32(20));

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
    let a = rt.ap(inc, rt.i32(0)); // 1
    let b = rt.ap(inc2, a); // 2
    let c_thunk = rt.ap(inc3, b); // 3

    // (a + a) + (b + b) + (c + c)
    let add_fn = add(&rt);
    let aa = rt.ap(rt.ap(add_fn, a), a);
    let add_fn = add(&rt);
    let bb = rt.ap(rt.ap(add_fn, b), b);
    let add_fn = add(&rt);
    let cc = rt.ap(rt.ap(add_fn, c_thunk), c_thunk);
    let add_fn = add(&rt);
    let aabb = rt.ap(rt.ap(add_fn, aa), bb);
    let add_fn = add(&rt);
    let result = rt.ap(rt.ap(add_fn, aabb), cc);

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

    let thunk = rt.ap(rt.lambda([], |&[], x, _rt| x), rt.i32(99));
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

    let a = rt.ap(counted_const(&rt, counter, 10), rt.i32(0));
    let b = rt.ap(counted_const(&rt, counter, 20), rt.i32(0));
    let c_thunk = rt.ap(counted_const(&rt, counter, 30), rt.i32(0));

    // Closure that captures a, b, c
    let sum_abc = rt.lambda([a, b, c_thunk], |&[a, b, c], _, rt| {
        rt.i32(rt.get_i32(a) + rt.get_i32(b) + rt.get_i32(c))
    });

    let result = rt.ap(sum_abc, rt.i32(0));

    assert_eq!(rt.get_i32(counter), 0);
    assert_eq!(rt.get_i32(result), 60);
    assert_eq!(rt.get_i32(counter), 3);

    // Force again - should not re-evaluate
    assert_eq!(rt.get_i32(result), 60);
    assert_eq!(rt.get_i32(counter), 3);
}
