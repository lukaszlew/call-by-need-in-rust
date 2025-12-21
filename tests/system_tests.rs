//! System tests for call-by-need implementation correctness.
//! These tests verify internal invariants and edge cases.

mod common;

use call_by_need_in_rust::{force_expect_i32, Runtime};
use common::{add, counted_const, counted_inc, counter};

// Test that identity doesn't corrupt shared arguments.
#[test]
fn identity_preserves_sharing() {
    let rt = Runtime::new();
    let arg = rt.i32(42);
    let result = rt.ap(rt.lambda(|x, _rt| x), arg.clone());
    result.force(&rt);
    assert_eq!(arg.get_i32().unwrap(), 42);
}

// Diamond dependency: result depends on left and right, both depend on shared base.
// base should be evaluated only once.
#[test]
fn diamond_sharing() {
    let rt = Runtime::new();
    let c = counter();
    let inc = counted_inc(&rt, &c);

    // base = inc 10 (shared)
    let base = rt.ap(inc.clone(), rt.i32(10));
    // left = inc base
    let left = rt.ap(inc.clone(), base.clone());
    // right = inc base
    let right = rt.ap(inc, base);
    // result = left + right = (base+1) + (base+1) = 11+1 + 11+1 = 24
    let result = rt.ap(rt.ap(add(&rt), left), right);

    assert_eq!(c.get(), 0);
    assert_eq!(force_expect_i32(&result, &rt), 24);
    // inc called 3 times: once for base, once for left, once for right
    assert_eq!(c.get(), 3);
}

// Nested thunks: outer thunk contains inner thunk, both memoized correctly.
#[test]
fn nested_thunks() {
    let rt = Runtime::new();
    let outer_count = counter();
    let inner_count = counter();

    let ic = inner_count.clone();
    let inner_fn = rt.lambda(move |x, rt| {
        ic.set(ic.get() + 1);
        rt.i32(force_expect_i32(&x, rt) * 2)
    });

    let oc = outer_count.clone();
    let outer_fn = rt.lambda(move |x, rt| {
        oc.set(oc.get() + 1);
        rt.ap(inner_fn.clone(), x)
    });

    let thunk = rt.ap(outer_fn, rt.i32(5));

    // Force multiple times
    assert_eq!(force_expect_i32(&thunk, &rt), 10);
    assert_eq!(force_expect_i32(&thunk, &rt), 10);
    assert_eq!(force_expect_i32(&thunk, &rt), 10);

    // Each function called exactly once
    assert_eq!(outer_count.get(), 1);
    assert_eq!(inner_count.get(), 1);
}

// Partial application creates shared closure.
#[test]
fn partial_application_sharing() {
    let rt = Runtime::new();
    let c = counter();

    // add = \x.\y. x + y (but tracks when outer lambda is called)
    let cc = c.clone();
    let counted_add = rt.lambda(move |x, rt| {
        cc.set(cc.get() + 1);
        rt.lambda(move |y, rt| {
            let x = x.clone();
            rt.i32(force_expect_i32(&x, rt) + force_expect_i32(&y, rt))
        })
    });

    // add5 = add 5 (partial application)
    let add5 = rt.ap(counted_add, rt.i32(5));

    // Use add5 twice
    let r1 = rt.ap(add5.clone(), rt.i32(10));
    let r2 = rt.ap(add5, rt.i32(20));

    assert_eq!(c.get(), 0);
    assert_eq!(force_expect_i32(&r1, &rt), 15);
    // add's outer lambda called once to produce the closure
    assert_eq!(c.get(), 1);
    assert_eq!(force_expect_i32(&r2, &rt), 25);
    // Still 1 - add5 thunk was already forced, closure is shared
    assert_eq!(c.get(), 1);
}

// Multiple levels of sharing.
#[test]
fn deep_sharing() {
    let rt = Runtime::new();
    let c = counter();
    let inc = counted_inc(&rt, &c);

    // Create a chain: a -> b -> c, all shared
    let a = rt.ap(inc.clone(), rt.i32(0)); // 1
    let b = rt.ap(inc.clone(), a.clone()); // 2
    let c_thunk = rt.ap(inc, b.clone()); // 3

    // (a + a) + (b + b) + (c + c)
    let add_fn = add(&rt);
    let aa = rt.ap(rt.ap(add_fn.clone(), a.clone()), a);
    let bb = rt.ap(rt.ap(add_fn.clone(), b.clone()), b);
    let cc = rt.ap(rt.ap(add_fn.clone(), c_thunk.clone()), c_thunk);
    let aabb = rt.ap(rt.ap(add_fn.clone(), aa), bb);
    let result = rt.ap(rt.ap(add_fn, aabb), cc);

    assert_eq!(c.get(), 0);
    assert_eq!(force_expect_i32(&result, &rt), 2 + 4 + 6); // 12
    // inc called exactly 3 times (once for a, once for b, once for c)
    assert_eq!(c.get(), 3);
}

// Verify that forcing a value multiple times is idempotent.
#[test]
fn force_is_idempotent() {
    let rt = Runtime::new();
    let val = rt.i32(42);
    val.force(&rt);
    val.force(&rt);
    val.force(&rt);
    assert_eq!(val.get_i32().unwrap(), 42);

    let thunk = rt.ap(rt.lambda(|x, _rt| x), rt.i32(99));
    thunk.force(&rt);
    thunk.force(&rt);
    thunk.force(&rt);
    assert_eq!(thunk.get_i32().unwrap(), 99);
}

// Test closure that captures and uses multiple variables.
#[test]
fn closure_captures_multiple() {
    let rt = Runtime::new();
    let c = counter();

    let a = rt.ap(counted_const(&rt, &c, 10), rt.i32(0));
    let b = rt.ap(counted_const(&rt, &c, 20), rt.i32(0));
    let c_thunk = rt.ap(counted_const(&rt, &c, 30), rt.i32(0));

    // Closure that captures a, b, c
    let sum_abc = rt.lambda(move |_, rt| {
        let a = a.clone();
        let b = b.clone();
        let c_thunk = c_thunk.clone();
        rt.i32(force_expect_i32(&a, rt) + force_expect_i32(&b, rt) + force_expect_i32(&c_thunk, rt))
    });

    let result = rt.ap(sum_abc, rt.i32(0));

    assert_eq!(c.get(), 0);
    assert_eq!(force_expect_i32(&result, &rt), 60);
    assert_eq!(c.get(), 3);

    // Force again - should not re-evaluate
    assert_eq!(force_expect_i32(&result, &rt), 60);
    assert_eq!(c.get(), 3);
}
