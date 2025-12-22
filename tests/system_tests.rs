//! System tests for call-by-need implementation correctness.
//! These tests verify internal invariants and edge cases.

mod common;

use call_by_need_in_rust::{force_expect_i32, Runtime};
use common::{add, counted_const, counted_inc};
use std::cell::Cell;
use std::rc::Rc;

// Test that identity doesn't corrupt shared arguments.
#[test]
fn identity_preserves_sharing() {
    let rt = Runtime::new();
    let arg = rt.i32(42);
    let result = rt.ap(rt.lambda(|x, _rt| x), arg);
    let _ = rt.get_i32(result); // force
    assert_eq!(rt.get_i32(arg).unwrap(), 42);
}

// Diamond dependency: result depends on left and right, both depend on shared base.
// base should be evaluated only once.
#[test]
fn diamond_sharing() {
    let rt = Runtime::new();
    let inc = counted_inc(&rt);

    // base = inc 10 (shared)
    let base = rt.ap(inc, rt.i32(10));
    // left = inc base
    let inc2 = counted_inc(&rt);
    let left = rt.ap(inc2, base);
    // right = inc base
    let inc3 = counted_inc(&rt);
    let right = rt.ap(inc3, base);
    // result = left + right = (base+1) + (base+1) = 11+1 + 11+1 = 24
    let result = rt.ap(rt.ap(add(&rt), left), right);

    assert_eq!(rt.count(), 0);
    assert_eq!(force_expect_i32(result, &rt), 24);
    // inc called 3 times: once for base, once for left, once for right
    assert_eq!(rt.count(), 3);
}

// Nested thunks: outer thunk contains inner thunk, both memoized correctly.
// Uses separate counters to verify each function called exactly once.
#[test]
fn nested_thunks() {
    let rt = Runtime::new();
    let outer_count = Rc::new(Cell::new(0));
    let inner_count = Rc::new(Cell::new(0));

    let ic = inner_count.clone();
    let inner_fn = rt.lambda(move |x, rt| {
        ic.set(ic.get() + 1);
        rt.i32(force_expect_i32(x, rt) * 2)
    });

    let oc = outer_count.clone();
    let outer_fn = rt.lambda(move |x, rt| {
        oc.set(oc.get() + 1);
        rt.ap(inner_fn, x)
    });

    let thunk = rt.ap(outer_fn, rt.i32(5));

    // Force multiple times
    assert_eq!(force_expect_i32(thunk, &rt), 10);
    assert_eq!(force_expect_i32(thunk, &rt), 10);
    assert_eq!(force_expect_i32(thunk, &rt), 10);

    // Each function called exactly once
    assert_eq!(outer_count.get(), 1);
    assert_eq!(inner_count.get(), 1);
}

// Partial application creates shared closure.
// Uses separate counter to track outer lambda only.
#[test]
fn partial_application_sharing() {
    let rt = Runtime::new();
    let c = Rc::new(Cell::new(0));

    // add = \x.\y. x + y (but tracks when outer lambda is called)
    let cc = c.clone();
    let counted_add = rt.lambda(move |x, rt| {
        cc.set(cc.get() + 1);
        rt.lambda(move |y, rt| {
            rt.i32(force_expect_i32(x, rt) + force_expect_i32(y, rt))
        })
    });

    // add5 = add 5 (partial application)
    let add5 = rt.ap(counted_add, rt.i32(5));

    // Use add5 twice
    let r1 = rt.ap(add5, rt.i32(10));
    let r2 = rt.ap(add5, rt.i32(20));

    assert_eq!(c.get(), 0);
    assert_eq!(force_expect_i32(r1, &rt), 15);
    // add's outer lambda called once to produce the closure
    assert_eq!(c.get(), 1);
    assert_eq!(force_expect_i32(r2, &rt), 25);
    // Still 1 - add5 thunk was already forced, closure is shared
    assert_eq!(c.get(), 1);
}

// Multiple levels of sharing.
#[test]
fn deep_sharing() {
    let rt = Runtime::new();
    let inc = counted_inc(&rt);
    let inc2 = counted_inc(&rt);
    let inc3 = counted_inc(&rt);

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

    assert_eq!(rt.count(), 0);
    assert_eq!(force_expect_i32(result, &rt), 2 + 4 + 6); // 12
    // inc called exactly 3 times (once for a, once for b, once for c)
    assert_eq!(rt.count(), 3);
}

// Verify that forcing a value multiple times is idempotent.
#[test]
fn force_is_idempotent() {
    let rt = Runtime::new();
    let val = rt.i32(42);
    assert_eq!(rt.get_i32(val).unwrap(), 42);
    assert_eq!(rt.get_i32(val).unwrap(), 42);
    assert_eq!(rt.get_i32(val).unwrap(), 42);

    let thunk = rt.ap(rt.lambda(|x, _rt| x), rt.i32(99));
    assert_eq!(rt.get_i32(thunk).unwrap(), 99);
    assert_eq!(rt.get_i32(thunk).unwrap(), 99);
    assert_eq!(rt.get_i32(thunk).unwrap(), 99);
}

// Test closure that captures and uses multiple variables.
#[test]
fn closure_captures_multiple() {
    let rt = Runtime::new();

    let a = rt.ap(counted_const(&rt, 10), rt.i32(0));
    let b = rt.ap(counted_const(&rt, 20), rt.i32(0));
    let c_thunk = rt.ap(counted_const(&rt, 30), rt.i32(0));

    // Closure that captures a, b, c
    let sum_abc = rt.lambda(move |_, rt| {
        rt.i32(force_expect_i32(a, rt) + force_expect_i32(b, rt) + force_expect_i32(c_thunk, rt))
    });

    let result = rt.ap(sum_abc, rt.i32(0));

    assert_eq!(rt.count(), 0);
    assert_eq!(force_expect_i32(result, &rt), 60);
    assert_eq!(rt.count(), 3);

    // Force again - should not re-evaluate
    assert_eq!(force_expect_i32(result, &rt), 60);
    assert_eq!(rt.count(), 3);
}
