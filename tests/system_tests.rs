//! System tests for call-by-need implementation correctness.
//! These tests verify internal invariants and edge cases.

use call_by_need_in_rust::{ap, force_expect_i32, i32, lambda};

// Test that identity doesn't corrupt shared arguments.
#[test]
fn identity_preserves_sharing() {
    let arg = i32(42);
    let result = ap(lambda(|x| x), arg.clone());
    result.force();
    // arg should still be 42, not corrupted
    assert_eq!(arg.get_i32().unwrap(), 42);
}

// Diamond dependency: result depends on left and right, both depend on shared base.
// base should be evaluated only once.
#[test]
fn diamond_sharing() {
    static mut CALL_COUNT: i32 = 0;

    let inc = lambda(|x| {
        unsafe { CALL_COUNT += 1; }
        i32(force_expect_i32(&x) + 1)
    });

    let add = lambda(|a| {
        lambda(move |b| {
            let a = a.clone();
            i32(force_expect_i32(&a) + force_expect_i32(&b))
        })
    });

    // base = inc 10 (shared)
    let base = ap(inc.clone(), i32(10));
    // left = inc base
    let left = ap(inc.clone(), base.clone());
    // right = inc base
    let right = ap(inc, base);
    // result = left + right = (base+1) + (base+1) = 11+1 + 11+1 = 24
    let result = ap(ap(add, left), right);

    assert_eq!(unsafe { CALL_COUNT }, 0);
    assert_eq!(force_expect_i32(&result), 24);
    // inc called 3 times: once for base, once for left, once for right
    assert_eq!(unsafe { CALL_COUNT }, 3);
}

// Nested thunks: outer thunk contains inner thunk, both memoized correctly.
#[test]
fn nested_thunks() {
    static mut OUTER_COUNT: i32 = 0;
    static mut INNER_COUNT: i32 = 0;

    let inner_fn = lambda(|x| {
        unsafe { INNER_COUNT += 1; }
        i32(force_expect_i32(&x) * 2)
    });

    let outer_fn = lambda(move |x| {
        unsafe { OUTER_COUNT += 1; }
        let inner_fn = inner_fn.clone();
        ap(inner_fn, x)
    });

    let thunk = ap(outer_fn, i32(5));

    // Force multiple times
    assert_eq!(force_expect_i32(&thunk), 10);
    assert_eq!(force_expect_i32(&thunk), 10);
    assert_eq!(force_expect_i32(&thunk), 10);

    // Each function called exactly once
    assert_eq!(unsafe { OUTER_COUNT }, 1);
    assert_eq!(unsafe { INNER_COUNT }, 1);
}

// Partial application creates shared closure.
#[test]
fn partial_application_sharing() {
    static mut CALL_COUNT: i32 = 0;

    // add = \x.\y. x + y (but tracks when outer lambda is called)
    let add = lambda(|x| {
        unsafe { CALL_COUNT += 1; }
        lambda(move |y| {
            let x = x.clone();
            i32(force_expect_i32(&x) + force_expect_i32(&y))
        })
    });

    // add5 = add 5 (partial application)
    let add5 = ap(add, i32(5));

    // Use add5 twice
    let r1 = ap(add5.clone(), i32(10));
    let r2 = ap(add5, i32(20));

    assert_eq!(unsafe { CALL_COUNT }, 0);
    assert_eq!(force_expect_i32(&r1), 15);
    // add's outer lambda called once to produce the closure
    assert_eq!(unsafe { CALL_COUNT }, 1);
    assert_eq!(force_expect_i32(&r2), 25);
    // Still 1 - add5 thunk was already forced, closure is shared
    assert_eq!(unsafe { CALL_COUNT }, 1);
}

// Multiple levels of sharing.
#[test]
fn deep_sharing() {
    static mut CALL_COUNT: i32 = 0;

    let inc = lambda(|x| {
        unsafe { CALL_COUNT += 1; }
        i32(force_expect_i32(&x) + 1)
    });

    // Create a chain: a -> b -> c, all shared
    let a = ap(inc.clone(), i32(0)); // 1
    let b = ap(inc.clone(), a.clone()); // 2
    let c = ap(inc, b.clone()); // 3

    // Use each multiple times
    let add = lambda(|x| {
        lambda(move |y| {
            let x = x.clone();
            i32(force_expect_i32(&x) + force_expect_i32(&y))
        })
    });

    // (a + a) + (b + b) + (c + c)
    let aa = ap(ap(add.clone(), a.clone()), a);
    let bb = ap(ap(add.clone(), b.clone()), b);
    let cc = ap(ap(add.clone(), c.clone()), c);
    let aabb = ap(ap(add.clone(), aa), bb);
    let result = ap(ap(add, aabb), cc);

    assert_eq!(unsafe { CALL_COUNT }, 0);
    assert_eq!(force_expect_i32(&result), 2 + 4 + 6); // 12
    // inc called exactly 3 times (once for a, once for b, once for c)
    assert_eq!(unsafe { CALL_COUNT }, 3);
}

// Verify that forcing a value multiple times is idempotent.
#[test]
fn force_is_idempotent() {
    let val = i32(42);
    val.force();
    val.force();
    val.force();
    assert_eq!(val.get_i32().unwrap(), 42);

    let thunk = ap(lambda(|x| x), i32(99));
    thunk.force();
    thunk.force();
    thunk.force();
    assert_eq!(thunk.get_i32().unwrap(), 99);
}

// Test closure that captures and uses multiple variables.
#[test]
fn closure_captures_multiple() {
    static mut CALL_COUNT: i32 = 0;

    let make_val = |n| {
        lambda(move |_| {
            unsafe { CALL_COUNT += 1; }
            i32(n)
        })
    };

    let a = ap(make_val(10), i32(0));
    let b = ap(make_val(20), i32(0));
    let c = ap(make_val(30), i32(0));

    // Closure that captures a, b, c
    let sum_abc = lambda(move |_| {
        let a = a.clone();
        let b = b.clone();
        let c = c.clone();
        i32(force_expect_i32(&a) + force_expect_i32(&b) + force_expect_i32(&c))
    });

    let result = ap(sum_abc, i32(0));

    assert_eq!(unsafe { CALL_COUNT }, 0);
    assert_eq!(force_expect_i32(&result), 60);
    assert_eq!(unsafe { CALL_COUNT }, 3);

    // Force again - should not re-evaluate
    assert_eq!(force_expect_i32(&result), 60);
    assert_eq!(unsafe { CALL_COUNT }, 3);
}
