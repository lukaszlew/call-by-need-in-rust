//! Didactic tests: These tests demonstrate key concepts of call-by-need.

use crate::common::{counted_const, counted_inc};
use crate::{expr_parser::parse, EnvExt, Expr, ForceMode, HeapPtr, Runtime, Var};
use rstest::rstest;
use std::collections::HashMap;

// -------------------------------------------------------------------------
// Basic application: (\x -> x) 5 = 5
// -------------------------------------------------------------------------
#[rstest]
fn identity_applied(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    let t = rt.app(rt.lam("x", &[], |env, _rt| env.v("x")), rt.i32(5));
    assert_eq!(rt.get_i32(t), 5);
}

// -------------------------------------------------------------------------
// Primitive addition: plus 3 4 = 7
// -------------------------------------------------------------------------
#[rstest]
fn plus_primitive(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    assert_eq!(
        rt.get_i32(rt.app(rt.app(rt.plus(), rt.i32(3)), rt.i32(4))),
        7
    );
}

// -------------------------------------------------------------------------
// Currying: fst and snd projections.
// fst = \x.\y.x    snd = \x.\y.y
// -------------------------------------------------------------------------
#[rstest]
fn fst_and_snd(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    let fst = rt.lam("x", &[], |env, rt| rt.lam("y", &[("x", env.v("x"))], |env, _rt| env.v("x")));
    let snd = rt.lam("x", &[], |_env, rt| rt.lam("y", &[], |env, _rt| env.v("y")));

    assert_eq!(rt.get_i32(rt.app(rt.app(fst, rt.i32(5)), rt.i32(6))), 5);
    assert_eq!(rt.get_i32(rt.app(rt.app(snd, rt.i32(5)), rt.i32(6))), 6);
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
    let counter = rt.i32(0);
    let expensive = counted_const(&rt, counter, 999);

    // const = \x.\y. x (ignores second argument)
    let const_fn = rt.lam("x", &[], |env, rt| rt.lam("y", &[("x", env.v("x"))], |env, _rt| env.v("x")));

    let unused_thunk = rt.app(expensive, rt.i32(0));
    let result = rt.app(rt.app(const_fn, rt.i32(42)), unused_thunk);

    assert_eq!(rt.get_i32(result), 42);
    assert_eq!(rt.get_i32(counter), 0); // expensive was never called!
}

// -------------------------------------------------------------------------
// Memoization: forcing twice doesn't re-evaluate.
// inc_twice 10 = 12, and inc is called exactly twice (not four times).
// -------------------------------------------------------------------------
#[rstest]
fn verify_call_by_need(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    let counter = rt.i32(0);
    let inc = counted_inc(&rt, counter);

    // inc_twice = \n. inc (inc n)
    let inc_twice = rt.lam("n", &[("inc", inc)], |env, rt| {
        rt.app(env.v("inc"), rt.app(env.v("inc"), env.v("n")))
    });
    let hopefully_12 = rt.app(inc_twice, rt.i32(10));

    assert_eq!(rt.get_i32(counter), 0);
    assert_eq!(rt.get_i32(hopefully_12), 12);
    assert_eq!(rt.get_i32(counter), 2);
    assert_eq!(rt.get_i32(hopefully_12), 12);
    assert_eq!(rt.get_i32(counter), 2); // Still 2! Memoization works.
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
    let counter = rt.i32(0);
    let expensive = counted_const(&rt, counter, 1);
    let thunk = rt.app(expensive, rt.i32(0));

    // Use thunk twice: add thunk thunk
    let result = rt.app(rt.app(rt.plus(), thunk), thunk);

    assert_eq!(rt.get_i32(counter), 0);
    assert_eq!(rt.get_i32(result), 2);
    assert_eq!(rt.get_i32(counter), 1); // Called once, not twice!
}

// -------------------------------------------------------------------------
// Church numerals: classic lambda calculus encoding of natural numbers.
// zero = \f.\x. x
// succ = \n.\f.\x. f (n f x)
// -------------------------------------------------------------------------
#[rstest]
fn church_numerals(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    let zero = rt.lam("f", &[], |_env, rt| rt.lam("x", &[], |env, _rt| env.v("x")));

    let succ = rt.lam("n", &[], |env, rt| {
        rt.lam("f", &[("n", env.v("n"))], |env, rt| {
            rt.lam("x", &[("n", env.v("n")), ("f", env.v("f"))], |env, rt| {
                rt.app(env.v("f"), rt.app(rt.app(env.v("n"), env.v("f")), env.v("x")))
            })
        })
    });

    // Convert church numeral to i32: apply n to inc and 0
    let inc = rt.lam("x", &[], |env, rt| rt.i32(rt.get_i32(env.v("x")) + 1));
    let to_int =
        |n: &HeapPtr| -> i32 { rt.get_i32(rt.app(rt.app(n.clone(), inc.clone()), rt.i32(0))) };

    let one = rt.app(succ.clone(), zero.clone());
    let two = rt.app(succ.clone(), one.clone());
    let three = rt.app(succ, two.clone());

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
    let i_comb = rt.lam("x", &[], |env, _rt| env.v("x"));
    let k_comb = rt.lam("x", &[], |env, rt| rt.lam("y", &[("x", env.v("x"))], |env, _rt| env.v("x")));
    let s_comb = rt.lam("x", &[], |env, rt| {
        rt.lam("y", &[("x", env.v("x"))], |env, rt| {
            rt.lam("z", &[("x", env.v("x")), ("y", env.v("y"))], |env, rt| {
                let xz = rt.app(env.v("x"), env.v("z"));
                let yz = rt.app(env.v("y"), env.v("z"));
                rt.app(xz, yz)
            })
        })
    });

    // I 5 = 5
    assert_eq!(rt.get_i32(rt.app(i_comb, rt.i32(5))), 5);

    // K 5 6 = 5
    assert_eq!(
        rt.get_i32(rt.app(rt.app(k_comb.clone(), rt.i32(5)), rt.i32(6))),
        5
    );

    // S K K x = x (S K K is identity)
    let skk = rt.app(rt.app(s_comb, k_comb.clone()), k_comb);
    assert_eq!(rt.get_i32(rt.app(skk, rt.i32(42))), 42);
}

// -------------------------------------------------------------------------
// Deep currying: f = \a.\b.\c. a
// -------------------------------------------------------------------------
#[rstest]
fn deep_currying(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    let f = rt.lam("a", &[], |env, rt| {
        rt.lam("b", &[("a", env.v("a"))], |env, rt| {
            rt.lam("c", &[("a", env.v("a"))], |env, _rt| env.v("a"))
        })
    });
    assert_eq!(
        rt.get_i32(rt.app(rt.app(rt.app(f, rt.i32(1)), rt.i32(2)), rt.i32(3))),
        1
    );
}

// =========================================================================
// Tests requiring env injection (can't be in txt files)
// =========================================================================

#[rstest]
fn foas_free_var(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    let env = HashMap::from([(Var::new("x"), rt.i32(42))]);
    assert_eq!(rt.get_i32(rt.expr(&env, &parse("x"))), 42);
}

#[rstest]
fn foas_capture_from_env(
    #[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode,
) {
    let rt = Runtime::new(mode);
    let env = HashMap::from([(Var::new("x"), rt.i32(100))]);
    let closure = rt.expr(&env, &parse(r"\y. x"));
    let result = rt.app(closure, rt.i32(999));
    assert_eq!(rt.get_i32(result), 100);
}

// =========================================================================
// Tests requiring exact AST structure (can't be in txt files)
// =========================================================================

#[rstest]
fn nbe_stuck_app(#[values(ForceMode::Recursive, ForceMode::Iterative)] mode: ForceMode) {
    let rt = Runtime::new(mode);
    // \f. f (\x. x) normalizes to \x0. x0 (\x1. x1)
    // This test checks the exact Expr structure, not just equality
    let result = rt.normalize(r"\f. f (\x. x)");
    let expected = Expr::lam(
        Var::new("x0"),
        Expr::App {
            head: Box::new(Expr::Var(Var::new("x0"))),
            spine: vec![Expr::lam(
                Var::new("x1"),
                Expr::Var(Var::new("x1")),
            )],
        },
    );
    assert_eq!(result, expected);
}
