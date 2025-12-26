//! Shared test utilities for call-by-need tests.

use crate::{expr_parser, EnvExt, ForceMode, HeapPtr, HeapStats, Runtime, Var};
use std::collections::HashMap;

/// Create an increment function that increments counter when called.
pub fn counted_inc(rt: &Runtime, counter: HeapPtr) -> HeapPtr {
    rt.lam("x", &[("counter", counter)], |env, rt| {
        rt.set_i32(env.v("counter"), rt.get_i32(env.v("counter")) + 1);
        rt.i32(rt.get_i32(env.v("x")) + 1)
    })
}

/// Create a thunk that returns `val` and increments counter when forced.
pub fn counted_const(rt: &Runtime, counter: HeapPtr, val: i32) -> HeapPtr {
    let val_ptr = rt.i32(val);
    rt.lam("_", &[("counter", counter), ("val", val_ptr)], |env, rt| {
        rt.set_i32(env.v("counter"), rt.get_i32(env.v("counter")) + 1);
        rt.i32(rt.get_i32(env.v("val")))
    })
}

pub fn add(rt: &Runtime) -> HeapPtr {
    rt.plus()
}

/// Statistics from running equality tests.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct TestStats {
    pub bindings: usize,
    pub tests: usize,
    pub heap_size: usize,
    pub heap_stats: HeapStats,
}

/// Run equality tests from a string.
/// Format:
/// - `let NAME = expr` defines a binding (evaluated once, added to env)
/// - `expr === expr` normalizes both and checks equality
/// - Empty lines and lines starting with `//` are skipped.
pub fn run_equality_tests(content: &str, mode: ForceMode) -> Result<TestStats, String> {
    let rt = Runtime::new(mode);
    let mut env = HashMap::new();
    let mut stats = TestStats::default();

    for (line_num, line) in content.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with("//") {
            continue;
        }

        // let binding
        if let Some(rest) = line.strip_prefix("let ") {
            let Some((name, expr)) = rest.split_once('=') else {
                return Err(format!("line {}: invalid let binding: {line}", line_num + 1));
            };
            let ptr = rt.expr(&env, &expr_parser::parse(expr.trim()));
            env.insert(Var::new(name.trim()), ptr);
            stats.bindings += 1;
            continue;
        }

        // equality test (===) or inequality test (/==)
        let (left, right, expect_equal) = if let Some((l, r)) = line.split_once("===") {
            (l, r, true)
        } else if let Some((l, r)) = line.split_once("/==") {
            (l, r, false)
        } else {
            return Err(format!("line {}: expected `===`, `/==`, or `let`: {line}", line_num + 1));
        };
        let left_ptr = rt.expr(&env, &expr_parser::parse(left.trim()));
        let right_ptr = rt.expr(&env, &expr_parser::parse(right.trim()));
        let left_norm = rt.readback(left_ptr, 0);
        let right_norm = rt.readback(right_ptr, 0);
        let are_equal = left_norm == right_norm;
        if are_equal != expect_equal {
            let msg = if expect_equal { "expected equal, got different" } else { "expected different, got equal" };
            return Err(format!(
                "line {}: {msg}\n  left:  {}\n  right: {}\n  left  normalized: {left_norm:?}\n  right normalized: {right_norm:?}",
                line_num + 1, left.trim(), right.trim()
            ));
        }
        stats.tests += 1;
    }
    stats.heap_size = rt.heap_size();
    stats.heap_stats = rt.stats();
    Ok(stats)
}
