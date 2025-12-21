//! Shared test utilities for call-by-need tests.

use call_by_need_in_rust::{force_expect_i32, HeapPtr, Runtime};
use std::cell::Cell;
use std::rc::Rc;

/// Shared counter for tracking function calls in tests.
pub type Counter = Rc<Cell<i32>>;

pub fn counter() -> Counter {
    Rc::new(Cell::new(0))
}

/// Create an increment function that counts how many times it's called.
pub fn counted_inc(rt: &Runtime, c: &Counter) -> HeapPtr {
    let c = c.clone();
    rt.lambda(move |x, rt| {
        c.set(c.get() + 1);
        rt.i32(force_expect_i32(&x, rt) + 1)
    })
}

/// Create a thunk that returns `val` and increments counter when forced.
pub fn counted_const(rt: &Runtime, c: &Counter, val: i32) -> HeapPtr {
    let c = c.clone();
    rt.lambda(move |_, rt| {
        c.set(c.get() + 1);
        rt.i32(val)
    })
}

pub fn add(rt: &Runtime) -> HeapPtr {
    rt.plus()
}
