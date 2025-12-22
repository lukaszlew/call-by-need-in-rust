//! Shared test utilities for call-by-need tests.

use call_by_need_in_rust::{HeapPtr, Runtime};

/// Create an increment function that ticks the counter when called.
pub fn counted_inc(rt: &Runtime) -> HeapPtr {
    rt.lambda([], |[], x, rt| {
        rt.tick();
        rt.i32(rt.get_i32(x) + 1)
    })
}

/// Create a thunk that returns `val` and ticks the counter when forced.
pub fn counted_const(rt: &Runtime, val: i32) -> HeapPtr {
    rt.lambda([], move |[], _, rt| {
        rt.tick();
        rt.i32(val)
    })
}

pub fn add(rt: &Runtime) -> HeapPtr {
    rt.plus()
}
