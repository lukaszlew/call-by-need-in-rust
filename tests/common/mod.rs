//! Shared test utilities for call-by-need tests.

use call_by_need_in_rust::{HeapPtr, Runtime};

/// Create an increment function that increments counter when called.
pub fn counted_inc(rt: &Runtime, counter: HeapPtr) -> HeapPtr {
    rt.lambda([counter], |&[counter], x, rt| {
        rt.set_i32(counter, rt.get_i32(counter) + 1);
        rt.i32(rt.get_i32(x) + 1)
    })
}

/// Create a thunk that returns `val` and increments counter when forced.
pub fn counted_const(rt: &Runtime, counter: HeapPtr, val: i32) -> HeapPtr {
    let val_ptr = rt.i32(val);
    rt.lambda([counter, val_ptr], |&[counter, val_ptr], _, rt| {
        rt.set_i32(counter, rt.get_i32(counter) + 1);
        rt.i32(rt.get_i32(val_ptr))
    })
}

pub fn add(rt: &Runtime) -> HeapPtr {
    rt.plus()
}
