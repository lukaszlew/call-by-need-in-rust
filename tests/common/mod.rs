//! Shared test utilities for call-by-need tests.

use call_by_need_in_rust::{EnvExt, HeapPtr, Runtime};

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
