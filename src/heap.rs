//! Generic heap data structure.

use std::cell::{Cell, RefCell};

/// Pointer into the heap.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub struct HeapPtr(usize);

/// Heap operation statistics.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HeapStats {
    pub allocs: usize,
    pub reads: usize,
    pub writes: usize,
}

/// Generic heap that stores objects of type T.
pub struct Heap<T> {
    objects: RefCell<Vec<T>>,
    allocs: Cell<usize>,
    reads: Cell<usize>,
    writes: Cell<usize>,
}

impl<T: Clone> Heap<T> {
    pub fn new() -> Self {
        Heap {
            objects: RefCell::new(Vec::new()),
            allocs: Cell::new(0),
            reads: Cell::new(0),
            writes: Cell::new(0),
        }
    }

    pub fn len(&self) -> usize {
        self.objects.borrow().len()
    }

    pub fn stats(&self) -> HeapStats {
        HeapStats {
            allocs: self.allocs.get(),
            reads: self.reads.get(),
            writes: self.writes.get(),
        }
    }

    pub fn alloc(&self, obj: T) -> HeapPtr {
        self.allocs.set(self.allocs.get() + 1);
        let mut objects = self.objects.borrow_mut();
        let ptr = HeapPtr(objects.len());
        objects.push(obj);
        ptr
    }

    pub fn get(&self, ptr: HeapPtr) -> T {
        self.reads.set(self.reads.get() + 1);
        self.objects.borrow()[ptr.0].clone()
    }

    pub fn update(&self, ptr: HeapPtr, obj: T) {
        self.writes.set(self.writes.get() + 1);
        self.objects.borrow_mut()[ptr.0] = obj;
    }
}

impl<T: Clone> Default for Heap<T> {
    fn default() -> Self {
        Self::new()
    }
}
