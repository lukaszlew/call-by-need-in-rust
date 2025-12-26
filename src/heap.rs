//! Generic heap data structure.

use std::cell::RefCell;

/// Pointer into the heap.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq)]
pub struct HeapPtr(usize);

/// Generic heap that stores objects of type T.
pub struct Heap<T> {
    objects: RefCell<Vec<T>>,
}

impl<T: Clone> Heap<T> {
    pub fn new() -> Self {
        Heap {
            objects: RefCell::new(Vec::new()),
        }
    }

    pub fn len(&self) -> usize {
        self.objects.borrow().len()
    }

    pub fn alloc(&self, obj: T) -> HeapPtr {
        let mut objects = self.objects.borrow_mut();
        let ptr = HeapPtr(objects.len());
        objects.push(obj);
        ptr
    }

    pub fn get(&self, ptr: HeapPtr) -> T {
        self.objects.borrow()[ptr.0].clone()
    }

    pub fn update(&self, ptr: HeapPtr, obj: T) {
        self.objects.borrow_mut()[ptr.0] = obj;
    }
}

impl<T: Clone> Default for Heap<T> {
    fn default() -> Self {
        Self::new()
    }
}
