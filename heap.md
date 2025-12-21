# Heap Design

Explicit heap with mark-sweep GC, replacing Rc-based memory management.

## Motivation

Rc can't be traced by GC. To enable GC, we need explicit heap with index-based pointers.
Removing Rc requires removing Clone (Box<dyn Fn> isn't Clone). Indirections solve this.

## HeapPtr

```rust
#[derive(Clone, Copy)]
struct HeapPtr(usize);
```

Index into heap Vec.

Rejected:
- Rc<RefCell<HeapObj>> - can't do custom GC
- Raw pointer - unnecessary unsafety

## Heap

```rust
struct Heap {
    objects: Vec<RefCell<HeapObj>>,
}
```

RefCell needed: force() reads and writes different slots during recursion.

Rejected:
- Vec<HeapObj> with &mut - can't have multiple mutable borrows in force()

## HeapObj

```rust
enum HeapObj {
    App(HeapPtr, HeapPtr),
    Ind(HeapPtr),
    Value(Value),
}
```

## Indirection nodes

After forcing App, write `Ind(result_ptr)` instead of cloning result into App's slot.

Why: Box<dyn Fn> isn't Clone. Without Clone, can't copy HeapObj.
Indirections avoid copying - just point to the result.

GC can short-out indirection chains.

Rejected:
- Clone HeapObj - requires Rc<dyn Fn> for closures
- Two-level ClosureRef - more complex

## HOAS closures

```rust
Value::RustClosure(Box<dyn Fn(HeapPtr, &Heap) -> HeapPtr>)
```

Stored in heap, no Rc needed.

Rejected:
- Rc<dyn Fn> - unnecessary, heap manages lifetime

## GC

Mark-sweep. HOAS closures can't be traced into - accept leaks.

Rejected:
- Stop-and-copy - moves objects, breaks HOAS captured HeapPtrs
- Drop HOAS entirely - want both representations
