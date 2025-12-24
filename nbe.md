# Normalization by Evaluation (NbE) / Readback

## Goal
Convert runtime values to β-normal forms for comparing arbitrary lambda terms.

## Core Idea
```
readback(closure) = λx. readback(closure @ Neutral(x))
readback(Neutral(n)) = Var(n)
readback(NeutralApp(f, x)) = App(readback(f), readback(x))
```

## New HeapObj Variants
```rust
Neutral(usize),               // de Bruijn level (free var)
NeutralApp(HeapPtr, HeapPtr), // stuck application
```

## Change apply Signature
```rust
// Before
fn apply(&self, closure: HeapObj, arg: HeapPtr) -> HeapPtr

// After
fn apply(&self, f_ptr: HeapPtr, arg: HeapPtr) -> HeapPtr {
    let f = self.force(f_ptr);
    match f {
        Closure(c) => (c.code)(c.env.as_ptr(), arg, self),
        ExprClosure(tc) => { /* existing */ },
        Neutral(_) | NeutralApp(_, _) => self.alloc(NeutralApp(f_ptr, arg)),
        _ => panic!("expected closure"),
    }
}
```

## Update Force Functions
```rust
// force_iter
Some(ApplyArg(arg)) => ptr = self.apply(ptr, arg)  // was: apply(value, arg)

// force_recursive
let result_ptr = self.apply(f, arg);  // was: apply(self.force_recursive(f), arg)
```

## Readback Implementation
```rust
pub fn readback(&self, ptr: HeapPtr, depth: usize) -> Expr {
    match self.force(ptr) {
        Closure(_) | ExprClosure(_) => {
            let var = self.alloc(Neutral(depth));
            let body = self.apply(ptr, var);
            Lam { param: x{depth}, body: readback(body, depth+1) }
        }
        Neutral(level) => Var(x{level}),
        NeutralApp(f, x) => App(readback(f), readback(x)),
        I32(n) => Int(n),
        _ => panic!(),
    }
}

pub fn normalize(&self, src: &str) -> Expr {
    self.readback(self.run(src), 0)
}
```

## Test Format
```
expr1 == expr2   # both normalize to same Expr
```

## Example
```
Input:  \f. f (\x. x)
        ↓ readback at depth 0
        ↓ apply to Neutral(0)
        ↓ body becomes: Neutral(0) applied to (\x.x)
        ↓ stuck! → NeutralApp(Neutral(0), ptr_to_id)
        ↓ readback NeutralApp
Output: \x0. x0 (\x1. x1)
```

## Note: Primitives

NbE works for pure lambda calculus. Primitives like `+` need special handling:

```rust
// Problem: plus calls get_i32 which panics on Neutral
fn plus_inner(a: HeapPtr, b: HeapPtr, rt: &Runtime) -> HeapPtr {
    rt.i32(rt.get_i32(a) + rt.get_i32(b))  // ← panics if a or b is Neutral
}

// Solution: make primitives neutral-aware
fn plus_inner(a: HeapPtr, b: HeapPtr, rt: &Runtime) -> HeapPtr {
    match (rt.force(a), rt.force(b)) {
        (I32(x), I32(y)) => rt.i32(x + y),
        _ => rt.alloc(NeutralApp(...))  // stuck
    }
}
```

For now: only NbE pure lambda terms (no `+`), or ensure all primitives are evaluated before readback.

## Implementation Order
1. Add Neutral, NeutralApp to HeapObj
2. Change apply signature
3. Update force_recursive
4. Update force_iter
5. Add readback, normalize to Runtime
6. Add tests
7. Run existing tests
