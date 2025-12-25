# Tail Call Optimization in Call-by-Need

## Problem

The iterative `force_iter` avoids Rust stack overflow by using a heap-allocated `Vec`, but the Vec still grows O(n) for n tail calls:

```rust
HeapObj::App(f, arg) => {
    stack.push(UseValueTo::UpdateThunk(ptr));  // grows for each App
    stack.push(UseValueTo::ApplyArg(arg));
    ptr = f
}
```

For a tail call sequence `f -> g -> h -> value`, we accumulate `UpdateThunk` entries for each intermediate thunk.

## Options

### Option 1: Recognize tail positions statically

Mark tail positions at parse/compile time, skip `UpdateThunk` for them.

**Problem**: breaks memoization. If `f 1` tail-calls `g 2` and we skip updating `f 1`, a second force of `f 1` redoes the work.

**Verdict**: doesn't work. Degenerates into Option 3.

### Option 2: In-place overwrite

When `apply` returns an `App` (tail call), overwrite the current thunk cell with that `App` and re-enter:

```
Cell 100: App(f, 1)  →  Cell 100: App(g, 2)  →  Cell 100: I32(42)
```

All references to cell 100 see the updates. No indirection chains.

| Pro | Con |
|-----|-----|
| O(1) space for tail calls | Need to check if result is `App` after each apply |
| No indirection overhead | Loses original expression (debugging harder) |
| Memoization works - cell gets final value | Control flow slightly more complex |

### Option 3: Indirection cells

Add `HeapObj::Indirection(HeapPtr)`. When thunk evaluates to another thunk, become an indirection:

```
Cell 100: App(f, 1)  →  Cell 100: Ind(101)
Cell 101: App(g, 2)  →  Cell 101: Ind(102)
Cell 102: I32(42)
```

| Pro | Con |
|-----|-----|
| Conceptually clean | Chains grow without short-circuiting |
| Standard technique (GHC's STG) | Every `force` must follow indirections |
| Non-destructive - can inspect chains | Need GC or explicit short-circuiting |

## Recommendation

Option 2 (in-place overwrite) is more efficient. The check "is result an App?" is cheap and avoids all indirection overhead.

Option 3 is more proven/debuggable and standard in literature.

## Note: Black Holes

Neither current implementation nor these options handle infinite loops:

```
let x = x in x  -- forces x while forcing x
```

Solution: before forcing, overwrite thunk with `BlackHole`. If we try to force a `BlackHole`, panic. This is orthogonal to tail call optimization.
