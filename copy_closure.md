# Plan: Mutable Param Cells with Indirection

## Memory Layout Examples

### Example 1: `(\x. x) 5`

**After to_heap:**
```
@0: Param                           -- placeholder for x
@1: ExprClosure { param: @0, env: {}, body: @0 }
```
Body points directly to the param placeholder.

**CURRENT: After apply with arg=@2 (I32(5)):**
```
@0: Param
@1: ExprClosure { param: @0, env: {}, body: @0 }
@2: I32(5)
```
eval_code(@0, {%0 -> @2}) looks up @0 in env, returns @2. No copying.

**NEW: After apply with arg=@2:**
```
@0: Param                           -- original (unused after copy)
@1: ExprClosure { ... }             -- original
@2: I32(5)
@3: Ind(@2)                         -- copied param, filled with indirection to 5
```
copy_code copies @0 to @3, substitute fills @3 with Ind(@2).
Result is @3, force follows Ind to get @2.

---

### Example 2: `(\x. \y. x) 5 6`

**After to_heap:**
```
@0: Param                           -- x placeholder
@1: Param                           -- y placeholder
@2: ExprClosure { param: @1, env: {}, body: @0 }   -- \y. x
@3: ExprClosure { param: @0, env: {}, body: @2 }   -- \x. \y. x
```

**CURRENT: After apply outer to @4=I32(5):**
```
@0: Param
@1: Param
@2: ExprClosure { param: @1, env: {}, body: @0 }
@3: ExprClosure { param: @0, env: {}, body: @2 }
@4: I32(5)
@5: ExprClosure { param: @1, env: {@0 -> @4}, body: @0 }  -- captured!
```
eval_code(@2, {@0->@4}) sees ExprClosure, captures env into new closure @5.
Body @0 is NOT copied, still points to original Param.

**CURRENT: After apply @5 to @6=I32(6):**
```
... (same as above)
@6: I32(6)
```
eval_code(@0, {@0->@4, @1->@6}) looks up @0, returns @4.
Result: 5. Correct!

**NEW: After apply outer to @4=I32(5):**
```
@0: Param                           -- original x
@1: Param                           -- original y
@2: ExprClosure { param: @1, body: @0 }
@3: ExprClosure { param: @0, body: @2 }
@4: I32(5)
@5: Param                           -- copied x
@6: Param                           -- copied y
@7: ExprClosure { param: @6, body: @5 }  -- copied inner closure
@8: Ind(@4)                         -- @5 filled: x = 5
```
copy_code(@2) copies whole structure: @0->@5, @1->@6, @2->@7.
substitute({@0->@5, @1->@6}, {@0->@4}) updates @5 to Ind(@4).
Result is @7 (copied inner closure).

**NEW: After apply @7 to @9=I32(6):**
```
... (same)
@9: I32(6)
@10: Param                          -- copied x (from @5)
@11: Param                          -- copied y (from @6)
@12: Ind(@4)                        -- @10 filled: x = 5 (via @5's Ind? No, fresh copy)
@13: Ind(@9)                        -- @11 filled: y = 6
```
Wait, this needs more thought...

Actually @5 is already Ind(@4). When we copy @7's body (@5), we copy Ind(@4), not Param.
So:
```
@9: I32(6)
@10: Ind(@4)                        -- copy of @5 (which is Ind)
@11: Param                          -- copy of @6
@12: Ind(@9)                        -- @11 filled: y = 6
```
Hmm, we're copying Ind nodes too. That's fine, they just forward.
Result body is @10, force(@10) -> force(@4) -> 5. Correct!

---

### Example 3: Sharing - `(\x. x x) 5`

**After to_heap:**
```
@0: Param                           -- x placeholder
@1: App(@0, @0)                     -- x x (both point to same Param!)
@2: ExprClosure { param: @0, body: @1 }
```

**CURRENT: After apply to @3=I32(5):**
```
@0: Param
@1: App(@0, @0)
@2: ExprClosure { param: @0, body: @1 }
@3: I32(5)
@4: App(@3, @3)                     -- eval_code created new App
```
eval_code(@1, {@0->@3}):
  - eval_code(@0) -> @3
  - eval_code(@0) -> @3
  - self.app(@3, @3) -> @4

**NEW: After apply to @3=I32(5):**
```
@0: Param
@1: App(@0, @0)
@2: ExprClosure { ... }
@3: I32(5)
@4: Param                           -- copied x
@5: App(@4, @4)                     -- copied App, both point to SAME copied Param
@6: Ind(@3)                         -- @4 filled: x = 5
```
copy_code(@1):
  - copy @0 -> @4 (first visit, add to param_map)
  - copy @0 -> @4 (second visit, reuse from param_map!)
  - App(@4, @4) -> @5
substitute: @4 becomes Ind(@3)
Result is @5. force sees App(@4, @4), forces @4 -> Ind(@3) -> I32(5).

Key: param_map ensures same Param copied once, preserving sharing!

---

### Summary of Differences

| Aspect | Current | New |
|--------|---------|-----|
| Param lookup | env HashMap at eval time | Ind pointer, set once |
| Structure copy | Interleaved with lookup | Separate copy phase |
| Sharing of Params | Via env (same key) | Via param_map during copy |
| When values resolve | During eval_code traversal | After copy, via substitute |
| ExprClosure.env | Stores captured values | Still needed for capture boundary |

## Goal
Separate "copy" from "substitute" in eval_code. Params become mutable cells that get filled in after copying.

## Current State
- `HeapObj::Param` is a marker (no data)
- `eval_code` interleaves copying (for App) with substitution (for Param lookup)
- `ExprClosure.env: HashMap<HeapPtr, HeapPtr>` captures values at closure boundaries

## New Design

### 1. Add Indirection Node
```rust
enum HeapObj {
    Ind(HeapPtr),  // indirection to value
    Param,         // unresolved placeholder
    // ... rest unchanged
}
```

### 2. Follow Indirections in Force
```rust
fn force(&self, ptr: HeapPtr) -> HeapObj {
    loop {
        match self.heap.get(ptr) {
            HeapObj::Ind(target) => ptr = target,
            obj => return // continue with normal force
        }
    }
}
```

### 3. Split eval_code into copy_code + substitute

**copy_code**: Deep copy body, Params remain Params, track mapping
```rust
fn copy_code(&self, ptr: HeapPtr, param_map: &mut HashMap<HeapPtr, HeapPtr>) -> HeapPtr {
    match self.heap.get(ptr) {
        HeapObj::Param => {
            let new_ptr = self.heap.alloc(HeapObj::Param);
            param_map.insert(ptr, new_ptr);
            new_ptr
        }
        HeapObj::App(f, g) => {
            let f2 = self.copy_code(f, param_map);
            let g2 = self.copy_code(g, param_map);
            self.app(f2, g2)
        }
        HeapObj::ExprClosure(c) => {
            // Copy closure, recursively copy body
            let new_body = self.copy_code(c.body, param_map);
            let new_param = param_map[&c.param];  // param was copied
            self.heap.alloc(HeapObj::ExprClosure(ExprClosure {
                param: new_param,
                env: HashMap::new(),  // env no longer needed?
                body: new_body,
            }))
        }
        // I32, RustClosure, etc: return as-is (shared)
        _ => ptr,
    }
}
```

**substitute**: Fill in Params via mutation
```rust
fn substitute(&self, param_map: &HashMap<HeapPtr, HeapPtr>, env: &HashMap<HeapPtr, HeapPtr>) {
    for (old_ptr, value) in env {
        if let Some(&new_ptr) = param_map.get(old_ptr) {
            self.heap.update(new_ptr, HeapObj::Ind(*value));
        }
    }
}
```

### 4. Update apply for ExprClosure
```rust
HeapObj::ExprClosure(c) => {
    let mut param_map = HashMap::new();
    let new_body = self.copy_code(c.body, &mut param_map);

    // Build env: param -> arg, plus captured env
    let mut env = c.env.clone();
    env.insert(c.param, arg);

    self.substitute(&param_map, &env);
    new_body  // return copied body with Params filled in
}
```

## Questions to Resolve

1. **Can we eliminate ExprClosure.env entirely?**
   - If we always copy+substitute immediately, env isn't needed
   - But we only substitute when closure is applied, not when captured
   - Need env to remember captured values until application

2. **Nested closures**: When copying, inner closures' params get copied too. Their param field must point to the new param ptr.

3. **Sharing**: Values (I32, RustClosure) are shared, not copied. Only structure (App, Param, ExprClosure) is copied.

4. **Force must handle Ind**: Any path that reads heap objects needs to follow indirections.

## Implementation Steps

1. Add `HeapObj::Ind(HeapPtr)` variant
2. Update `force` to follow Ind chains
3. Implement `copy_code`
4. Implement `substitute`
5. Update `apply` for ExprClosure to use copy+substitute
6. Run tests
7. Consider removing env from ExprClosure if possible

## Alternative: Param with Optional Value
Instead of separate Ind node:
```rust
HeapObj::Param(Option<HeapPtr>)  // None = hole, Some = filled
```
Simpler but conflates two concepts. Ind is more general (can point to any value type).
