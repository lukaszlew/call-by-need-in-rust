# Lambda Body Representation: Copying and Sharing Tradeoffs

## The Core Question

When representing lambda closures, how should we store the body?

```
\x. body   -- body references x (param) and possibly free variables (captures)
```

On application with `arg`, we need to "substitute" `x -> arg` in body.

---

## Option A: Term-based (Current Implementation)

**Representation:**
```rust
struct TermClosure {
    param: Var,
    body: Term,                      // syntax tree
    env: HashMap<Var, HeapPtr>,      // captured bindings
}
```

**On apply:**
- Extend env with `param -> arg`
- Traverse Term, allocating HeapObjs
- Captures looked up in env (O(1) HashMap lookup)

**Pros:**
- Simple, correct
- Captures are shared (just HeapPtrs in env)
- No copying of captured structures

**Cons:**
- Stores env in every closure
- Re-traverses Term on every apply

**Cost:** O(body size) per apply

---

## Option B: HeapPtr Body with Graph Copy

**Representation:**
```rust
struct TermClosure {
    param_hole: HeapPtr,    // placeholder Hole in the graph
    body: HeapPtr,          // pre-allocated heap graph
    // no env! captures baked into graph
}
```

**On apply:**
- `copy_subst(body, param_hole, arg)` - copy graph, substituting hole -> arg

**The Sharing Problem:**

Captured values are now HeapPtrs embedded in the body graph. When copying:
- We must NOT recurse into captured structures (they don't contain our hole)
- We must NOT copy them (lose sharing, waste work)
- We must NOT force them (unnecessary evaluation)

### B1: No optimization (traverse everything)

```rust
fn copy_subst(&self, root: HeapPtr, hole: HeapPtr, arg: HeapPtr) -> HeapPtr {
    if root == hole { return arg; }
    match self.get(root) {
        App(f, x) => { /* recurse into both */ }
        TermClosure(tc) => { /* recurse into body */ }
        _ => root,
    }
}
```

**Problem:** Traverses captured structures unnecessarily. Worse than Term approach.

### B2: Timestamp optimization (FLAWED)

Idea: HeapPtr index is a timestamp. Captures allocated before hole, so:
```rust
if root.0 < hole.0 { return root; }  // allocated before hole, can't contain it
```

**Problem:** After substitution, body contains `arg` which may have index > hole.
Later applies would incorrectly recurse into `arg`. The invariant breaks across
substitutions.

### B3: Track (hole, closure_end) range

```rust
if root.0 < hole.0 || root.0 > closure_end.0 { return root; }
```

**Problem:** After substitution, new nodes are outside original range but may
contain inner lambda's holes. Range tracking doesn't survive substitution.

### B4: Mark nodes that reference hole

```rust
struct TermClosure {
    param_hole: HeapPtr,
    body: HeapPtr,
    references_param: HashSet<HeapPtr>,  // nodes with path to hole
}
```

Build during construction:
```rust
fn build(term, env, param) -> (HeapPtr, bool) {
    match term {
        Var(v) if v == param => (alloc(Hole), true),
        Var(v) => (env[v], false),
        App(f, x) => {
            let (f_ptr, f_has) = build(f, ...);
            let (x_ptr, x_has) = build(x, ...);
            (alloc(App(f_ptr, x_ptr)), f_has || x_has)
        }
    }
}
```

Copy:
```rust
if !references_param.contains(&root) { return root; }
```

**Problem:** After substitution, must recompute `references_param` for new nodes.
Gets complicated with nested lambdas (each has its own param to track).

---

## Option C: Typed Body Nodes (Explicit Capture Markers)

**Representation:**
```rust
enum BodyNode {
    Hole,                              // this lambda's param
    Capture(HeapPtr),                  // external value, don't recurse
    App(Box<BodyNode>, Box<BodyNode>),
    Lam { body: Box<BodyNode> },       // nested lambda
    Int(i32),
}

struct TermClosure {
    body: BodyNode,  // no env needed
}
```

**On apply:**
```rust
fn subst(&self, body: &BodyNode, arg: HeapPtr) -> HeapPtr {
    match body {
        Hole => arg,
        Capture(ptr) => *ptr,  // STOP HERE
        App(f, x) => self.app(self.subst(f, arg), self.subst(x, arg)),
        Lam { body } => /* create new closure */,
        Int(n) => self.i32(*n),
    }
}
```

**Pros:**
- Explicit stop markers for captures
- No accidental traversal into captured structures

**Cons:**
- Basically Term with different representation
- Same O(body size) cost

### C1: Nested Lambda Problem - The Capture Conflation

Consider `\x. z (\y. f x y)` where `z` and `f` are truly external (already HeapPtrs).

When building inner `\y. f x y`:
- `f` is truly external → `Capture(ptr_f)` ✓
- `y` is inner's param → `Hole` ✓
- `x` is outer's param, not yet bound → `Capture(???)` ???

**The problem:** `x` is not a HeapPtr yet! It's outer's Hole. If we represent it as
`Capture(Hole_x)`:

```
Outer body: App(Capture(ptr_z), InnerClosure)
Inner body: App(App(Capture(ptr_f), Capture(Hole_x)), Hole_y)
```

When copying outer (substituting Hole_x → arg1):
- Hit `Capture(ptr_z)` → stop, return ptr_z ✓
- Hit `Capture(ptr_f)` → stop, return ptr_f ✓
- Hit `Capture(Hole_x)` → **stop?** But we NEED to substitute here!

**The Capture wrapper hides that this IS our substitution target.**

`Capture` conflates two different things:
1. **Truly external** (ptr_f, ptr_z) - already HeapPtrs, never substitute
2. **Enclosing lambda's param** (x from inner's view) - must substitute when outer is applied

Different lambdas need to stop copying at different nodes:
- When copying `\x`: stop at `z` and `f`, but NOT at `x`
- When copying `\y`: stop at `z`, `f`, AND `x` (now bound)

A single `Capture` marker can't express "stop for inner but not for outer."

**Solution: De Bruijn indices**

```rust
enum BodyNode {
    Param(usize),        // 0 = this lambda, 1 = parent, 2 = grandparent...
    Capture(HeapPtr),    // truly external, already resolved
    App(Box<BodyNode>, Box<BodyNode>),
    Lam { body: Box<BodyNode> },
    Int(i32),
}
```

For `\x. \y. x + y`:
```
Lam {
    body: Lam {
        body: App(App(Capture(plus), Param(1)), Param(0))
        //                          ^^^^^^^^    ^^^^^^^^
        //                          outer x     inner y
    }
}
```

On apply outer with arg1:
- `Param(0)` in outer scope -> substitute with arg1
- In inner Lam body: `Param(1)` -> becomes `Param(0)` or `Capture(arg1)`

This requires de Bruijn shifting/substitution logic.

---

## Option D: Hybrid - Term with Inline HeapPtrs

**Representation:**
```rust
enum Term {
    Param,                    // this lambda's param
    Capture(HeapPtr),         // resolved external value
    App(Box<Term>, Box<Term>),
    Lam { body: Box<Term> },  // nested lambda
    Int(i32),
}
```

Like Term, but captures are HeapPtrs instead of Var names + env lookup.

**Nested lambdas:** Same de Bruijn issue as Option C1.

---

## Summary Comparison

| Approach | Captures | Body | Apply Cost | Complexity |
|----------|----------|------|------------|------------|
| A: Term + env | HashMap lookup | Term tree | O(body) | Simple |
| B: HeapPtr graph | Baked in | Heap graph | O(body) + copy overhead | Complex |
| C: BodyNode | Explicit Capture | Tree | O(body) | Medium |
| D: Term + HeapPtr | Inline | Tree | O(body) | Medium |

**Key Insight:** All approaches have O(body size) cost per apply. The differences are:
1. Where captures are stored (env vs inline)
2. Whether we risk traversing into captures (B without optimization)
3. How nested lambdas are handled (names vs de Bruijn)

---

## Recommendation

**Option A (current)** is the simplest and handles all cases correctly:
- Env HashMap cleanly separates captures from body structure
- Named variables with unique IDs avoid capture issues
- No risk of traversing into captured structures
- Well-understood semantics

**Option C/D with de Bruijn** might be worth exploring if:
- We want to eliminate env storage overhead
- We're willing to implement de Bruijn substitution
- We have a use case that benefits from inline captures

**Option B (HeapPtr graph)** has significant complexity without clear benefit:
- Timestamp optimization is flawed
- Marking adds overhead and complexity
- Risk of incorrect sharing/copying behavior
