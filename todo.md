Goal:
- compare to sharing graph, esp copying.
- perhaps implement sharing graph.
- have a test that captures the copying behavior, count size on that one test.

What could we do next?
- eval experiments
  - call by push value
  - linear logic reduction
  - It would be very interesting to have explicit weakening and contraction (instead of Rc?) and be closer to linear lambda calculus.
  - manual thunking
- pairs, sums
- Can we turn `force` calls into tail calls (jmp)? It would be nice to be closer to Haskell "jmp continuations".
- Simplest GC is not hard in itself and would be cool to see it. But it would need explicit access to closure captured variables, wouldn't it?
- Would be very cool to have some runtime benchmarks and maybe compute number of allocations.
- Would be even cooler to use [Haskell's benchmarks](https://gitlab.haskell.org/ghc/ghc/-/wikis/building/running-tests/performance-tests)

## Differences from STG

- **Term representation**: We use HOAS (Rust closures, opaque). STG uses FOAS (explicit Lam/Var/App).

- **Arity**: We treat all functions as taking 1 argument (curried). `plus 3 4` becomes `App(App(plus, 3), 4)` - two App nodes, two force cycles, one intermediate closure. STG tracks function arity. A 2-ary function applied to 2 args executes directly - no intermediate closure allocated. Under-saturated calls create PAP (partial application) objects.

- **Stacks**: `force_iter` uses one stack with Apply/Update frames. STG has three:
  - Argument stack: pending args. Our `Apply(HeapPtr)` is similar but one arg at a time.
  - Update stack: thunks to memoize. Our `Update(HeapPtr)` is the same.
  - Return stack: continuations after eval. We don't have this - the loop structure is our continuation.

  STG's separation enables arity: function grabs N args at once. We always do one Apply per App.

- **Memoization**: We clone the result HeapObj into the thunk's slot. STG writes an indirection pointer `Ind(result_ptr)` - no copying, just a pointer. GC later "shorts out" indirection chains. We clone because it's simple and cheap with Rc (just refcount bump).

  **Why Rc**: `Box<dyn Fn>` isn't Clone. We need Clone for memoization - when we update a thunk's slot with the result, we clone the HeapObj. Without Rc, we'd need indirection nodes (like STG) to avoid cloning.

  **What closures capture**: `&Runtime` is passed as parameter, not captured. Closures capture: HeapPtrs (lambda calculus variables like `x`, `f`), Rust values (i32 in `counted_const`), Rc<Cell<i32>> (test counters). The closure struct on heap contains: vtable pointer (8 bytes) + all captured values. A closure capturing 3 HeapPtrs is ~32 bytes.

- **Cycle detection**: If a thunk forces itself, we stack overflow. STG writes a "blackhole" marker before evaluating a thunk. Hitting a blackhole during evaluation means cycle detected - runtime error instead of hang.

- **Values**: Everything lives on the heap, even i32. STG has unboxed values that live in registers, never heap-allocated. Strict functions can take/return unboxed args directly. This avoids allocation for primitive operations.

- **GC**: We append forever (no collection). STG has generational GC. Our HOAS closures are opaque - can't trace into them to find captured HeapPtrs. Would need FOAS for proper GC.

- **ADTs**: We only have i32 and closures. STG has constructors `Con(tag, args)` and case expressions for pattern matching.

- **Spineless**: Traditional graph reduction has a "spine" - a chain of application nodes that must be traversed to find the function. `f x y z` is `App(App(App(f, x), y), z)`. To call f, you walk the spine collecting args. STG is "spineless" - saturated calls go directly to the function's entry code without building/traversing a spine. We have spines: nested App nodes that force() traverses one by one.

- **Tagless**: Traditional implementations check a tag (closure vs thunk vs constructor) before entering. STG is "tagless" - every heap object has an entry code pointer. To evaluate, just jump to the entry code. The code itself handles what to do (return value, apply args, update thunk, etc.). No runtime tag dispatch. We have tags: the `HeapObj` enum discriminant that `match` dispatches on.
