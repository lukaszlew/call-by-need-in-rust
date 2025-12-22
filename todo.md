What could we do next?
- Move the test counter to the runtime
- force and get should be perhaps merged
- Closure must be Rc<dyn Fn>, not Box. Box<dyn Fn> isn't Clone, but cloning is needed when
  memoizing shared values (e.g., identity returns its argument, which may be shared elsewhere).
- How to change enum Value to union Value? Rc is in a way. ManualDrop?
- We are verbose. How to write a macro that would synthesise the code for the lambdas, including the awkward clones.
- Runtime `force` has two recursive calls, so Rust stack is a part of the runtime.
- Simplest GC is not hard in itself and would be cool to see it. But it would need explicit access to closure captured variables, wouldn't it?
- Can we turn `force` calls into tail calls (jmp)? It would be nice to be closer to Haskell "jmp continuations".
- Would be very cool to have some runtime benchmarks and maybe compute number of allocations.
- Would be even cooler to use [Haskell's benchmarks](https://gitlab.haskell.org/ghc/ghc/-/wikis/building/running-tests/performance-tests)
- How could be print body of the lambdas? Abstract interpretation?
- It would be very interesting to have explicit weakening and contraction (instead of Rc?) and be closer to linear lambda calculus.
