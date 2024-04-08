# Call-By-Need Lambda Calculus in Rust

In the past I made many implementations of lambda calculus in Haskell and OCaml.
I wanted to learn where is the difficulty of implementing lambda calculus without relying on lambda calculus implementation of the host language.
But each time I ended up to "parasite" on the host language features, typically:

- representation of the term in memory,
- term sharing in the memory,
- host language binders (through HOAS),
- garbage collection,
- sometimes typechecking.

So I decided to do it in Rust, to force myself to think about how terms are repsented and shared.
This repo is the result.

The implementation turned out to be pretty compact: say 100 lines, all-in-one-file.
All resides in [src/main.rs](https://github.com/lukaszlew/call-by-need-in-rust/blob/main/src/main.rs).

To me, the biggest "cheat" of this implementation is a reliance of Rust's lambda-abstraction memory representation .
I use it in an enssential way and it is not trivial.
I use Rust lambdas also for binders (HOAS) but this time I consider it a superficial "cheat".
GC is not implemented.
