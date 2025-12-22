# Explicit Term Representation (FOAS)

Second lambda representation alongside existing HOAS (Rust closures).

## Var

```rust
#[derive(Clone, Hash, Eq, PartialEq)]
struct Var { name: String, id: u64 }
```

Fresh ID via global `AtomicU64`. Assume initial terms don't shadow.

## Term (syntax only)

```rust
enum Term {
    Var(Var),
    Lam { captures: Vec<Var>, param: Var, body: Box<Term> },
    App(Box<Term>, Box<Term>),
    Int(i32),
    Plus,
}
```

STG-style: lambdas explicitly list captured variables.

## TermClosure (runtime value)

```rust
struct TermClosure {
    param: Var,
    body: Term,
    env: HashMap<Var, HeapPtr>,
}
```

## Integration

Extend existing `HeapObj` enum:

```rust
enum HeapObj {
    App(HeapPtr, HeapPtr),
    I32(i32),
    Closure(Closure),        // HOAS (fn pointer + explicit env)
    TermClosure(TermClosure), // FOAS
}
```

## Compilation

`fn compile(term: &Term, env: &HashMap<Var, HeapPtr>) -> HeapPtr`

- `Term::Var(v)` → lookup in env
- `Term::Int(n)` → `HeapObj::Value(Value::I32(n))`
- `Term::App(f, x)` → `HeapObj::App(compile(f), compile(x))`
- `Term::Lam{captures, param, body}` → `HeapObj::Value(Value::TermClosure{param, body, env})`
  - `body` stays as `Term` (compiled later on application)
  - `env` = subset of current env for captured vars only
- `Term::Plus` → curried plus closure

## Forcing TermClosure

When `force()` encounters `App` where f is `TermClosure`:
- Extend closure's env with `param -> arg`
- **Compile body now** with extended env
- Continue forcing result
