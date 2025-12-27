use std::collections::{HashMap, HashSet};

pub use super::{Env, ExprClosure, HeapObj, HeapPat, HeapPtr, Runtime, Var};

/// Pattern for lambda parameters.
#[derive(Debug, Clone, PartialEq)]
pub enum Pat {
    Var(Var),
    Tuple(Vec<Pat>),
}

impl Pat {
    /// Collect all variables bound by this pattern.
    pub fn vars(&self) -> Vec<&Var> {
        match self {
            Pat::Var(v) => vec![v],
            Pat::Tuple(pats) => pats.iter().flat_map(Pat::vars).collect(),
        }
    }

    /// Check if pattern binds a variable.
    pub fn binds(&self, var: &Var) -> bool {
        match self {
            Pat::Var(v) => v == var,
            Pat::Tuple(pats) => pats.iter().any(|p| p.binds(var)),
        }
    }

    /// Rename free occurrences of `from` to `to` in the pattern.
    /// (Patterns only bind, so this is a no-op, but included for completeness.)
    pub fn rename(&self, _from: &Var, _to: &Var) -> Pat {
        self.clone()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(Var),
    Lam {
        param: Pat,
        body: Box<Expr>,
    },
    /// Application in spine form: `App { head, spine: [a, b, c] }` represents `head a b c`.
    /// Invariant: `head` must not be `App` (use flat spine instead).
    /// Invariant: `spine` must not be empty (use head directly instead).
    App {
        head: Box<Expr>,
        spine: Vec<Expr>,
    },
    Tuple(Vec<Expr>),
    Int(i32),
    Plus,
}

impl Expr {
    /// Create an App, flattening if head is already an App.
    /// Returns head unchanged if spine is empty.
    pub fn app(head: Expr, mut spine: Vec<Expr>) -> Expr {
        if spine.is_empty() {
            return head;
        }
        match head {
            // Flatten: (f a b) c d -> f a b c d
            Expr::App {
                head: h,
                spine: mut s,
            } => {
                s.append(&mut spine);
                Expr::App { head: h, spine: s }
            }
            head => Expr::App {
                head: Box::new(head),
                spine,
            },
        }
    }

    /// Compute free variables in the expression.
    /// FV(x) = {x}, FV(λx.e) = FV(e) \ {x}, FV(e₁ e₂) = FV(e₁) ∪ FV(e₂)
    pub fn free_vars(&self) -> HashSet<Var> {
        match self {
            Expr::Var(v) => HashSet::from([v.clone()]),
            Expr::Lam { param, body } => {
                let mut fvs = body.free_vars();
                for v in param.vars() {
                    fvs.remove(v);
                }
                fvs
            }
            Expr::App { head, spine } => {
                let mut fvs = head.free_vars();
                for arg in spine {
                    fvs.extend(arg.free_vars());
                }
                fvs
            }
            Expr::Tuple(elems) => elems.iter().flat_map(Expr::free_vars).collect(),
            Expr::Int(_) | Expr::Plus => HashSet::new(),
        }
    }

    /// Create a Lam with a variable pattern.
    pub fn lam(param: Var, body: Expr) -> Expr {
        Expr::Lam {
            param: Pat::Var(param),
            body: Box::new(body),
        }
    }

    /// Create a Lam with a pattern.
    pub fn lam_pat(param: Pat, body: Expr) -> Expr {
        Expr::Lam {
            param,
            body: Box::new(body),
        }
    }

    /// Rename free occurrences of `from` to `to`.
    /// Respects shadowing: if `from` is bound by an inner lambda, don't rename inside it.
    pub fn rename(&self, from: &Var, to: &Var) -> Expr {
        match self {
            Expr::Var(v) if v == from => Expr::Var(to.clone()),
            Expr::Var(v) => Expr::Var(v.clone()),
            Expr::Lam { param, body } => {
                if param.binds(from) {
                    // from is shadowed, don't rename in body
                    self.clone()
                } else {
                    Expr::Lam {
                        param: param.clone(),
                        body: Box::new(body.rename(from, to)),
                    }
                }
            }
            Expr::App { head, spine } => Expr::App {
                head: Box::new(head.rename(from, to)),
                spine: spine.iter().map(|e| e.rename(from, to)).collect(),
            },
            Expr::Tuple(elems) => Expr::Tuple(elems.iter().map(|e| e.rename(from, to)).collect()),
            Expr::Int(_) | Expr::Plus => self.clone(),
        }
    }

    /// Allocate Expr to heap with free variable bindings.
    /// Bound vars get Param placeholders; free vars are resolved from env.
    pub fn to_heap(&self, rt: &Runtime, env: &Env) -> HeapPtr {
        match self {
            Expr::Var(v) => env
                .get(v)
                .copied()
                .unwrap_or_else(|| panic!("unbound variable: {:?}", v)),
            Expr::Int(n) => rt.i32(*n),
            Expr::App { head, spine } => {
                let mut ptr = head.to_heap(rt, env);
                for arg in spine {
                    ptr = rt.app(ptr, arg.to_heap(rt, env));
                }
                ptr
            }
            Expr::Lam { param, body } => {
                let mut env = env.clone();
                let heap_pat = param.to_heap(rt, &mut env);
                let body_ptr = body.to_heap(rt, &env);
                rt.alloc(HeapObj::ExprClosure(ExprClosure {
                    param: heap_pat,
                    env: HashMap::new(),
                    body: body_ptr,
                }))
            }
            Expr::Tuple(elems) => {
                let ptrs: Vec<_> = elems.iter().map(|e| e.to_heap(rt, env)).collect();
                rt.alloc(HeapObj::Tuple(ptrs))
            }
            Expr::Plus => rt.plus(),
        }
    }
}

impl Pat {
    /// Convert pattern to heap representation, allocating Param placeholders
    /// and adding variable bindings to env.
    pub fn to_heap(&self, rt: &Runtime, env: &mut Env) -> HeapPat {
        match self {
            Pat::Var(v) => {
                let param_ptr = rt.alloc(HeapObj::Param);
                env.insert(v.clone(), param_ptr);
                HeapPat::Var(param_ptr)
            }
            Pat::Tuple(pats) => {
                HeapPat::Tuple(pats.iter().map(|p| p.to_heap(rt, env)).collect())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rename_free_var() {
        // x -> y
        let expr = Expr::Var("x".into());
        assert_eq!(expr.rename(&"x".into(), &"y".into()), Expr::Var("y".into()));
    }

    #[test]
    fn rename_different_var() {
        // z unchanged when renaming x -> y
        let expr = Expr::Var("z".into());
        assert_eq!(expr.rename(&"x".into(), &"y".into()), Expr::Var("z".into()));
    }

    #[test]
    fn rename_in_body() {
        // \y. x -> \y. z when renaming x -> z
        let expr = Expr::lam("y".into(), Expr::Var("x".into()));
        let expected = Expr::lam("y".into(), Expr::Var("z".into()));
        assert_eq!(expr.rename(&"x".into(), &"z".into()), expected);
    }

    #[test]
    fn rename_shadowed() {
        // \x. x unchanged when renaming x -> y (x is bound)
        let expr = Expr::lam("x".into(), Expr::Var("x".into()));
        assert_eq!(expr.rename(&"x".into(), &"y".into()), expr);
    }

    #[test]
    fn rename_nested_shadow() {
        // \y. \x. x unchanged when renaming x -> z (x is bound by inner lambda)
        let expr = Expr::lam("y".into(), Expr::lam("x".into(), Expr::Var("x".into())));
        assert_eq!(expr.rename(&"x".into(), &"z".into()), expr);
    }

    #[test]
    fn rename_partial_shadow() {
        // \y. x (\x. x) -> \y. z (\x. x) when renaming x -> z
        // The free x becomes z, but the bound x stays
        let expr = Expr::lam(
            "y".into(),
            Expr::app(
                Expr::Var("x".into()),
                vec![Expr::lam("x".into(), Expr::Var("x".into()))],
            ),
        );
        let expected = Expr::lam(
            "y".into(),
            Expr::app(
                Expr::Var("z".into()),
                vec![Expr::lam("x".into(), Expr::Var("x".into()))],
            ),
        );
        assert_eq!(expr.rename(&"x".into(), &"z".into()), expected);
    }
}
