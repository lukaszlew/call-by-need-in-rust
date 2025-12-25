use std::collections::HashSet;

#[derive(Clone, Hash, Eq, PartialEq, Debug)]
pub struct Var(pub String);

impl Var {
    pub fn new(name: impl Into<String>) -> Self {
        Var(name.into())
    }
}

impl From<&str> for Var {
    fn from(s: &str) -> Self {
        Var::new(s)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(Var),
    Lam {
        param: Var,
        body: Box<Expr>,
    },
    /// Application in spine form: `App { head, spine: [a, b, c] }` represents `head a b c`.
    /// Invariant: `head` must not be `App` (use flat spine instead).
    /// Invariant: `spine` must not be empty (use head directly instead).
    App {
        head: Box<Expr>,
        spine: Vec<Expr>,
    },
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
                fvs.remove(param);
                fvs
            }
            Expr::App { head, spine } => {
                let mut fvs = head.free_vars();
                for arg in spine {
                    fvs.extend(arg.free_vars());
                }
                fvs
            }
            Expr::Int(_) | Expr::Plus => HashSet::new(),
        }
    }

    /// Create a Lam.
    pub fn lam(param: Var, body: Expr) -> Expr {
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
                if param == from {
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
            Expr::Int(_) | Expr::Plus => self.clone(),
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
