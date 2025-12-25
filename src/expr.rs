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
}
