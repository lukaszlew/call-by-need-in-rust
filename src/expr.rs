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
        captures: Vec<Var>,
        param: Var,
        body: Box<Expr>,
    },
    App(Box<Expr>, Box<Expr>),
    Int(i32),
    Plus,
}
