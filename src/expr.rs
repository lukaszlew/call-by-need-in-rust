#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Var(String),
    Lam {
        captures: Vec<String>,
        param: String,
        body: Box<Expr>,
    },
    App(Box<Expr>, Box<Expr>),
}
