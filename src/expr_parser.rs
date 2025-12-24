use chumsky::prelude::*;

use crate::expr::Expr;

pub fn parse(input: &str) -> Expr {
    parser().parse(input).expect("parse error")
}

fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    expr()
}

fn expr() -> impl Parser<char, Expr, Error = Simple<char>> {
    recursive(|expr| {
        let ident = text::ident().padded();

        let var = ident.map(Expr::Var);

        let captures = ident
            .separated_by(just(','))
            .allow_trailing()
            .delimited_by(just('['), just(']'))
            .padded();

        let lambda = just('\\')
            .ignore_then(captures)
            .then(ident)
            .then_ignore(just('.'))
            .then(expr.clone())
            .map(|((caps, param), body)| Expr::Lam {
                captures: caps,
                param,
                body: Box::new(body),
            })
            .padded();

        let parens = expr.delimited_by(just('('), just(')')).padded();

        let atom = lambda.or(parens).or(var);

        atom.clone()
            .then(atom.repeated())
            .foldl(|f, x| Expr::App(Box::new(f), Box::new(x)))
    })
    .padded()
    .then_ignore(end())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_var() {
        assert_eq!(parse("x"), Expr::Var("x".into()));
        assert_eq!(parse("  foo  "), Expr::Var("foo".into()));
    }

    #[test]
    fn parse_identity() {
        assert_eq!(
            parse(r"\[] x. x"),
            Expr::Lam {
                captures: vec![],
                param: "x".into(),
                body: Box::new(Expr::Var("x".into())),
            }
        );
    }

    #[test]
    fn parse_const() {
        assert_eq!(
            parse(r"\[y] x. y"),
            Expr::Lam {
                captures: vec!["y".into()],
                param: "x".into(),
                body: Box::new(Expr::Var("y".into())),
            }
        );
    }

    #[test]
    fn parse_app() {
        assert_eq!(
            parse("f x"),
            Expr::App(
                Box::new(Expr::Var("f".into())),
                Box::new(Expr::Var("x".into())),
            )
        );
    }

    #[test]
    fn parse_app_left_assoc() {
        assert_eq!(
            parse("f x y"),
            Expr::App(
                Box::new(Expr::App(
                    Box::new(Expr::Var("f".into())),
                    Box::new(Expr::Var("x".into())),
                )),
                Box::new(Expr::Var("y".into())),
            )
        );
    }

    #[test]
    fn parse_nested_lambda() {
        assert_eq!(
            parse(r"\[] f. \[f] x. f x"),
            Expr::Lam {
                captures: vec![],
                param: "f".into(),
                body: Box::new(Expr::Lam {
                    captures: vec!["f".into()],
                    param: "x".into(),
                    body: Box::new(Expr::App(
                        Box::new(Expr::Var("f".into())),
                        Box::new(Expr::Var("x".into())),
                    )),
                }),
            }
        );
    }

    #[test]
    fn parse_parens() {
        assert_eq!(
            parse("f (g x)"),
            Expr::App(
                Box::new(Expr::Var("f".into())),
                Box::new(Expr::App(
                    Box::new(Expr::Var("g".into())),
                    Box::new(Expr::Var("x".into())),
                )),
            )
        );
    }

    #[test]
    fn parse_multiple_captures() {
        assert_eq!(
            parse(r"\[a, b, c] x. x"),
            Expr::Lam {
                captures: vec!["a".into(), "b".into(), "c".into()],
                param: "x".into(),
                body: Box::new(Expr::Var("x".into())),
            }
        );
    }
}
