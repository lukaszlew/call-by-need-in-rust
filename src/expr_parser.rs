use chumsky::prelude::*;

use crate::expr::{Expr, Var};

pub fn parse(input: &str) -> Expr {
    parser().parse(input).expect("parse error")
}

fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    expr()
}

fn expr() -> impl Parser<char, Expr, Error = Simple<char>> {
    recursive(|expr| {
        let ident = text::ident().padded();

        let var = ident.map(|s| Expr::Var(Var::new(s)));

        let captures = ident
            .map(Var::new)
            .separated_by(just(','))
            .allow_trailing()
            .delimited_by(just('['), just(']'))
            .padded();

        let lambda = just('\\')
            .ignore_then(captures)
            .then(ident.map(Var::new))
            .then_ignore(just('.'))
            .then(expr.clone())
            .map(|((caps, param), body)| Expr::Lam {
                captures: caps,
                param,
                body: Box::new(body),
            })
            .padded();

        let parens = expr.delimited_by(just('('), just(')')).padded();

        let int = just('-')
            .or_not()
            .then(text::int(10))
            .map(|(neg, s): (Option<char>, String)| {
                let n: i32 = s.parse().unwrap();
                Expr::Int(if neg.is_some() { -n } else { n })
            })
            .padded();

        let plus = just('+').to(Expr::Plus).padded();

        let atom = lambda.or(parens).or(int).or(plus).or(var);

        atom.clone()
            .then(atom.repeated())
            .map(|(head, spine)| Expr::app(head, spine))
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
            Expr::App {
                head: Box::new(Expr::Var("f".into())),
                spine: vec![Expr::Var("x".into())],
            }
        );
    }

    #[test]
    fn parse_app_spine() {
        assert_eq!(
            parse("f x y"),
            Expr::App {
                head: Box::new(Expr::Var("f".into())),
                spine: vec![Expr::Var("x".into()), Expr::Var("y".into())],
            }
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
                    body: Box::new(Expr::App {
                        head: Box::new(Expr::Var("f".into())),
                        spine: vec![Expr::Var("x".into())],
                    }),
                }),
            }
        );
    }

    #[test]
    fn parse_parens() {
        assert_eq!(
            parse("f (g x)"),
            Expr::App {
                head: Box::new(Expr::Var("f".into())),
                spine: vec![Expr::App {
                    head: Box::new(Expr::Var("g".into())),
                    spine: vec![Expr::Var("x".into())],
                }],
            }
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

    #[test]
    fn parse_int() {
        assert_eq!(parse("42"), Expr::Int(42));
        assert_eq!(parse("-5"), Expr::Int(-5));
        assert_eq!(parse("  123  "), Expr::Int(123));
    }

    #[test]
    fn parse_plus() {
        assert_eq!(parse("+"), Expr::Plus);
    }

    #[test]
    fn parse_plus_application() {
        // + 1 2 = App { head: +, spine: [1, 2] }
        assert_eq!(
            parse("+ 1 2"),
            Expr::App {
                head: Box::new(Expr::Plus),
                spine: vec![Expr::Int(1), Expr::Int(2)],
            }
        );
    }
}
