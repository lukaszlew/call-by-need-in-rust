use chumsky::prelude::*;

use crate::expr::{Expr, Pat, Var};

pub fn parse(input: &str) -> Expr {
    parser().parse(input).expect("parse error")
}

fn parser() -> impl Parser<char, Expr, Error = Simple<char>> {
    expr()
}

/// Parse a pattern: variable or tuple pattern.
fn pattern() -> impl Parser<char, Pat, Error = Simple<char>> + Clone {
    recursive(|pat| {
        let ident = text::ident().padded();
        let var_pat = ident.map(|s| Pat::Var(Var::new(s)));

        // Tuple pattern: (p1, p2, ...) with at least one comma
        let tuple_pat = pat
            .clone()
            .separated_by(just(',').padded())
            .at_least(1)
            .delimited_by(just('(').padded(), just(')').padded())
            .map(|pats| {
                if pats.len() == 1 {
                    // (p) is just grouping, not a 1-tuple
                    pats.into_iter().next().unwrap()
                } else {
                    Pat::Tuple(pats)
                }
            });

        tuple_pat.or(var_pat)
    })
}

fn expr() -> impl Parser<char, Expr, Error = Simple<char>> {
    recursive(|expr| {
        let ident = text::ident().padded();

        let var = ident.map(|s| Expr::Var(Var::new(s)));

        let lambda = just('\\')
            .ignore_then(pattern())
            .then_ignore(just('.').padded())
            .then(expr.clone())
            .map(|(param, body)| Expr::lam_pat(param, body))
            .padded();

        // Tuple or parenthesized expression
        let paren_or_tuple = expr
            .clone()
            .separated_by(just(',').padded())
            .at_least(1)
            .delimited_by(just('(').padded(), just(')').padded())
            .map(|exprs| {
                if exprs.len() == 1 {
                    // (e) is just grouping
                    exprs.into_iter().next().unwrap()
                } else {
                    Expr::Tuple(exprs)
                }
            })
            .padded();

        let int = just('-')
            .or_not()
            .then(text::int(10))
            .map(|(neg, s): (Option<char>, String)| {
                let n: i32 = s.parse().unwrap();
                Expr::Int(if neg.is_some() { -n } else { n })
            })
            .padded();

        let plus = just('+').to(Expr::Plus).padded();

        let atom = lambda.or(paren_or_tuple).or(int).or(plus).or(var);

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
        assert_eq!(parse(r"\x. x"), Expr::lam("x".into(), Expr::Var("x".into())));
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
        // \f. \x. f x
        assert_eq!(
            parse(r"\f. \x. f x"),
            Expr::lam(
                "f".into(),
                Expr::lam(
                    "x".into(),
                    Expr::app(Expr::Var("f".into()), vec![Expr::Var("x".into())])
                )
            )
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

    #[test]
    fn parse_tuple() {
        assert_eq!(parse("(1, 2)"), Expr::Tuple(vec![Expr::Int(1), Expr::Int(2)]));
        assert_eq!(
            parse("(1, 2, 3)"),
            Expr::Tuple(vec![Expr::Int(1), Expr::Int(2), Expr::Int(3)])
        );
    }

    #[test]
    fn parse_nested_tuple() {
        assert_eq!(
            parse("(1, (2, 3))"),
            Expr::Tuple(vec![
                Expr::Int(1),
                Expr::Tuple(vec![Expr::Int(2), Expr::Int(3)])
            ])
        );
    }

    #[test]
    fn parse_tuple_pattern_lambda() {
        // \(x, y). x
        assert_eq!(
            parse(r"\(x, y). x"),
            Expr::lam_pat(
                Pat::Tuple(vec![Pat::Var("x".into()), Pat::Var("y".into())]),
                Expr::Var("x".into())
            )
        );
    }

    #[test]
    fn parse_nested_pattern() {
        // \(x, (y, z)). y
        assert_eq!(
            parse(r"\(x, (y, z)). y"),
            Expr::lam_pat(
                Pat::Tuple(vec![
                    Pat::Var("x".into()),
                    Pat::Tuple(vec![Pat::Var("y".into()), Pat::Var("z".into())])
                ]),
                Expr::Var("y".into())
            )
        );
    }
}
