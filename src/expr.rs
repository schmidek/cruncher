use crate::ast::Ast;
use crate::lexer::Lexer;
use crate::Error;
use hashbrown::HashMap;

/// Evaluate a single expression from `input`.
///
/// Returns `Ok(result)` if the evaluation is successful, or `Err(cause)` if
/// parsing or evaluating the expression failed.
///
/// # Example
///
/// ```
/// # use hashbrown::HashMap;
/// use cruncher::{eval};
///
/// assert_eq!(eval("45 - 2^3", None), Ok(37.0));
///
/// let mut context :HashMap<String,f64> = HashMap::new();
/// context.insert("a".into(), -5.0);
/// assert_eq!(eval("3 * a", &context), Ok(-15.0));
/// ```
pub fn eval<'a, C>(input: &str, context: C) -> Result<f64, Error>
where
    C: Into<Option<&'a HashMap<String, f64>>>,
{
    Expr::parse(input).and_then(|expr| expr.eval(context))
}

/// A parsed and optimized mathematical expression.
///
/// # Examples
/// ```
/// # use cruncher::{Expr};
/// # use hashbrown::HashMap;
/// let expr = Expr::parse("3 + 5 * 2").unwrap();
/// assert_eq!(expr.eval(None), Ok(13.0));
///
/// let mut context :HashMap<String,f64> = HashMap::new();
/// context.insert("a".into(), 42.0);
/// let expr = Expr::parse("-2 * a").unwrap();
/// assert_eq!(expr.eval(&context), Ok(-84.0));
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    ast: Ast,
}

impl Expr {
    /// Parse the given mathematical `expression` into an `Expr`.
    ///
    /// # Examples
    /// ```
    /// # use cruncher::Expr;
    /// // A valid expression
    /// assert!(Expr::parse("3 + 5 * 2").is_ok());
    /// // an invalid expression
    /// assert!(Expr::parse("3eff + 5 * 2").is_err());
    /// ```
    pub fn parse(expression: &str) -> Result<Self, Error> {
        let mut lexer = Lexer::new(expression);

        match Ast::from_tokens(&mut lexer.parse()?, "") {
            Ok(ast) => Ok(Self { ast }),
            Err(err) => Err(err),
        }
    }

    /// Evaluate the expression in a given optional `context`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use cruncher::{Expr};
    /// # use hashbrown::HashMap;
    /// let expr = Expr::parse("3 + 5 * 2").unwrap();
    /// assert_eq!(expr.eval(None), Ok(13.0));
    ///
    /// let expr = Expr::parse("3 + a").unwrap();
    ///
    /// let mut context :HashMap<String,f64> = HashMap::new();
    /// context.insert("a".into(), -5.0);
    /// assert_eq!(expr.eval(&context), Ok(-2.0));
    /// context.insert("a".into(), 2.0);
    /// assert_eq!(expr.eval(&context), Ok(5.0));
    /// ```
    pub fn eval<'a, C>(&self, context: C) -> Result<f64, Error>
    where
        C: Into<Option<&'a HashMap<String, f64>>>,
    {
        Self::inner_eval(&self.ast, context.into())
    }

    fn inner_eval(ast: &Ast, context: Option<&HashMap<String, f64>>) -> Result<f64, Error> {
        match *ast {
            Ast::Variable(ref name) => context
                // If we have a context
                .and_then(|c|
                    // and the context has a value for the variable name, use the value
                    c.get(name).map(std::borrow::ToOwned::to_owned))
                // Otherwise, we return an error
                .ok_or_else(|| Error::NameError(format!("name '{}' is not defined", name))),
            Ast::Value(number) => Ok(number),
            Ast::Add(ref left, ref right) => {
                Ok(Self::inner_eval(left, context)? + Self::inner_eval(right, context)?)
            }
            Ast::Sub(ref left, ref right) => {
                Ok(Self::inner_eval(left, context)? - Self::inner_eval(right, context)?)
            }
            Ast::Mul(ref left, ref right) => {
                Ok(Self::inner_eval(left, context)? * Self::inner_eval(right, context)?)
            }
            Ast::Div(ref left, ref right) => {
                Ok(Self::inner_eval(left, context)? / Self::inner_eval(right, context)?)
            }
            Ast::Exp(ref left, ref right) => {
                Ok(Self::inner_eval(left, context)?.powf(Self::inner_eval(right, context)?))
            }
            Ast::Function(ref func, ref arg) => Ok(func(Self::inner_eval(arg, context)?)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::error::Error;

    #[test]
    fn parse() {
        let valid_expressions = [
            "3 + +5e67",
            "(3 + -5)*45",
            "(3. + 5.0)*\t\n45",
            "(3 + 5^5e-6)*45",
            "sin(34.0) ^ sqrt(28.0)",
            "abc[ty8789]",
        ];
        for expr in &valid_expressions {
            assert!(Expr::parse(expr).is_ok());
        }
    }

    #[test]
    fn eval() {
        let mut context: HashMap<String, f64> = HashMap::new();
        context.insert("a".into(), 1.0);
        context.insert("b".into(), 2.0);

        let eval_pairs = [
            ("3 + 5", None, 8.0),
            ("2 - 5", None, -3.0),
            ("2 * 5", None, 10.0),
            ("10 / 5", None, 2.0),
            ("2 ^ 3", None, 8.0),
            ("-3", None, -3.0),
            ("25 + -3", None, 22.0),
            ("25 - -3", None, 28.0),
            ("25 - -3", None, 28.0),
            ("3 + 5 * 2", None, 13.0),
            ("sqrt(9)", None, 3.0),
            ("sin(18.0) * 3", None, 3.0 * f64::sin(18.0)),
            ("2 * a", Some(&context), 2.0),
            ("(a + b)^2", Some(&context), 9.0),
        ];
        for eval_pair in &eval_pairs {
            assert_eq!(super::eval(eval_pair.0, eval_pair.1), Ok(eval_pair.2));
        }

        let result = super::eval("2 * z", &context);
        assert_eq!(
            result.err().unwrap().description(),
            "name 'z' is not defined"
        );
        let result = super::eval("2 * a", None);
        assert_eq!(
            result.err().unwrap().description(),
            "name 'a' is not defined"
        );
    }

    // use std::time::Instant;
    //
    // #[test]
    // fn bench() {
    //     let watch = Instant::now();
    //     let t = Expr::parse("(var1 + var2 * 3) / (2 + 3) - something").unwrap();
    //     let capacity = 5_000_000;
    //     let iterations = 5_000_000;
    //     let mut dicts = Vec::with_capacity(capacity);
    //     for i in 1..=iterations {
    //         let mut dict: HashMap<String, f64> = HashMap::with_capacity(3);
    //         dict.insert("var1".to_owned(), 10.0 + f64::from(i));
    //         dict.insert("var2".to_owned(), 20.0 + f64::from(i));
    //         dict.insert("something".to_owned(), 30.0 + f64::from(i));
    //         dicts.push(dict);
    //     }
    //     let watch = watch.elapsed();

    //     let mut results: Vec<f64> = Vec::with_capacity(capacity);

    //     let watch2 = Instant::now();
    //     for dict in &dicts {
    //         results.push(t.eval(dict).unwrap());
    //     }
    //     let watch2 = watch2.elapsed();

    //     println!("{}", results[0]);
    //     println!("{}", watch.as_millis());
    //     println!("{}", watch2.as_millis());
    // }
}
