#![warn(missing_docs, clippy::all, clippy::pedantic)]
#![allow(
    clippy::needless_return,
    clippy::missing_docs_in_private_items,
    clippy::non_ascii_literal
)]

//! Cruncher, a crate for dynamic evaluation of mathematical expressions.
//!
//! This crate provide run-time evaluation of mathematical expressions,
//! embedded in strings. The easiest way to use this crate is with the
//! [`eval`](fn.eval.html) function:
//!
//! ```
//! use std::collections::HashMap;
//! assert_eq!(cruncher::eval("3 + 5 * 2", &HashMap::new()), Ok(13.0));
//! ```
//!
//! The second argument to `eval` is a [`HashMap`](struct.HashMap.html), that
//! can define variables:
//!
//! ```
//! use std::collections::HashMap;
//!
//! let mut context :HashMap<String,f64> = HashMap::new();
//! context.insert("a".into(), 3.5);
//! assert_eq!(cruncher::eval("2 * a", &context), Ok(7.0));
//! ```
//!
//! It is also possible to separate the parsing from the evaluation of an
//! expression with the [`Expr`](struct.Expr.html) type. This allow to reuse
//! the same expression with different values for variables.
//!
//! ```
//! use std::collections::HashMap;
//! use cruncher::{Expr};
//!
//! let expr = Expr::parse("3 + 5 * 2").unwrap();
//! assert_eq!(expr.eval(&HashMap::new()), Ok(13.0));
//!
//! let expr = Expr::parse("3 / c + b").unwrap();
//! let mut context :HashMap<String,f64> = HashMap::new();
//! context.insert("c".into(), 1.0);
//! context.insert("b".into(), 5.0);
//! assert_eq!(expr.eval(&context), Ok(8.0));
//!
//! context.insert("b".into(), 10.0);
//! assert_eq!(expr.eval(&context), Ok(13.0));
//! ```
//!
//! # Language definition
//!
//! The language implemented by cruncher can contain the following elements:
//!
//! - float literal values: `-12.456`, `+0.0045e78`, ...;
//! - left and right parenthesis;
//! - mathematical operators: `+` for addition, `-` for subtraction,
//!   `*` for multiplication, `/` for division and `^` for exponentiation
//!   (`std::f64::powf`);
//! - variables. Variables names are ASCII only, and can start by a letter or
//!   `_`, and can contain letters, digits, `.`, `_`, `[` or `]`.
//! - function call: `sin(a)`, `atan(22.0)`. The following function are
//!   accessible, with the same meaning as the corresponding `std::f64`
//!   function: `sqrt`, `cbrt`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`,
//!   `sinh`, `cosh`, `tanh`, `asinh`, `acosh`, `atanh`, `floor`, `ceil`,
//!   `abs`, `exp`, `ln`, `log2`, `log10`.
//!
//! Any other symbol is forbidden in the input.
//!
//! The mathematical operators obey the usual relations of associativity and
//! precedence, but still carry the floating point properties: addition is not
//! commutative, `NaN` and infinities exist, ...
//!
//! # Technical details
//!
//! cruncher is based on an AST interpreter, and uses a simple Shuntting-Yard
//! algorithm for parsing the expressions. It works only with `f64` data, and
//! perform a simple constant propagation to optimize the expressions.

#[macro_use]
extern crate lazy_static;

mod ast;
mod error;
mod expr;
mod jit;
mod lexer;
mod token;
mod util;

pub use ast::Ast;
pub use error::Error;
pub use expr::{eval, Expr};
pub use jit::JIT;
pub use lexer::is_variable;
pub use util::FUNCTIONS;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
