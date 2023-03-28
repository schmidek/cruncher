use crate::error::Error;
use crate::lexer::is_variable;
use crate::token::{Op, Token};
use crate::util::FUNCTIONS;
use std::hash::{Hash, Hasher};

/// Ast nodes for the expressions
#[derive(Debug, Clone)]
pub enum Ast {
    /// A variable, to be resolved later
    Variable(String),
    /// A constant value
    Value(f64),
    /// <left> + <right>
    Add(Box<Ast>, Box<Ast>),
    /// <left> - <right>
    Sub(Box<Ast>, Box<Ast>),
    /// <left> * <right>
    Mul(Box<Ast>, Box<Ast>),
    /// <left> / <right>
    Div(Box<Ast>, Box<Ast>),
    /// <left> ^ <right>
    Exp(Box<Ast>, Box<Ast>),
    /// fn(<arg>)
    Function(fn(f64) -> f64, Box<Ast>),
}

impl PartialEq<Self> for Ast {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Ast::Variable(str), Ast::Variable(str2)) => str == str2,
            (Ast::Value(v), Ast::Value(v2)) => v.to_le_bytes() == v2.to_le_bytes(),
            (Ast::Add(a, b), Ast::Add(a2, b2)) => a == a2 && b == b2,
            (Ast::Sub(a, b), Ast::Sub(a2, b2)) => a == a2 && b == b2,
            (Ast::Mul(a, b), Ast::Mul(a2, b2)) => a == a2 && b == b2,
            (Ast::Div(a, b), Ast::Div(a2, b2)) => a == a2 && b == b2,
            (Ast::Exp(a, b), Ast::Exp(a2, b2)) => a == a2 && b == b2,
            (Ast::Function(a, b), Ast::Function(a2, b2)) => a == a2 && b == b2,
            _ => false,
        }
    }
}
impl Eq for Ast {}

impl Hash for Ast {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Ast::Variable(str) => {
                state.write_u8(0);
                str.hash(state)
            }
            Ast::Value(v) => {
                state.write_u8(1);
                v.to_le_bytes().hash(state)
            }
            Ast::Add(a, b) => {
                state.write_u8(2);
                a.hash(state);
                b.hash(state);
            }
            Ast::Sub(a, b) => {
                state.write_u8(3);
                a.hash(state);
                b.hash(state);
            }
            Ast::Mul(a, b) => {
                state.write_u8(4);
                a.hash(state);
                b.hash(state);
            }
            Ast::Div(a, b) => {
                state.write_u8(5);
                a.hash(state);
                b.hash(state);
            }
            Ast::Exp(a, b) => {
                state.write_u8(6);
                a.hash(state);
                b.hash(state);
            }
            Ast::Function(a, b) => {
                state.write_u8(7);
                a.hash(state);
                b.hash(state);
            }
        }
    }
}

impl Ast {
    /// Construct the AST for a vector of tokens in reverse polish notation.
    /// This function eats the tokens as it uses them
    pub fn from_tokens(tokens: &mut Vec<Token>, context: &str) -> Result<Self, Error> {
        let unoptimized_ast = Self::from_tokens_internal(tokens, context);
        if let Ok(unoptimized_ast) = unoptimized_ast {
            Ok(Self::optimize(unoptimized_ast))
        } else {
            unoptimized_ast
        }
    }

    fn from_tokens_internal(tokens: &mut Vec<Token>, context: &str) -> Result<Self, Error> {
        if let Some(token) = tokens.pop() {
            match token {
                Token::Value(value) => {
                    if let Some(&func) = FUNCTIONS.get(&value) {
                        let args = Box::new(Self::from_tokens(tokens, " in function call")?);
                        Ok(Self::Function(func, args))
                    } else if let Ok(number) = value.parse() {
                        Ok(Self::Value(number))
                    } else if is_variable(&value) {
                        Ok(Self::Variable(value))
                    } else {
                        Err(Error::ParseError(format!("invalid value {}", value)))
                    }
                }
                Token::Op(op) => {
                    let right = Box::new(Self::from_tokens(tokens, " after operator")?);
                    let left = Box::new(Self::from_tokens(tokens, " befor operator")?);
                    match op {
                        Op::Plus => Ok(Self::Add(left, right)),
                        Op::Minus => Ok(Self::Sub(left, right)),
                        Op::Mul => Ok(Self::Mul(left, right)),
                        Op::Div => Ok(Self::Div(left, right)),
                        Op::Exp => Ok(Self::Exp(left, right)),
                    }
                }
                other => panic!("Internal error: got {:?} token after shunting yard", other),
            }
        } else {
            Err(Error::ParseError(format!("empty expression{}", context)))
        }
    }

    /// If the AST node correspond to a constant, get `Some(constant)`. Else,
    /// get `None`
    pub fn value(&self) -> Option<f64> {
        if let Self::Value(value) = *self {
            Some(value)
        } else {
            None
        }
    }

    /// Optimize the AST by doing constants propagation
    pub fn optimize(self) -> Self {
        match self {
            Self::Variable(_) | Self::Value(_) => self,
            Self::Function(func, arg) => {
                let arg = arg.optimize();
                if let Some(arg) = arg.value() {
                    return Self::Value(func(arg));
                }
                return Self::Function(func, Box::new(arg));
            }
            Self::Add(left, right) => {
                let left = left.optimize();
                let right = right.optimize();
                if let Some(left) = left.value() {
                    if let Some(right) = right.value() {
                        return Self::Value(left + right);
                    }
                }
                return Self::Add(Box::new(left), Box::new(right));
            }
            Self::Sub(left, right) => {
                let left = left.optimize();
                let right = right.optimize();
                if let Some(left) = left.value() {
                    if let Some(right) = right.value() {
                        return Self::Value(left - right);
                    }
                }
                return Self::Sub(Box::new(left), Box::new(right));
            }
            Self::Mul(left, right) => {
                let left = left.optimize();
                let right = right.optimize();
                if let Some(left) = left.value() {
                    if let Some(right) = right.value() {
                        return Self::Value(left * right);
                    }
                }
                return Self::Mul(Box::new(left), Box::new(right));
            }
            Self::Div(left, right) => {
                let left = left.optimize();
                let right = right.optimize();
                if let Some(left) = left.value() {
                    if let Some(right) = right.value() {
                        return Self::Value(left / right);
                    }
                }
                return Self::Div(Box::new(left), Box::new(right));
            }
            Self::Exp(left, right) => {
                let left = left.optimize();
                let right = right.optimize();
                if let Some(left) = left.value() {
                    if let Some(right) = right.value() {
                        return Self::Value(left.powf(right));
                    }
                }
                return Self::Exp(Box::new(left), Box::new(right));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Ast;
    use crate::lexer::Lexer;

    #[test]
    // Verifies that we have reduced the input to a single value token when possible
    fn optimize() {
        let mut lexer = Lexer::new("3 + 5");
        let ast = Ast::from_tokens(&mut lexer.parse().unwrap(), "").unwrap();
        assert_eq!(ast.value(), Some(8.0));

        let mut lexer = Lexer::new("(3 + 5^2)*45");
        let ast = Ast::from_tokens(&mut lexer.parse().unwrap(), "").unwrap();
        assert_eq!(ast.value(), Some(1260.0));

        let mut lexer = Lexer::new("sqrt(9)");
        let ast = Ast::from_tokens(&mut lexer.parse().unwrap(), "").unwrap();
        assert_eq!(ast.value(), Some(3.0));
    }
}
