/// Possible tokens to find in the input string
#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    /// Any literal: value or variables
    Value(String),
    /// A boolean operator
    Op(Op),
    /// Left parenthesis
    LParen,
    /// Right parenthesis
    RParen,
}

/// Allowed operators in the algorithm
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Op {
    Plus,
    Minus,
    Mul,
    Div,
    Exp,
}

impl Op {
    /// Get the operator precedence. Operators with higher precedence should be
    /// evaluated first.
    pub fn precedence(self) -> u8 {
        match self {
            Op::Plus | Op::Minus => 1,
            Op::Mul | Op::Div => 2,
            Op::Exp => 3,
        }
    }

    /// Check if the operator is left associative
    pub fn is_left_associative(self) -> bool {
        match self {
            Op::Plus | Op::Minus | Op::Mul | Op::Div => true,
            Op::Exp => false,
        }
    }

    /// Check if the operator is right associative
    pub fn is_right_associative(self) -> bool {
        !self.is_left_associative()
    }
}
