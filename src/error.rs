use std::error;
use std::fmt::{self, Display, Formatter};

/// Error types for cruncher
#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    /// Error while parsing an expression
    ParseError(String),
    /// Unknown variable during evaluation
    NameError(String),
}

impl Display for Error {
    fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
        match *self {
            Self::ParseError(ref message) => write!(fmt, "ParseError: {}", message),
            Self::NameError(ref message) => write!(fmt, "NameError: {}", message),
        }
    }
}

impl error::Error for Error {
    #[must_use]
    fn description(&self) -> &str {
        match *self {
            Self::ParseError(ref message) | Self::NameError(ref message) => message,
        }
    }

    #[must_use]
    fn cause(&self) -> Option<&dyn error::Error> {
        match *self {
            Self::ParseError(_) | Self::NameError(_) => None,
        }
    }
}
