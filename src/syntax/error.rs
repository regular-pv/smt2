use std::result;
use std::fmt;
use source_span::Span;
use crate::Located;
use super::Token;

// #[derive(Clone)]
pub enum Error {
	IO(std::io::Error),
	MissingClosingParenthesis,
	UnexpectedToken(Token, Option<Token>),
	UnknownCommand(String),
	Server(String)
}

impl Error {
	pub fn at(self, span: Span) -> Located<Error> {
		Located::new(self, span)
	}
}

pub type Result<T> = result::Result<T, Located<Error>>;

impl fmt::Display for Error {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::Error::*;
		match self {
			IO(e) => write!(f, "io: {}", e),
			MissingClosingParenthesis => write!(f, "missing parenthesis `)'"),
			UnexpectedToken(t, None) => write!(f, "unexpected token `{}'", t),
			UnexpectedToken(t, Some(e)) => write!(f, "unexpected token: excepted `{}', got `{}'", e, t),
			UnknownCommand(name) => write!(f, "unknown command `{}'", name),
			Server(name) => write!(f, "server error: {}", name)
		}
    }
}
