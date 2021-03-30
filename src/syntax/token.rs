use source_span::Span;
use std::fmt;

use super::Located;

/**
 * Litteral constants.
 */
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Litteral {
	// /**
	//  * Signed numeric value.
	//  */
	// Int(i64),
	String(String),
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Token {
	/**
	 * End of file token.
	 */
	EndOfFile,

	/**
	 * Opening parenthesis.
	 */
	Begin,

	/**
	 * Closing parenthesis.
	 */
	End,

	/**
	 * Identifier.
	 */
	Ident(String),

	/**
	 * Litteral constant.
	 */
	Litteral(Litteral),
}

impl Token {
	pub fn at(self, span: Span) -> Located<Token> {
		Located::new(self, span)
	}
}

impl fmt::Display for Token {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::Token::*;
		match self {
			EndOfFile => write!(f, "<end of file>"),
			Begin => write!(f, "("),
			End => write!(f, ")"),
			Ident(id) => write!(f, "{}", id),
			Litteral(lit) => write!(f, "{}", lit),
		}
	}
}

impl fmt::Display for Litteral {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::Litteral::*;
		match self {
			// Int(i) => write!(f, "{}", i),
			String(string) => write!(f, "\"{}\"", string),
		}
	}
}
