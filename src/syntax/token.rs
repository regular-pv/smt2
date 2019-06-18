use std::fmt;

use super::{Location, Localisable};

/**
 * Token
 */
#[derive(Clone)]
pub struct Token<F: Clone> {
	pub location: Location<F>,
	pub kind: Kind
}

impl<F: Clone> Localisable<F> for Token<F> {
	fn location(&self) -> &Location<F> {
		&self.location
	}
}

/**
 * Litteral constants.
 */
#[derive(Clone, PartialEq, Eq)]
pub enum Litteral {
	/**
	 * Signed numeric value.
	 */
	Int(i64)
}

#[derive(Clone, PartialEq, Eq)]
pub enum Kind {
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
	Litteral(Litteral)
}

impl Kind {
	pub fn at<F: Clone>(self, location: Location<F>) -> Token<F> {
		Token {
			location: location,
			kind: self
		}
	}
}

impl<F: Clone> fmt::Display for Token<F> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self.kind.fmt(f)
    }
}

impl fmt::Display for Kind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::Kind::*;
		match self {
			EndOfFile => write!(f, "<end of file>"),
			Begin => write!(f, "("),
			End => write!(f, ")"),
			Ident(id) => write!(f, "{}", id),
			Litteral(lit) => write!(f, "{}", lit)
		}
    }
}

impl fmt::Display for Litteral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::Litteral::*;
		match self {
			Int(i) => write!(f, "{}", i)
		}
    }
}
