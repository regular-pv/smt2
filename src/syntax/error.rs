use std::result;
use std::fmt;
use super::{Location, Localisable};
use super::token;

#[derive(Clone)]
pub struct Error<F: Clone> {
	pub location: Location<F>,
	pub kind: Kind
}

impl<F: Clone> Error<F> {
	fn new(kind: Kind, location: Location<F>) -> Error<F> {
		Error {
			location: location,
			kind: kind
		}
	}
}

impl<F: Clone> Localisable<F> for Error<F> {
	fn location(&self) -> &Location<F> {
		&self.location
	}
}

#[derive(Clone)]
pub enum Kind {
	MissingClosingParenthesis,
	UnexpectedToken(token::Kind, Option<token::Kind>),
	UnknownCommand(String),
	Server(String)
}

impl Kind {
	pub fn at<F: Clone>(self, location: Location<F>) -> Error<F> {
		Error::new(self, location)
	}
}

pub type Result<T, F> = result::Result<T, Error<F>>;

impl<F: Clone> fmt::Display for Error<F> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}", self.kind)
    }
}

impl fmt::Display for Kind {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::Kind::*;
		match self {
			MissingClosingParenthesis => write!(f, "missing parenthesis `)'"),
			UnexpectedToken(t, None) => write!(f, "unexpected token `{}'", t),
			UnexpectedToken(t, Some(e)) => write!(f, "unexpected token: excepted `{}', got `{}'", e, t),
			UnknownCommand(name) => write!(f, "unknown command `{}'", name),
			Server(name) => write!(f, "server error: {}", name)
		}
    }
}
