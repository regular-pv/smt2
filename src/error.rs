use std::result;
use std::fmt;
use source_span::Span;
use crate::{syntax, typing};
use crate::{Located, GroundSort, AbstractGroundSort, Environment};

pub enum Error<E: Environment> {
	UnknownLogic,
	InvalidSymbol(syntax::Symbol),
	InvalidIdent(syntax::Ident),
	UnknownSort,
	UnknownFunction(E::Ident),
	UndefinedVariable(E::Ident),
	NegativeArity,
	WrongNumberOfArguments(usize, usize, usize), // (expected_min, expected_max, given).
	Type(typing::Error<E::Sort>)
}

impl<E: Environment> Error<E> {
	pub fn at(self, location: Span) -> Located<Error<E>> {
		Located::new(self, location)
	}
}

pub type Result<T, E> = result::Result<T, Located<Error<E>>>;

impl<E: Environment> fmt::Display for Error<E> where E::Sort: fmt::Display, E::Ident: fmt::Display {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::Error::*;
		match self {
			UnknownLogic => write!(f, "unknown logic"),
			InvalidSymbol(sym) => write!(f, "unknown symbol `{}`", sym),
			InvalidIdent(id) => write!(f, "unknown ident `{}`", id),
			UnknownSort => write!(f, "unknown sort"),
			UnknownFunction(id) => write!(f, "unknown function `{}`", id),
			UndefinedVariable(id) => write!(f, "undefined variable `{}`", id),
			NegativeArity => write!(f, "arity must be positive or zero"),
			WrongNumberOfArguments(min, max, given) => {
				if min == max {
					write!(f, "wrong number of arguments (expected {}, given {})", min, given)
				} else {
					if given < min {
						write!(f, "wrong number of arguments (expected at least {}, given {})", min, given)
					} else {
						write!(f, "wrong number of arguments (expected at most {}, given {})", max, given)
					}
				}
			},
			Type(e) => write!(f, "type: {}", e)
		}
    }
}
