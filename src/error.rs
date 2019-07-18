use std::result;
use std::fmt;
use crate::syntax;
use crate::{Location, Localisable, GroundSort, AbstractGroundSort, Environment};

pub struct Error<E: Environment, F: Clone> {
	pub location: Location<F>,
	pub kind: Kind<E, F>
}

impl<E: Environment, F: Clone> Error<E, F> {
	fn new(kind: Kind<E, F>, location: Location<F>) -> Error<E, F> {
		Error {
			location: location,
			kind: kind
		}
	}
}

impl<E: Environment, F: Clone> Localisable<F> for Error<E, F> {
	fn location(&self) -> &Location<F> {
		&self.location
	}
}

pub enum Kind<E: Environment, F: Clone> {
	UnknownLogic,
	InvalidSymbol(syntax::Symbol<F>),
	InvalidIdent(syntax::Ident<F>),
	UnknownSort,
	UnknownFunction(E::Ident),
	UndefinedVariable(E::Ident),
	NegativeArity,
	WrongNumberOfArguments(usize, usize, usize), // (expected_min, expected_max, given).
	TypeMissmatch(AbstractGroundSort<E::Sort>, GroundSort<E::Sort>),
	TypeAmbiguity
}

impl<E: Environment, F: Clone> Kind<E, F> {
	pub fn at(self, location: Location<F>) -> Error<E, F> {
		Error::new(self, location)
	}
}

pub type Result<T, E, F> = result::Result<T, Error<E, F>>;

impl<E: Environment, F: Clone> fmt::Display for Error<E, F> where E::Sort: fmt::Display, E::Ident: fmt::Display {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self.kind.fmt(f)
    }
}

impl<E: Environment, F: Clone> fmt::Display for Kind<E, F> where E::Sort: fmt::Display, E::Ident: fmt::Display {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use self::Kind::*;
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
			TypeMissmatch(expected, given) => write!(f, "expected sort `{}`, got `{}`", expected, given),
			TypeAmbiguity => write!(f, "sort parameters are ambiguous")
		}
    }
}
