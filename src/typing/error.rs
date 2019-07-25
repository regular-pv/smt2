use std::fmt;
use crate::{Sort, GroundSort};

pub enum Error<S: Sort> {
    Missmatch(GroundSort<S>, GroundSort<S>),
    Ambiguity
}

pub type Result<T, S> = std::result::Result<T, Error<S>>;

impl<S: Sort + fmt::Display> fmt::Display for Error<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;
        match self {
            Missmatch(expected, given) => write!(f, "sort missmatch: expected `{}` found `{}`", expected, given),
            Ambiguity => write!(f, "ambiguity")
        }
    }
}
