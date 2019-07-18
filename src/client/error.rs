use super::*;

pub enum Error<L, C: Clone + PartialEq, S: Sort, F: Function> {
    IO(std::io::Error),
    Server(String),
    Syntax(syntax::Error<u32>),
    Compile(crate::error::Error<Client<L, C, S, F>, u32>),
    UnknownSort,
    UnknownUserFunction(F),
    UnknownFunction(Ident)
}

impl<L, C: Clone + PartialEq, S: Sort, F: Function> From<std::io::Error> for Error<L, C, S, F> {
    fn from(e: std::io::Error) -> Error<L, C, S, F> {
        Error::IO(e)
    }
}

impl<L, C: Clone + PartialEq, S: Sort, F: Function> From<syntax::Error<u32>> for Error<L, C, S, F> {
    fn from(e: syntax::Error<u32>) -> Error<L, C, S, F> {
        if let syntax::error::Kind::Server(message) = e.kind {
            Error::Server(message)
        } else {
            Error::Syntax(e)
        }
    }
}

impl<L: fmt::Display, C: Clone + PartialEq, S: Sort + fmt::Display, F: Function + fmt::Display> fmt::Display for Error<L, C, S, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::IO(e) => write!(f, "IO: {}", e),
            Error::Server(msg) => write!(f, "solver reponded with an error: {}", msg),
            Error::Syntax(e) =>  write!(f, "syntax error in the solver response: {}", e),
            Error::Compile(e) => write!(f, "unable to compile the solver response: {}", e),
            Error::UnknownSort => write!(f, "unknown sort"),
            Error::UnknownUserFunction(fun) => write!(f, "unknown user function `{}`", fun),
            Error::UnknownFunction(id) => write!(f, "unknown function `{}`", id)
        }
    }
}

pub enum InternalError<L, C: Clone + PartialEq, F: Function> {
    IO(std::io::Error),
    Server(String),
    Syntax(syntax::Error<u32>),
    Compile(crate::error::Error<Internal<L, C, F>, u32>)
}

impl<L, C: Clone + PartialEq, F: Function> From<std::io::Error> for InternalError<L, C, F> {
    fn from(e: std::io::Error) -> InternalError<L, C, F> {
        InternalError::IO(e)
    }
}

impl<L, C: Clone + PartialEq, F: Function> From<syntax::Error<u32>> for InternalError<L, C, F> {
    fn from(e: syntax::Error<u32>) -> InternalError<L, C, F> {
        if let syntax::error::Kind::Server(message) = e.kind {
            InternalError::Server(message)
        } else {
            InternalError::Syntax(e)
        }
    }
}

impl<L, C: Clone + PartialEq, F: Function> From<crate::error::Error<Internal<L, C, F>, u32>> for InternalError<L, C, F> {
    fn from(e: crate::error::Error<Internal<L, C, F>, u32>) -> InternalError<L, C, F> {
        InternalError::Compile(e)
    }
}
