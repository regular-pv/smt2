use super::*;

pub enum Error<L, S: Sort, F: Function> {
    IO(std::io::Error),
    Server(String),
    Syntax(syntax::Error<u32>),
    Compile(crate::error::Error<Client<L, S, F>, u32>),
    UnknownSort
}

impl<L, S: Sort, F: Function> From<std::io::Error> for Error<L, S, F> {
    fn from(e: std::io::Error) -> Error<L, S, F> {
        Error::IO(e)
    }
}

impl<L, S: Sort, F: Function> From<syntax::Error<u32>> for Error<L, S, F> {
    fn from(e: syntax::Error<u32>) -> Error<L, S, F> {
        if let syntax::error::Kind::Server(message) = e.kind {
            Error::Server(message)
        } else {
            Error::Syntax(e)
        }
    }
}

impl<L: fmt::Display, S: Sort + fmt::Display, F: Function + fmt::Display> fmt::Display for Error<L, S, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::IO(e) => write!(f, "IO: {}", e),
            Error::Server(msg) => write!(f, "solver reponded with an error: {}", msg),
            Error::Syntax(e) =>  write!(f, "syntax error in the solver response: {}", e),
            Error::Compile(e) => write!(f, "unable to compile the solver response: {}", e),
            Error::UnknownSort => write!(f, "unknown sort")
        }
    }
}

pub enum InternalError<L, F: Function> {
    IO(std::io::Error),
    Server(String),
    Syntax(syntax::Error<u32>),
    Compile(crate::error::Error<Internal<L, F>, u32>)
}

impl<L, F: Function> From<std::io::Error> for InternalError<L, F> {
    fn from(e: std::io::Error) -> InternalError<L, F> {
        InternalError::IO(e)
    }
}

impl<L, F: Function> From<syntax::Error<u32>> for InternalError<L, F> {
    fn from(e: syntax::Error<u32>) -> InternalError<L, F> {
        if let syntax::error::Kind::Server(message) = e.kind {
            InternalError::Server(message)
        } else {
            InternalError::Syntax(e)
        }
    }
}

impl<L, F: Function> From<crate::error::Error<Internal<L, F>, u32>> for InternalError<L, F> {
    fn from(e: crate::error::Error<Internal<L, F>, u32>) -> InternalError<L, F> {
        InternalError::Compile(e)
    }
}
