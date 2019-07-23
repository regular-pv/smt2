use super::*;

pub enum Error<L, C: Clone + PartialEq, S: Sort, F: Function> {
    IO(std::io::Error),
    Server(String),
    Syntax(Located<syntax::Error>),
    Compile(Located<crate::error::Error<Client<L, C, S, F>>>),
    UnknownSort,
    UnknownUserFunction(F),
    UnknownFunction(Ident)
}

impl<L, C: Clone + PartialEq, S: Sort, F: Function> Error<L, C, S, F> {
    pub fn at(self, loc: Span) -> Located<Error<L, C, S, F>> {
        Located::new(self, loc)
    }
}

impl<L, C: Clone + PartialEq, S: Sort, F: Function> From<std::io::Error> for Error<L, C, S, F> {
    fn from(e: std::io::Error) -> Error<L, C, S, F> {
        Error::IO(e)
    }
}

impl<L, C: Clone + PartialEq, S: Sort, F: Function> From<Located<syntax::Error>> for Error<L, C, S, F> {
    fn from(e: Located<syntax::Error>) -> Error<L, C, S, F> {
        if let syntax::Error::Server(message) = e.as_ref() {
            Error::Server(message.clone())
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
    Syntax(Located<syntax::Error>),
    Compile(Located<crate::error::Error<Internal<L, C, F>>>)
}

impl<L, C: Clone + PartialEq, F: Function> From<std::io::Error> for InternalError<L, C, F> {
    fn from(e: std::io::Error) -> InternalError<L, C, F> {
        InternalError::IO(e)
    }
}

impl<L, C: Clone + PartialEq, F: Function> From<Located<syntax::Error>> for InternalError<L, C, F> {
    fn from(e: Located<syntax::Error>) -> InternalError<L, C, F> {
        if let syntax::Error::Server(message) = e.as_ref() {
            InternalError::Server(message.clone())
        } else {
            InternalError::Syntax(e)
        }
    }
}

impl<L, C: Clone + PartialEq, F: Function> From<Located<crate::error::Error<Internal<L, C, F>>>> for InternalError<L, C, F> {
    fn from(e: Located<crate::error::Error<Internal<L, C, F>>>) -> InternalError<L, C, F> {
        InternalError::Compile(e)
    }
}
