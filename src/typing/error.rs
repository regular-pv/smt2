use std::fmt;
use source_span::Span;
use crate::{Located, Sort, GroundSort};
use super::TypeRef;

pub enum Error<S: Sort> {
    Missmatch(SortMissmatch<S>),
    Ambiguity
}

impl<S: Sort> Error<S> {
    pub fn at(self, span: Span) -> Located<Error<S>> {
        Located::new(self, span)
    }
}

pub type Result<T, S> = std::result::Result<T, Located<Error<S>>>;

impl<S: Sort + fmt::Display> fmt::Display for Error<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;
        match self {
            Missmatch(_) => write!(f, "mismatched sorts"),
            Ambiguity => write!(f, "sort ambiguity")
        }
    }
}

impl<S: Sort + fmt::Display> crate::error::Informative for Error<S> {
	fn informations(&self, i: &mut crate::error::Infos) {
        use self::Error::*;
		match self {
			Missmatch(m) => {
                let (expected, given) = m.mismatched_sorts();
                i.set_label(format!("expected `{}`, found `{}`", expected, given));
                i.add_note(format!("\x1b[1mnote:\x1b[m expected sort `{}`\n         found sort `{}`", Expected(&m), Given(&m)));
            },
            Ambiguity => {
                i.set_label(format!("use the `(as {} <sort>)` type coercion construct to remove the ambiguity", i.content()));
            }
			_ => ()
		}
	}
}

pub enum SortMissmatch<S: Sort> {
    Var(usize, Span),
    Match {
        sort: S,
        parameters: Vec<SortMissmatch<S>>
    },
    Miss {
        expected_sort: S,
        expected_parameters: Vec<TypeRef<S>>,

        given_sort: S,
        given_parameters: Vec<TypeRef<S>>
    }
}

pub struct Expected<'a, S: Sort>(&'a SortMissmatch<S>);

impl<'a, S: Sort + fmt::Display> fmt::Display for Expected<'a, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use SortMissmatch::*;
        match &self.0 {
            Var(_, _) => write!(f, "_"),
            Match { sort, parameters } => {
                if parameters.is_empty() {
                    write!(f, "{}", sort)
                } else {
                    write!(f, "({}", sort)?;
                    for p in parameters {
                        write!(f, " {}", Expected(p))?;
                    }
                    write!(f, ")")
                }
            },
            Miss { expected_sort, expected_parameters, .. } => {
                if expected_parameters.is_empty() {
                    write!(f, "\x1b[1m{}\x1b[m", expected_sort)
                } else {
                    write!(f, "\x1b[1m({}", expected_sort)?;
                    for p in expected_parameters {
                        write!(f, " {}", p)?;
                    }
                    write!(f, ")\x1b[m")
                }
            }
        }
    }
}

pub struct Given<'a, S: Sort>(&'a SortMissmatch<S>);

impl<'a, S: Sort + fmt::Display> fmt::Display for Given<'a, S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use SortMissmatch::*;
        match &self.0 {
            Var(_, _) => write!(f, "_"),
            Match { sort, parameters } => {
                if parameters.is_empty() {
                    write!(f, "{}", sort)
                } else {
                    write!(f, "({}", sort)?;
                    for p in parameters {
                        write!(f, " {}", Given(p))?;
                    }
                    write!(f, ")")
                }
            },
            Miss { given_sort, given_parameters, .. } => {
                if given_parameters.is_empty() {
                    write!(f, "\x1b[1m{}\x1b[m", given_sort)
                } else {
                    write!(f, "\x1b[1m({}", given_sort)?;
                    for p in given_parameters {
                        write!(f, " {}", p)?;
                    }
                    write!(f, ")\x1b[m")
                }
            }
        }
    }
}

impl<S: Sort> SortMissmatch<S> {
    fn find_mismatched_sorts(&self) -> Option<(&S, &S)> {
        use SortMissmatch::*;
        match self {
            Var(_, _) => None,
            Match { parameters, .. } => {
                for p in parameters {
                    if let Some(m) = p.find_mismatched_sorts() {
                        return Some(m)
                    }
                }

                None
            },
            Miss { expected_sort, given_sort, .. } => {
                Some((expected_sort, given_sort))
            }
        }
    }

    pub fn mismatched_sorts(&self) -> (&S, &S) {
        self.find_mismatched_sorts().unwrap()
    }
}
