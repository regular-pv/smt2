use std::fmt;
use crate::Location;
use super::*;

pub type Result = std::fmt::Result;

pub trait Display {
    fn fmt(&self, f: &mut Formatter) -> Result;
}

pub struct Formatter<'f, 'a> {
    f: &'f mut std::fmt::Formatter<'a>,
    empty: bool,
    tabs: u32
}

pub struct PrettyPrint<'a, T>(pub &'a T);

impl<'a, T: Display> std::fmt::Display for PrettyPrint<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result {
        let mut ppf = Formatter {
            f: f,
            empty: true,
            tabs: 0
        };

        self.0.fmt(&mut ppf)
    }
}

impl<'f, 'a> Formatter<'f, 'a> {
    pub fn next(&mut self) -> Result {
        if self.empty {
            self.empty = false;
            Ok(())
        } else {
            write!(self.f, " ")
        }
    }

    pub fn begin(&mut self) -> Result {
        self.next()?;
        self.empty = true;
        write!(self.f, "(")
    }

    pub fn end(&mut self) -> Result {
        self.empty = false;
        write!(self.f, ")")
    }

    pub fn tab(&mut self) {
        self.tabs += 1;
    }

    pub fn backtab(&mut self) {
        self.tabs -= 1;
    }

    pub fn keyword(&mut self, name: &str) -> Result {
        self.next()?;
        write!(self.f, "{}", name)
    }

    pub fn symbol<F: Clone>(&mut self, sym: &Symbol<F>) -> Result {
        self.next()?;
        write!(self.f, "{}", sym)
    }

    /// Go to the next line
    pub fn split(&mut self) -> Result {
        write!(self.f, "\n")?;
        for _ in 0..self.tabs {
            write!(self.f, "\t")?;
        }
        self.empty = true;
        Ok(())
    }

    pub fn pseudo_list<T: Display>(&mut self, list: &[T]) -> Result {
        for e in list {
            e.fmt(self)?;
        }
        Ok(())
    }

    pub fn list<T: Display>(&mut self, list: &[T]) -> Result {
        self.begin()?;
        for e in list {
            e.fmt(self)?;
        }
        self.end()
    }

    pub fn tabulated_list<T: Display>(&mut self, list: &[T]) -> Result {
        self.begin()?;
        self.tab();
        for e in list {
            self.split();
            e.fmt(self)?;
        }
        self.backtab();
        self.split();
        self.end()
    }
}

impl<F: Clone> Display for Symbol<F> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        f.symbol(self)
    }
}

impl<F: Clone> Display for Ident<F> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        f.symbol(&self.id)
    }
}

impl<F: Clone> Display for Sort<F> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        if self.parameters.is_empty() {
            self.id.fmt(f)
        } else {
            f.begin()?;
            self.id.fmt(f)?;
            f.pseudo_list(&self.parameters)?;
            f.end()
        }
    }
}

impl<F: Clone> Display for Term<F> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        use TermKind::*;
        match &self.kind {
            Ident(id) => id.fmt(f),
            Let { bindings, body } => {
                f.begin()?;
                f.keyword("let")?;
                f.list(bindings)?;
                body.fmt(f)?;
                f.end()
            },
            Forall { vars, body } => {
                f.begin()?;
                f.keyword("forall")?;
                f.list(vars)?;
                body.fmt(f)?;
                f.end()
            },
            Exists { vars, body } => {
                f.begin()?;
                f.keyword("exists")?;
                f.list(vars)?;
                body.fmt(f)?;
                f.end()
            },
            Match { term, cases } => {
                f.begin()?;
                f.keyword("match")?;
                term.fmt(f)?;
                f.tabulated_list(cases)?;
                f.end()
            },
            Apply { id, args } => {
                if args.is_empty() {
                    id.fmt(f)
                } else {
                    f.begin()?;
                    id.fmt(f)?;
                    f.list(args)?;
                    f.end()
                }
            }
        }
    }
}

impl<F: Clone> Display for MatchCase<F> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        f.begin()?;
        self.pattern.fmt(f)?;
        self.term.fmt(f)?;
        f.end()
    }
}

impl<F: Clone> Display for Pattern<F> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        if self.args.is_empty() {
            self.constructor.fmt(f)
        } else {
            f.begin()?;
            self.constructor.fmt(f)?;
            f.list(&self.args)?;
            f.end()
        }
    }
}

impl<F: Clone> Display for Binding<F> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        f.begin()?;
        self.id.fmt(f)?;
        self.value.fmt(f)?;
        f.end()
    }
}

impl<F: Clone> Display for SortedVar<F> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        f.begin()?;
        self.id.fmt(f)?;
        self.sort.fmt(f)?;
        f.end()
    }
}
