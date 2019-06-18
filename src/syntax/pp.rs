use std::fmt;

use crate::Location;
use super::Buffer;

pub struct PrettyPrinter<'b, I: 'b + Iterator<Item=char>, F: 'b + Clone> {
    buffer: &'b Buffer<I>,
    loc: Location<F>,
    hints: Vec<Hint<F>>
}

pub struct Hint<F: Clone> {
    loc: Location<F>
}

impl<'b, I: 'b + Iterator<Item=char>, F: 'b + Clone> PrettyPrinter<'b, I, F> {
    pub fn new(buffer: &'b Buffer<I>, loc: &Location<F>) -> PrettyPrinter<'b, I, F> {
        PrettyPrinter {
            buffer: buffer,
            loc: loc.clone(),
            hints: Vec::new()
        }
    }

    pub fn add_hint(&mut self, loc: &Location<F>) {
        self.hints.push(Hint {
            loc: loc.clone()
        })
    }
}

impl<'b, I: 'b + Iterator<Item=char>, F: 'b + Clone>  fmt::Display for PrettyPrinter<'b, I, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let n = self.loc.order()+1;
        let mut margin = String::with_capacity(n+4);
        for _ in 0..n {
            margin.push(' ');
        }
        match self.buffer.lines(&self.loc) {
            Some(lines) => {
                write!(f, "\x1b[1;34m{} |\x1b[m\n", margin)?;
                for (pos, line) in lines {
                    write!(f, "\x1b[1;34m{:#width$} |\x1b[m {}", pos.line+1, line, width=n)?;

                    for hint in self.hints.iter() {
                        // FIXME for now we ignore multi-line hints.
                        match hint.loc {
                            Location::Nowhere => (),
                            Location::Somewhere { start, end, .. } => {
                                if start.line == pos.line && start.column >= pos.column && end.line == start.line {
                                    let mut underline = String::with_capacity(end.column);
                                    for _ in 0..(start.column) {
                                        underline.push(' ');
                                    }
                                    for _ in start.column..end.column {
                                        underline.push('^');
                                    }
                                    write!(f, "\x1b[1;34m{} | \x1b[1;31m{}\x1b[m\n", margin, underline);
                                }
                            }
                        }

                    }
                }
                write!(f, "\x1b[1;34m{} |\x1b[m\n", margin)?;
            },
            None => ()
        }

        Ok(())
    }
}
