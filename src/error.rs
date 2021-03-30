use crate::{syntax, typing};
use crate::{Environment, Located};
use source_span::{Metrics, SourceBuffer, Span};
use std::fmt;
use std::result;

pub struct Infos {
	content: String,
	label: Option<String>,
	notes: Vec<String>,
	highlights: Vec<(Span, Option<String>)>,
}

impl Infos {
	pub fn content(&self) -> &str {
		&self.content
	}

	pub fn set_label(&mut self, label: String) {
		self.label = Some(label)
	}

	pub fn add_note(&mut self, note: String) {
		self.notes.push(note)
	}

	pub fn add(&mut self, span: Span, label: Option<String>) {
		self.highlights.push((span, label))
	}

	pub fn print_at<
		I: Informative + fmt::Display,
		F: fmt::Display,
		E,
		B: Iterator<Item = result::Result<char, E>>,
		M: Metrics,
	>(
		e: &I,
		file: F,
		buffer: &SourceBuffer<E, B, M>,
		viewport: Span,
		span: Span,
		metrics: &M,
	) -> result::Result<(), E> {
		let content = buffer.iter_span(span).into_string()?;

		let mut i = Infos {
			content: content,
			label: None,
			notes: Vec::new(),
			highlights: Vec::new(),
		};

		let mut pp = source_span::fmt::Formatter::new();

		e.informations(&mut i);

		pp.add(span, i.label, source_span::fmt::Style::Error);

		for (h_span, h_label) in i.highlights.into_iter() {
			pp.add(h_span, h_label, source_span::fmt::Style::Note);
		}

		let line_number_margin = (((viewport.last().line + 1) as f32).log10() as usize) + 1;
		let mut margin = String::new();
		for _ in 0..line_number_margin {
			margin.push(' ');
		}

		println!("\x1b[1;31merror\x1b[m\x1b[1;1m: {}\x1b[m", e);
		println!("\x1b[1;34m{}-->\x1b[m {} {}", margin, file, span);
		print!(
			"{}",
			pp.render(buffer.iter_from(viewport.start()), viewport, metrics)?
		);

		for note in i.notes.into_iter() {
			for (n, line) in note.lines().enumerate() {
				if n == 0 {
					println!("\x1b[1;34m{} = \x1b[m{}", margin, line);
				} else {
					println!("\x1b[1;34m{}   \x1b[m{}", margin, line);
				}
			}
		}

		Ok(())
	}

	pub fn print<
		T: Informative + fmt::Display,
		F: fmt::Display,
		E,
		B: Iterator<Item = result::Result<char, E>>,
		M: Metrics,
	>(
		e: Located<T>,
		file: F,
		buffer: &SourceBuffer<E, B, M>,
		viewport: Span,
		metrics: &M,
	) -> result::Result<(), E> {
		let span = e.span();
		Self::print_at(e.as_ref(), file, buffer, viewport, span, metrics)
	}
}

pub trait Informative {
	fn informations(&self, i: &mut Infos);
}

pub enum Error<E: Environment> {
	UnknownLogic,
	InvalidSymbol(syntax::Symbol),
	InvalidIdent(syntax::Ident),
	UnknownSort,
	UnknownFunction(E::Ident),
	UndefinedVariable(E::Ident),
	NegativeArity,
	WrongNumberOfArguments(usize, usize, usize), // (expected_min, expected_max, given).
	Type(typing::Error<E::Sort>),
}

impl<E: Environment> Error<E> {
	pub fn at(self, location: Span) -> Located<Error<E>> {
		Located::new(self, location)
	}
}

impl<E: Environment> From<Located<typing::Error<E::Sort>>> for Located<Error<E>> {
	fn from(e: Located<typing::Error<E::Sort>>) -> Located<Error<E>> {
		let span = e.span();
		Located::new(Error::Type(e.into_inner()), span)
	}
}

pub type Result<T, E> = result::Result<T, Located<Error<E>>>;

impl<E: Environment> fmt::Display for Error<E>
where
	E::Sort: fmt::Display,
	E::Ident: fmt::Display,
{
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
					write!(
						f,
						"wrong number of arguments (expected {}, given {})",
						min, given
					)
				} else {
					if given < min {
						write!(
							f,
							"wrong number of arguments (expected at least {}, given {})",
							min, given
						)
					} else {
						write!(
							f,
							"wrong number of arguments (expected at most {}, given {})",
							max, given
						)
					}
				}
			}
			Type(e) => write!(f, "{}", e),
		}
	}
}

impl<E: Environment> Informative for Error<E>
where
	E::Sort: fmt::Display,
	E::Ident: fmt::Display,
{
	fn informations(&self, i: &mut Infos) {
		use self::Error::*;
		match self {
			Type(e) => e.informations(i),
			_ => (),
		}
	}
}
