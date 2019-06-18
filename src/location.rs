use std::cmp::Ordering;
use std::ops::Deref;
use std::fmt;

use std::result::Result;

#[derive(Clone, Copy, PartialEq, Eq)]
#[derive(Debug)]
pub struct Cursor {
	pub line: usize,
	pub column: usize
}

impl Cursor {
	pub fn new(line: usize, col: usize) -> Cursor {
		Cursor {
			line: line,
			column: col
		}
	}

	/// Gives the magnitude order of the line number (rounded log10 of the line number).
	/// This is usefull when formatting line numbers.
	pub fn order(&self) -> usize {
		((self.line+1) as f32).log10().floor() as usize
	}
}

impl PartialOrd for Cursor {
	fn partial_cmp(&self, other: &Cursor) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Cursor {
	fn cmp(&self, other: &Cursor) -> Ordering {
        match self.line.cmp(&other.line) {
			Ordering::Equal => self.column.cmp(&other.column),
			ordering => ordering
		}
    }
}

impl Default for Cursor {
	fn default() -> Cursor {
		Cursor {
			line: 0,
			column: 0
		}
	}
}

impl fmt::Display for Cursor {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}:{}", self.line+1, self.column+1)
    }
}

#[derive(Clone)]
#[derive(Debug)]
pub enum Location<File: Clone> {
	Nowhere,
	Somewhere {
		file: File,
		start: Cursor,
		end: Cursor
	}
}

impl<File: Clone> Location<File> {
	pub fn new(file: File, start: Cursor, end: Cursor) -> Location<File> {
		Location::Somewhere {
			file: file,
			start: start,
			end: end
		}
	}

	pub fn from_file(file: File) -> Location<File> {
		Location::Somewhere {
			file: file,
			start: Cursor::default(),
			end: Cursor::default()
		}
	}

	pub fn nowhere() -> Location<File> {
		Location::Nowhere
	}

	pub fn move_forward(&mut self) {
		match self {
			Location::Somewhere { ref mut end, .. } => end.column += 1,
			_ => ()
		}
	}

	pub fn new_line(&mut self) {
		match self {
			Location::Somewhere { ref mut end, .. } => {
				*end = Cursor {
					line: end.line + 1,
					column: 0
				}
			},
			_ => ()
		}
	}

	pub fn next(&mut self) {
		match self {
			Location::Somewhere { ref mut start, ref end, .. } => *start = *end,
			_ => ()
		}
	}

	pub fn union(&self, other: &Location<File>) -> Location<File> {
		match self {
			Location::Somewhere { ref file, ref start, .. } => {
				match other {
					Location::Somewhere { ref end, .. } => {
						Location::Somewhere {
							file: file.clone(),
							start: *start,
							end: *end
						}
					},
					_ => self.clone()
				}
			},
			_ => other.clone()
		}
	}

	pub fn includes(&self, pos: Cursor) -> bool {
		match self {
			Location::Somewhere { ref start, ref end, .. } => {
				*start <= pos && pos <= *end
			},
			_ => false
		}
	}

	/// Gives the magnitude order of the line number,
	/// which is the order of the last line of the location.
	/// Or 0 is the location is Nowhere.
	pub fn order(&self) -> usize {
		match self {
			Location::Somewhere { end, .. } => end.order(),
			_ => 0
		}
	}
}

impl<File: Clone + Default> Default for Location<File> {
	fn default() -> Location<File> {
		Location::Somewhere {
			file: File::default(),
			start: Cursor::default(),
			end: Cursor::default()
		}
	}
}

impl<File: Clone + fmt::Display> fmt::Display for Location<File> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match self {
			Location::Somewhere { file, start, end } => {
				write!(f, "{}: {} to {}", file, start, end)
			},
			Location::Nowhere => {
				write!(f, "<nowhere>")
			}
		}

    }
}

pub trait Localisable<File: Clone> {
	fn location(&self) -> &Location<File>;

	// /**
	//  * Return the same object but a some location.
	//  */
	// fn at(&self, location: Location<File>) -> Self;
}

impl<F: Clone, T: Localisable<F>, E: Localisable<F>> Localisable<F> for Result<T, E> {
	fn location(&self) -> &Location<F> {
		match self {
			Err(e) => e.location(),
			Ok(v) => v.location()
		}
	}

	// fn at(&self, location: Location<F>) -> Self {
	// 	match self {
	// 		Err(e) => Err(e.at(location)),
	// 		Ok(v) => Ok(v.at(location))
	// 	}
	// }
}

/**
 * Wrap a value to give it a location.
 */
pub struct Located<T, F: Clone> {
	t: T,
	location: Location<F>
}

impl<T, F: Clone> Deref for Located<T, F> {
	type Target = T;

	fn deref(&self) -> &T {
		&self.t
	}
}

impl<T, F: Clone> Located<T, F> {
	pub fn new(t: T, loc: Location<F>) -> Located<T, F> {
		Located {
			t: t,
			location: loc
		}
	}

	pub fn into_inner(self) -> T {
		self.t
	}
}

impl<T, F: Clone> Localisable<F> for Located<T, F> {
	fn location(&self) -> &Location<F> {
		&self.location
	}

	// fn at(&self, location: Location<F>) -> Self {
	// 	Location::
	// }
}

impl<T: fmt::Display, F: Clone> fmt::Display for Located<T, F> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self.t.fmt(f)
    }
}

impl<T: Clone, F: Clone> Clone for Located<T, F> {
	fn clone(&self) -> Self {
		Located {
			t: self.t.clone(),
			location: self.location.clone()
		}
	}
}

impl<T, F: Clone> AsRef<T> for Located<T, F> {
	fn as_ref(&self) -> &T {
		&self.t
	}
}

impl<T, F: Clone> AsMut<T> for Located<T, F> {
	fn as_mut(&mut self) -> &mut T {
		&mut self.t
	}
}
