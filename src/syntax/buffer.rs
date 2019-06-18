use std::cell::{RefCell, RefMut};
use std::io::{Read, Bytes};
use std::ops::{Deref, DerefMut};
use std::fmt;

use crate::{Location, Cursor};

/// Lexer buffer, containing everything the lexer has already read.
/// The text is orginezd line by line.
/// It can be used to format the text and display error messages.
pub struct Buffer<I: Iterator<Item=char>> {
	p: RefCell<Inner<I>>
}

#[derive(Clone)]
pub struct Line(Vec<char>);

impl Deref for Line {
	type Target = Vec<char>;

	fn deref(&self) -> &Vec<char> {
		&self.0
	}
}

impl DerefMut for Line {
	fn deref_mut(&mut self) -> &mut Vec<char> {
		&mut self.0
	}
}

impl fmt::Display for Line {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		for c in self.0.iter() {
			c.fmt(f)?;
		}

		Ok(())
	}
}

struct Inner<I: Iterator<Item=char>> {
	input: I,
	is_complete: bool,
	lines: Vec<Line>,
	start: Cursor,
	end: Cursor
}

impl<I: Iterator<Item=char>> Inner<I> {
	fn read_line(&mut self) -> bool {
		let mut eof = true;
		loop {
			match self.input.next() {
				Some(c) => {
					eof = false;
					self.lines.last_mut().unwrap().push(c);
					if c == '\n' {
						self.lines.push(Line(Vec::new()));
						self.end = Cursor::new(self.end.line+1, 0);
						return true
					}
				},
				_ => {
					if eof {
						return false
					} else {
						self.end = Cursor::new(self.end.line, self.lines.last().unwrap().len());
						return true
					}
				}
			}
		}
	}

	/// Get the char at the given position.
	/// Return the target char is it exists along with the next
	/// cursor position.
	pub fn get(&mut self, pos: Cursor) -> Option<(char, Cursor)> {
		if pos < self.start {
			None
		} else {
			while pos >= self.end && self.read_line() {}

			if pos >= self.end {
				None
			} else {
				let i = pos.line - self.start.line;
				let line = &self.lines[i];
				if pos.column >= line.len() {
					// println!("line: {}, col: {}, len: {}", i, pos.column, line.len());
					None
				} else {
					let c = line[pos.column];
					let next_pos = if c == '\n' {
						Cursor::new(pos.line+1, 0)
					} else {
						Cursor::new(pos.line, pos.column+1)
					};
					Some((c, next_pos))
				}
			}
		}
	}
}

impl<I: Iterator<Item=char>> Buffer<I> {
	/// Create a new empty buffer.
	pub fn new(input: I, cursor: Cursor) -> Buffer<I> {
		let first_line = Line(Vec::new());

		Buffer {
			p: RefCell::new(Inner {
				input: input,
				is_complete: false,
				lines: vec![first_line],
				start: cursor,
				end: cursor
			})
		}
	}

	/// Get the char at the given position.
	/// Return the target char is it exists along with the next
	/// cursor position.
	pub fn get(&self, pos: Cursor) -> Option<(char, Cursor)> {
		self.p.borrow_mut().get(pos)
	}

	pub fn reader(&self) -> BufferReader<I> {
		BufferReader {
			buffer: &self,
			pos: self.p.borrow().start
		}
	}

	pub fn lines<F: Clone>(&self, loc: &Location<F>) -> Option<BufferFragment<I>> {
		match loc {
			Location::Nowhere => None,
			Location::Somewhere { start, end, .. } => {
				let p = self.p.borrow_mut();

				let start_line = if start.line >= p.start.line {
					start.line - p.start.line
				} else {
					0
				};

				let end_line = if end.line >= p.start.line {
					std::cmp::min(end.line - p.start.line, p.lines.len())
				} else {
					0
				};

				if start_line < p.lines.len() && end_line >= start_line {
					let start_col = if start_line == start.line {
						start.column
					} else {
						0
					};

					let end_col = if end_line == end.line {
						end.column
					} else {
						p.lines[end_line].len()
					};

					let sub_lines = &p.lines[start_line..end_line];

					Some(BufferFragment {
						buffer: p,
						pos: Cursor::new(start_line, start_col),
						end: Cursor::new(end_line, end_col)
					})
				} else {
					None
				}
			}
		}
	}
}

pub struct BufferReader<'b, I: 'b + Iterator<Item=char>> {
	buffer: &'b Buffer<I>,
	pos: Cursor
}

impl<'b, I: 'b + Iterator<Item=char>> Iterator for BufferReader<'b, I> {
	type Item = char;

	fn next(&mut self) -> Option<char> {
		match self.buffer.get(self.pos) {
			Some((c, next_pos)) => {
				self.pos = next_pos;
				Some(c)
			},
			None => None
		}
	}
}

pub struct BufferFragment<'b, I: 'b + Iterator<Item=char>> {
	buffer: RefMut<'b, Inner<I>>,
	pos: Cursor,
	end: Cursor
}

impl<'b, I: 'b + Iterator<Item=char>> Iterator for BufferFragment<'b, I> {
	type Item = (Cursor, Line);

	fn next(&mut self) -> Option<(Self::Item)> {
		if self.pos < self.end {
			let line = self.buffer.lines[self.pos.line].clone();
			let item = (self.pos, line);
			self.pos = Cursor::new(self.pos.line + 1, 0); // move to the next line.
			Some(item)
		} else {
			None
		}
	}
}
