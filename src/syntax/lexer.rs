use std::io;
use std::iter::Peekable;
use super::{Cursor, Location};
use super::{utf8, token, Token, Result};

pub struct Decoder<R: Iterator<Item=io::Result<u8>>> {
	bytes: R
}

impl<R: Iterator<Item=io::Result<u8>>> Decoder<R> {
	pub fn new(source: R) -> Decoder<R> {
		Decoder {
			bytes: source
		}
	}
}

impl<R: Iterator<Item=io::Result<u8>>> Iterator for Decoder<R> {
	type Item = char;

	fn next(&mut self) -> Option<char> {
		match utf8::decode(&mut self.bytes) {
			Some(c) => Some(c.expect("invalid utf8 sequence")),
			None => None
		}
	}
}

pub struct Lexer<R: Iterator<Item=char>, F: Clone> {
	decoder: Peekable<R>,
	location: Location<F>
}

fn is_separator(c: char) -> bool {
	c == '.' || c == ';' || c == ':' || c == '(' || c == ')' || c == '{' || c == '}' || c == '[' || c == ']'
}

impl<R: Iterator<Item=char>, F: Clone> Lexer<R, F> {
	pub fn new(source: R, file: F, cursor: Cursor) -> Lexer<R, F> {
		Lexer {
			decoder: source.peekable(),
			location: Location::new(file, cursor, cursor),
			//buffer: Buffer::new(cursor)
		}
	}

	pub fn location(&self) -> &Location<F> {
		&self.location
	}

	/**
	 * Update the lexer location.
	 */
	pub fn set_location(&mut self, location: Location<F>) {
		self.location = location
	}

	fn peek_char(&mut self) -> Option<char> {
		match self.decoder.peek() {
			Some(c) => {
				// eprintln!("peeking: {}", c);
				Some(*c)
			},
			None => None
		}
	}

	fn consume(&mut self) -> char {
		let c = self.decoder.next().unwrap();
		// eprintln!("consume: {}", c);
		match c {
			'\n' => {
				self.location.new_line();
			},
			c if !c.is_whitespace() => {
				self.location.move_forward();
			},
			_ => self.location.move_forward()
		}
		c
	}

	fn skip_whitespaces(&mut self) {
		loop {
			match self.peek_char() {
				Some(';') => self.skip_line(),
				Some('\n') => {
					self.consume();
				}
				Some(c) if c.is_whitespace() => {
					self.consume();
				},
				_ => break
			}
		}
	}

	/**
	 * Skip all chars until the next line break.
	 */
	fn skip_line(&mut self) {
		loop {
			match self.peek_char() {
				Some('\n') => {
					self.consume();
					break
				}
				_ => {
					self.consume();
				},
				_ => break
			}
		}
	}

	fn read_ident(&mut self) -> Result<Token<F>, F> {
		let mut name = String::new();
		name.push(self.consume());

		loop {
			match self.peek_char() {
				Some(c) if !c.is_whitespace() && !is_separator(c) => {
					name.push(self.consume());
				},
				_ => break
			}
		}

		let location = self.location.clone();
		self.location.next();

		Ok(Token {
			location: location,
			kind: token::Kind::Ident(name.to_string())
		})
	}

	fn read_numeric(&mut self, radix: u32, positive: bool) -> Result<Token<F>, F> {
		let mut value = 0;
		let f = radix as i64;

		loop {
			match self.peek_char() {
				Some(c) if c.is_digit(radix) => {
					self.consume();
					value = value * f + c.to_digit(radix).unwrap() as i64;
				},
				_ => break
			}
		}

		if !positive {
			value = -value;
		}

		let location = self.location.clone();
		self.location.next();

		Ok(Token {
			location: location,
			kind: token::Kind::Litteral(token::Litteral::Int(value))
		})
	}
}

impl<R: Iterator<Item=char>, F: Clone> Iterator for Lexer<R, F> {
	type Item = Result<Token<F>, F>;

	fn next(&mut self) -> Option<Result<Token<F>, F>> {
		self.skip_whitespaces();
		self.location.next();
		match self.peek_char() {
			Some(c) => {
				match c {
					'(' => {
						self.consume();
						let location = self.location.clone();
						self.location.next();
						Some(Ok(token::Kind::Begin.at(location)))
					},

					')' => {
						self.consume();
						let location = self.location.clone();
						self.location.next();
						Some(Ok(token::Kind::End.at(location)))
					},

					'-' => {
						self.consume();
						match self.peek_char() {
							Some(c) if c.is_digit(10) => {
								Some(self.read_numeric(10, false))
							},
							_ => { // the ident "-"
								let location = self.location.clone();
								self.location.next();
								Some(Ok(Token {
									location: location,
									kind: token::Kind::Ident("-".to_string())
								}))
							}
						}
					},

					c if c.is_digit(10) => {
						Some(self.read_numeric(10, true))
					},

					_ => {
						Some(self.read_ident())
					}
				}
			},
			None => None
		}
	}
}
