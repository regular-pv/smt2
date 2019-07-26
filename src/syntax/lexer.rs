use std::io;
use std::iter::Peekable;
use source_span::{Position, Span};
use crate::Located;
use super::{token, Token, Result, Error};

pub struct Lexer<R: Iterator<Item=io::Result<char>>> {
	decoder: Peekable<R>,
	location: Span
}

fn is_separator(c: char) -> bool {
	c == '.' || c == ';' || c == ':' || c == '(' || c == ')' || c == '{' || c == '}' || c == '[' || c == ']' || c == ','
}

impl<R: Iterator<Item = io::Result<char>>> Lexer<R> {
	pub fn new(source: R, cursor: Position) -> Lexer<R> {
		Lexer {
			decoder: source.peekable(),
			location: cursor.into(),
			//buffer: Buffer::new(cursor)
		}
	}

	pub fn location(&self) -> Span {
		self.location
	}

	/**
	 * Update the lexer location.
	 */
	pub fn set_location(&mut self, location: Span) {
		self.location = location
	}

	fn peek_char(&mut self) -> Result<Option<char>> {
		match self.decoder.peek() {
			Some(Ok(c)) => {
				// eprintln!("peeking: {}", c);
				Ok(Some(*c))
			},
			Some(Err(_)) => {
				Ok(Some(self.consume()?)) // this will always fail.
			},
			None => Ok(None)
		}
	}

	fn consume(&mut self) -> Result<char> {
		match self.decoder.next() {
			Some(Ok(c)) => {
				self.location.push(c);
				Ok(c)
			},
			Some(Err(e)) => {
				self.location.clear();
				Err(Error::IO(e).at(self.location.clone()))
			},
			None => {
				self.location.clear();
				Err(Error::IO(std::io::Error::new(std::io::ErrorKind::UnexpectedEof, "unexpected enf of stream")).at(self.location.clone()))
			}
		}
	}

	fn skip_whitespaces(&mut self) -> Result<()> {
		loop {
			match self.peek_char()? {
				Some(';') => self.skip_line()?,
				Some('\n') => {
					self.consume()?;
				}
				Some(c) if c.is_whitespace() => {
					self.consume()?;
				},
				_ => break
			}
		}

		Ok(())
	}

	/**
	 * Skip all chars until the next line break.
	 */
	fn skip_line(&mut self) -> Result<()> {
		loop {
			match self.peek_char()? {
				Some('\n') => {
					self.consume()?;
					break
				}
				_ => {
					self.consume()?;
				}
			}
		}

		Ok(())
	}

	fn read_ident(&mut self) -> Result<Located<Token>> {
		let mut name = String::new();
		name.push(self.consume()?);

		loop {
			match self.peek_char()? {
				Some(c) if !c.is_whitespace() && !is_separator(c) => {
					name.push(self.consume()?);
				},
				_ => break
			}
		}

		let location = self.location;
		self.location.clear();

		Ok(Token::Ident(name.to_string()).at(location))
	}

	fn read_string(&mut self) -> Result<Located<Token>> {
		let mut string = String::new();

		let mut escape = false;
		loop {
			if escape {
				match self.consume()? {
					'n' => string.push('\n'),
					c => string.push(c)
				}
				escape = false;
			} else {
				match self.consume()? {
					'\\' => {
						escape = true;
					},
					'"' => {
						break
					},
					c => {
						string.push(c)
					}
				}
			}
		}

		let location = self.location;
		self.location.clear();

		Ok(Token::Litteral(token::Litteral::String(string)).at(location))
	}

	// fn read_numeric(&mut self, radix: u32, positive: bool) -> Result<Located<Token>> {
	// 	let mut value = 0;
	// 	let f = radix as i64;
	//
	// 	loop {
	// 		match self.peek_char()? {
	// 			Some(c) if c.is_digit(radix) => {
	// 				self.consume()?;
	// 				value = value * f + c.to_digit(radix).unwrap() as i64;
	// 			},
	// 			_ => break
	// 		}
	// 	}
	//
	// 	if !positive {
	// 		value = -value;
	// 	}
	//
	// 	let location = self.location;
	// 	self.location.clear();
	//
	// 	Ok(Token::Litteral(token::Litteral::Int(value)).at(location))
	// }

	fn read_token(&mut self) -> Result<Option<Located<Token>>> {
		self.skip_whitespaces()?;
		self.location.clear();
		match self.peek_char()? {
			Some(c) => {
				match c {
					'(' => {
						self.consume()?;
						let location = self.location;
						self.location.clear();
						Ok(Some(Token::Begin.at(location)))
					},

					')' => {
						self.consume()?;
						let location = self.location;
						self.location.clear();
						Ok(Some(Token::End.at(location)))
					},

					'"' => {
						self.consume()?;
						Ok(Some(self.read_string()?))
					}

					// '-' => {
					// 	self.consume()?;
					// 	match self.peek_char()? {
					// 		Some(c) if c.is_digit(10) => {
					// 			Ok(Some(self.read_numeric(10, false)?))
					// 		},
					// 		_ => { // the ident "-"
					// 			let location = self.location.clone();
					// 			self.location.clear();
					// 			Ok(Some(Token::Ident("-".to_string()).at(location)))
					// 		}
					// 	}
					// },

					// c if c.is_digit(10) => {
					// 	Ok(Some(self.read_numeric(10, true)?))
					// },

					_ => {
						Ok(Some(self.read_ident()?))
					}
				}
			},
			None => Ok(None)
		}
	}
}

impl<R: Iterator<Item = io::Result<char>>> Iterator for Lexer<R> {
	type Item = Result<Located<Token>>;

	fn next(&mut self) -> Option<Result<Located<Token>>> {
		self.read_token().transpose()
	}
}
