use source_span::Span;
/**
 * SMT2-lib syntax.
 */
use std::iter::Peekable;

pub use crate::location::*;

pub mod ast;
pub mod display;
pub mod error;
pub mod lexer;
pub mod response;
pub mod token;

pub use ast::*;
pub use display::{Display, Formatter, PrettyPrint};
pub use error::*;
pub use lexer::Lexer;
pub use token::Token;

pub trait Parsable: Sized {
	/**
	 * Parse from a lexer.
	 * Separators are handled depending on the flavor parameter.
	 */
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Self>>
	where
		L: Iterator<Item = Result<Located<Token>>>;
}

/**
 * Peek the next token from a lexer.
 */
pub(crate) fn peek<L>(lexer: &mut Peekable<L>) -> Result<Located<Token>>
where
	L: Iterator<Item = Result<Located<Token>>>,
{
	match lexer.peek() {
		Some(Ok(token)) => Ok(token.clone()),
		None => Ok(Token::EndOfFile.at(Span::default())),
		Some(Err(_)) => consume(lexer),
	}
}

/**
 * Consume the next token from a lexer.
 */
pub(crate) fn consume<L>(lexer: &mut Peekable<L>) -> Result<Located<Token>>
where
	L: Iterator<Item = Result<Located<Token>>>,
{
	match lexer.next() {
		Some(Ok(token)) => Ok(token.clone()),
		None => Ok(Token::EndOfFile.at(Span::default())),
		Some(Err(error)) => Err(error),
	}
}

/**
 * Consume the next token and ensure it is of the given kind.
 */
pub(crate) fn consume_token<L>(lexer: &mut Peekable<L>, kind: Token) -> Result<Span>
where
	L: Iterator<Item = Result<Located<Token>>>,
{
	let token = consume(lexer)?;
	if *token == kind {
		Ok(token.span())
	} else {
		Err(Error::UnexpectedToken(token.clone().into_inner(), Some(kind)).at(token.span()))
	}
}

pub(crate) fn parse_list<L, T: Parsable>(
	lexer: &mut Peekable<L>,
	loc: &mut Span,
) -> Result<Vec<Located<T>>>
where
	L: Iterator<Item = Result<Located<Token>>>,
{
	use Token::*;
	let mut list = Vec::new();

	loop {
		let token = peek(lexer)?;
		match *token {
			End => {
				//println!("LIST end");
				consume(lexer)?;
				*loc = loc.union(token.span());
				break;
			}
			_ => {
				//println!("LIST parse");
				let t = T::parse(lexer)?;
				list.push(t);
			}
		}
	}

	Ok(list)
}

// impl Parsable for Constant {
//	 fn parse<L>(lexer: &mut Peekable<L>) -> Result<Constant> where L: Iterator<Item=Result<Located<Token>>> {
//		 use Token::*;
//		 let token = consume(lexer)?;
//		 let loc = token.span();
//		 match *token {
//			 Litteral(token::Litteral::Int(i)) => Ok(Constant::Int(i)),
//			 unexpected => Err(Error::UnexpectedToken(unexpected, None).at(loc))
//		 }
//	 }
// }

impl Parsable for Symbol {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Symbol>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let token = consume(lexer)?;
		let loc = token.span();
		match token.into_inner() {
			Ident(name) => Ok(Located::new(Symbol { id: name.clone() }, loc)),
			unexpected => Err(Error::UnexpectedToken(unexpected, None).at(loc)),
		}
	}
}

impl Parsable for Index {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Index>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		let token = peek(lexer)?;
		let loc = token.span();

		use Token::*;
		let kind = match token.into_inner() {
			// Litteral(token::Litteral::Int(i)) => {
			//	 consume(lexer)?;
			//	 IndexKind::Numeral(i)
			// },
			Ident(_) => {
				let symbol = Symbol::parse(lexer)?;
				Index::Symbol(symbol.into_inner())
			}
			unexpected => return Err(Error::UnexpectedToken(unexpected, None).at(loc)),
		};

		Ok(Located::new(kind, loc))
	}
}

impl Parsable for Ident {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Ident>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let token = peek(lexer)?;
		let mut loc = token.span();

		match token.into_inner() {
			Begin => {
				consume(lexer)?;
				consume_token(lexer, Ident("_".to_string()))?;
				let id = Symbol::parse(lexer)?;
				let mut indexes = Vec::new();

				loop {
					let token = peek(lexer)?;
					match token.as_ref() {
						End => {
							consume(lexer)?;
							loc = loc.union(token.span());
							break;
						}
						_ => {
							let index = Index::parse(lexer)?;
							indexes.push(index);
						}
					}
				}

				Ok(Located::new(
					ast::Ident {
						id: id,
						indexes: indexes,
					},
					loc,
				))
			}
			Ident(_) => {
				let id = Symbol::parse(lexer)?;
				Ok(Located::new(
					ast::Ident {
						id: id,
						indexes: Vec::new(),
					},
					loc,
				))
			}
			unexpected => return Err(Error::UnexpectedToken(unexpected, None).at(loc)),
		}
	}
}

impl Parsable for Keyword {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Keyword>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let token = consume(lexer)?;
		let loc = token.span();
		match token.into_inner() {
			Ident(name) => Ok(Located::new(Keyword { id: name.clone() }, loc)),
			unexpected => Err(Error::UnexpectedToken(unexpected, None).at(loc)),
		}
	}
}

impl Parsable for Attribute {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Attribute>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		let key = Keyword::parse(lexer)?;
		let token = peek(lexer)?;
		use Token::*;

		let value = match token.as_ref() {
			Ident(name) => match name.chars().next() {
				Some(':') => None,
				Some(_) => Some(AttributeValue::parse(lexer)?),
				_ => None,
			},
			Litteral(_) => Some(AttributeValue::parse(lexer)?),
			Begin => Some(AttributeValue::parse(lexer)?),
			_ => None,
		};

		let loc = match value {
			Some(ref value) => key.span().union(value.span()),
			None => key.span(),
		};

		Ok(Located::new(
			Attribute {
				key: key,
				value: value,
			},
			loc,
		))
	}
}

impl Parsable for AttributeValue {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<AttributeValue>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		let token = peek(lexer)?;
		let mut loc = token.span();

		use Token::*;
		let kind = match token.as_ref() {
			Ident(_) => {
				let id = ast::Symbol::parse(lexer)?;
				AttributeValue::Sym(id)
			}

			// Litteral(_) => {
			//	 let c = Constant::parse(lexer)?;
			//	 AttributeValueKind::Const(c)
			// },
			Begin => {
				consume(lexer)?;
				let mut exprs = Vec::new();

				loop {
					let token = peek(lexer)?;
					match token.as_ref() {
						End => {
							consume(lexer)?;
							loc = loc.union(token.span());
							break;
						}
						_ => {
							let expr = SExpr::parse(lexer)?;
							exprs.push(expr);
						}
					}
				}

				AttributeValue::List(exprs)
			}

			unexpected => {
				consume(lexer)?;
				return Err(Error::UnexpectedToken(unexpected.clone(), None).at(loc));
			}
		};

		Ok(Located::new(kind, loc))
	}
}

impl Parsable for SExpr {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<SExpr>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		let token = peek(lexer)?;
		let mut loc = token.span();

		use Token::*;
		let kind = match token.as_ref() {
			Ident(name) => match name.chars().next() {
				Some(':') => {
					let key = Keyword::parse(lexer)?;
					SExpr::Keyword(key)
				}
				_ => {
					let id = ast::Symbol::parse(lexer)?;
					SExpr::Sym(id)
				}
			},

			// Litteral(_) => {
			//	 let c = Constant::parse(lexer)?;
			//	 SExprKind::Const(c)
			// },
			Begin => {
				consume(lexer)?;
				let mut exprs = Vec::new();

				loop {
					let token = peek(lexer)?;
					match token.as_ref() {
						End => {
							consume(lexer)?;
							loc = loc.union(token.span());
							break;
						}
						_ => {
							let expr = SExpr::parse(lexer)?;
							exprs.push(expr);
						}
					}
				}

				SExpr::List(exprs)
			}

			unexpected => {
				consume(lexer)?;
				return Err(Error::UnexpectedToken(unexpected.clone(), None).at(loc));
			}
		};

		Ok(Located::new(kind, loc))
	}
}

impl Parsable for Sort {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Sort>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let token = peek(lexer)?;
		let mut loc = token.span();

		match token.as_ref() {
			Ident(_) => {
				let id = ast::Ident::parse(lexer)?;

				Ok(Located::new(
					Sort {
						id: id,
						parameters: Vec::new(),
					},
					loc,
				))
			}
			Begin => {
				consume(lexer)?;
				let id = ast::Ident::parse(lexer)?;
				let mut parameters = Vec::new();

				loop {
					let token = peek(lexer)?;
					match *token {
						End => {
							consume(lexer)?;
							loc = loc.union(token.span());
							break;
						}
						_ => {
							let param = Sort::parse(lexer)?;
							parameters.push(param);
						}
					}
				}

				Ok(Located::new(
					Sort {
						id: id,
						parameters: parameters,
					},
					loc,
				))
			}
			unexpected => Err(Error::UnexpectedToken(unexpected.clone(), None).at(loc)),
		}
	}
}

impl Parsable for Term {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Term>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let token = peek(lexer)?;
		let mut loc = token.span();

		let kind = match token.as_ref() {
			Begin => {
				consume(lexer)?;
				let token = peek(lexer)?;

				match token.as_ref() {
					Ident(name) => {
						match name.as_str() {
							"let" => {
								consume(lexer)?;
								consume_token(lexer, Begin)?; // begining of the bindings list
								let bindings = parse_list(lexer, &mut loc)?;
								let body = Term::parse(lexer)?;
								consume_token(lexer, End)?; // end of the term.

								Term::Let {
									bindings: bindings,
									body: Box::new(body),
								}
							}

							"forall" => {
								consume(lexer)?;
								consume_token(lexer, Begin)?; // begining of the vars list
								let vars = parse_list(lexer, &mut loc)?;
								let body = Term::parse(lexer)?;
								consume_token(lexer, End)?; // end of the term.

								Term::Forall {
									vars: vars,
									body: Box::new(body),
								}
							}

							"exists" => {
								consume(lexer)?;
								consume_token(lexer, Begin)?; // begining of the vars list
								let vars = parse_list(lexer, &mut loc)?;
								let body = Term::parse(lexer)?;
								consume_token(lexer, End)?; // end of the term.

								Term::Exists {
									vars: vars,
									body: Box::new(body),
								}
							}

							"as" => {
								consume(lexer)?;
								let term = Term::parse(lexer)?;
								let sort = Sort::parse(lexer)?;
								consume_token(lexer, End)?; // end of the term.

								Term::Coerce {
									term: Box::new(term),
									sort: sort,
								}
							}

							_ => {
								let id = ast::Ident::parse(lexer)?;
								//println!("APPLY list");
								let args = parse_list(lexer, &mut loc)?;
								//println!("APPLY done");

								Term::Apply {
									id: id,
									args: Box::new(args),
								}
							}
						}
					}

					unexpected => {
						return Err(Error::UnexpectedToken(unexpected.clone(), None).at(loc))
					}
				}
			}

			// Litteral(_) => {
			//	 let c = Constant::parse(lexer)?;
			//	 TermKind::Const(c)
			// },
			_ => {
				let id = ast::Ident::parse(lexer)?;
				Term::Ident(id)
			}
		};

		Ok(Located::new(kind, loc))
	}
}

impl Parsable for Binding {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Binding>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let mut loc = consume_token(lexer, Begin)?;
		let id = Symbol::parse(lexer)?;
		let term = Term::parse(lexer)?;
		loc = loc.union(consume_token(lexer, End)?);

		Ok(Located::new(
			Binding {
				id: id,
				value: Box::new(term),
			},
			loc,
		))
	}
}

impl Parsable for SortedVar {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<SortedVar>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let mut loc = consume_token(lexer, Begin)?;
		let id = Symbol::parse(lexer)?;
		let sort = Sort::parse(lexer)?;
		loc = loc.union(consume_token(lexer, End)?);

		Ok(Located::new(SortedVar { id: id, sort: sort }, loc))
	}
}

impl Parsable for DataTypeDeclaration {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<DataTypeDeclaration>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let constructors;
		let parameters;
		let mut loc = consume_token(lexer, Begin)?;

		let next_token = peek(lexer)?;
		match *next_token {
			Ident(ref id) if id == "par" => {
				consume(lexer)?;
				consume_token(lexer, Begin)?;
				parameters = parse_list(lexer, &mut loc)?;
				consume_token(lexer, Begin)?;
				constructors = parse_list(lexer, &mut loc)?;
				loc = loc.union(consume_token(lexer, End)?);
			}
			_ => {
				parameters = Vec::new();
				constructors = parse_list(lexer, &mut loc)?;
			}
		}

		Ok(Located::new(
			DataTypeDeclaration {
				parameters: parameters,
				constructors: constructors,
			},
			loc,
		))
	}
}

impl Parsable for ConstructorDeclaration {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<ConstructorDeclaration>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let mut loc = consume_token(lexer, Begin)?;
		let id = Symbol::parse(lexer)?;
		let selectors = parse_list(lexer, &mut loc)?;

		Ok(Located::new(
			ConstructorDeclaration {
				id: id,
				selectors: selectors,
			},
			loc,
		))
	}
}

impl Parsable for SelectorDeclaration {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<SelectorDeclaration>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let mut loc = consume_token(lexer, Begin)?;
		let id = Symbol::parse(lexer)?;
		let sort = Sort::parse(lexer)?;
		loc = loc.union(consume_token(lexer, End)?);

		Ok(Located::new(
			SelectorDeclaration { id: id, sort: sort },
			loc,
		))
	}
}

fn parse_numeral<L>(lexer: &mut Peekable<L>) -> Result<Located<i64>>
where
	L: Iterator<Item = Result<Located<Token>>>,
{
	use Token::*;
	let token = consume(lexer)?;
	let loc = token.span();

	match token.as_ref() {
		Ident(id) => {
			if let Ok(i) = i64::from_str_radix(id, 10) {
				Ok(Located::new(i, loc))
			} else {
				Err(Error::UnexpectedToken(Ident(id.clone()), None).at(loc))
			}
		}
		unexpected => Err(Error::UnexpectedToken(unexpected.clone(), None).at(loc)),
	}
}

impl Parsable for SortDeclaration {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<SortDeclaration>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let mut loc = consume_token(lexer, Begin)?;
		let id = Symbol::parse(lexer)?;
		let arity = parse_numeral(lexer)?;
		loc = loc.union(consume_token(lexer, End)?);

		Ok(Located::new(
			SortDeclaration {
				id: id,
				arity: arity,
			},
			loc,
		))
	}
}

impl Parsable for Command {
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Command>>
	where
		L: Iterator<Item = Result<Located<Token>>>,
	{
		use Token::*;
		let mut loc = consume_token(lexer, Begin)?;

		let token = consume(lexer)?;
		let name_loc = token.span();
		let kind = match token.as_ref() {
			Ident(ref name) => match name.as_str() {
				"assert" => {
					let term = Term::parse(lexer)?;
					Command::Assert(term)
				}

				"check-sat" => Command::CheckSat,

				"declare-const" => {
					let id = Symbol::parse(lexer)?;
					let sort = Sort::parse(lexer)?;
					Command::DeclareConst(id, sort)
				}

				"declare-datatype" => {
					let id = Symbol::parse(lexer)?;
					let decl = DataTypeDeclaration::parse(lexer)?;
					Command::DeclareDatatype(id, decl)
				}

				"declare-datatypes" => {
					consume_token(lexer, Begin)?;
					let sort_decls = parse_list(lexer, &mut loc)?;
					consume_token(lexer, Begin)?;
					let decls = parse_list(lexer, &mut loc)?;
					Command::DeclareDatatypes(sort_decls, decls)
				}

				"declare-fun" => {
					let id = Symbol::parse(lexer)?;
					consume_token(lexer, Begin)?;
					let args = parse_list(lexer, &mut loc)?;
					let return_sort = Sort::parse(lexer)?;
					Command::DeclareFun(id, args, return_sort)
				}

				"exit" => Command::Exit,

				"get-model" => Command::GetModel,

				"set-info" => {
					let attr = Attribute::parse(lexer)?;
					Command::SetInfo(attr)
				}

				"set-logic" => {
					let logic = Symbol::parse(lexer)?;
					Command::SetLogic(logic)
				}

				_ => return Err(Error::UnknownCommand(name.clone()).at(name_loc)),
			},

			unexpected => return Err(Error::UnexpectedToken(unexpected.clone(), None).at(name_loc)),
		};

		loc = loc.union(consume_token(lexer, End)?);

		Ok(Located::new(kind, loc))
	}
}
