/**
 * SMT2-lib syntax.
 */

use std::iter::Peekable;

pub use crate::location::*;

pub mod error;
pub mod ast;
pub mod token;
pub mod utf8;
pub mod lexer;
pub mod buffer;
pub mod pp;
pub mod response;
pub mod display;

pub use error::*;
pub use ast::*;
pub use token::Token;
pub use lexer::Lexer;
pub use buffer::Buffer;
pub use pp::PrettyPrinter;
pub use display::{Display, Formatter, PrettyPrint};

pub trait Parsable<F: Clone> : Sized {
	/**
	 * Parse from a lexer.
	 * Separators are handled depending on the flavor parameter.
	 */
	fn parse<L>(lexer: &mut Peekable<L>) -> Result<Self, F> where L: Iterator<Item=Result<Token<F>, F>>;
}

/**
 * Peek the next token from a lexer.
 */
pub(crate) fn peek<L, F: Clone>(lexer: &mut Peekable<L>) -> Result<Token<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
	match lexer.peek() {
		Some(Ok(token)) => Ok(token.clone()),
		None => Ok(token::Kind::EndOfFile.at(Location::nowhere())),
		Some(Err(error)) => Err(error.clone())
	}
}

/**
 * Consume the next token from a lexer.
 */
pub(crate) fn consume<L, F: Clone>(lexer: &mut Peekable<L>) -> Result<Token<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
	match lexer.next() {
		Some(Ok(token)) => Ok(token.clone()),
		None => Ok(token::Kind::EndOfFile.at(Location::nowhere())),
		Some(Err(error)) => Err(error)
	}
}

/**
 * Consume the next token and ensure it is of the given kind.
 */
pub(crate) fn consume_token<L, F: Clone>(lexer: &mut Peekable<L>, kind: token::Kind) -> Result<Location<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
	let token = consume(lexer)?;
	if token.kind == kind {
		Ok(token.location().clone())
	} else {
		Err(error::Kind::UnexpectedToken(token.kind.clone(), Some(kind)).at(token.location.clone()))
	}
}

pub(crate) fn parse_list<L, T: Parsable<F>, F: Clone>(lexer: &mut Peekable<L>, loc: &mut Location<F>) -> Result<Vec<T>, F> where L: Iterator<Item=Result<Token<F>, F>> {
    use token::Kind::*;
    let mut list = Vec::new();

    loop {
        let token = peek(lexer)?;
        match token.kind {
            End => {
				//println!("LIST end");
                consume(lexer)?;
                *loc = loc.union(token.location());
                break;
            },
            _ => {
				//println!("LIST parse");
                let t = T::parse(lexer)?;
                list.push(t);
            }
        }
    }

    Ok(list)
}

// impl<F: Clone> Parsable<F> for Constant {
//     fn parse<L>(lexer: &mut Peekable<L>) -> Result<Constant, F> where L: Iterator<Item=Result<Token<F>, F>> {
//         use token::Kind::*;
//         let token = consume(lexer)?;
//         let loc = token.location().clone();
//         match token.kind {
//             Litteral(token::Litteral::Int(i)) => Ok(Constant::Int(i)),
//             unexpected => Err(error::Kind::UnexpectedToken(unexpected, None).at(loc))
//         }
//     }
// }

impl<F: Clone> Parsable<F> for Symbol<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Symbol<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
        let token = consume(lexer)?;
        let loc = token.location().clone();
        match token.kind {
            Ident(name) => Ok(Symbol {
                location: loc,
                id: name.clone()
            }),
            unexpected => Err(error::Kind::UnexpectedToken(unexpected, None).at(loc))
        }
    }
}

impl<F: Clone> Parsable<F> for Index<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Index<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        let token = peek(lexer)?;
        let loc = token.location().clone();

        use token::Kind::*;
        let kind = match token.kind {
            // Litteral(token::Litteral::Int(i)) => {
            //     consume(lexer)?;
            //     IndexKind::Numeral(i)
            // },
            Ident(_) => {
                let symbol = Symbol::<F>::parse(lexer)?;
                IndexKind::Symbol(symbol)
            }
            unexpected => return Err(error::Kind::UnexpectedToken(unexpected, None).at(loc))
        };

        Ok(Index {
            location: loc,
            kind: kind
        })
    }
}

impl<F: Clone> Parsable<F> for Ident<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Ident<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
        let token = peek(lexer)?;
        let mut loc = token.location().clone();

        match token.kind {
            Begin => {
                consume(lexer)?;
                consume_token(lexer, Ident("_".to_string()))?;
                let id = Symbol::<F>::parse(lexer)?;
                let mut indexes = Vec::new();

                loop {
                    let token = peek(lexer)?;
                    match token.kind {
                        End => {
                            consume(lexer)?;
                            loc = loc.union(token.location());
                            break;
                        },
                        _ => {
                            let index = Index::<F>::parse(lexer)?;
                            indexes.push(index);
                        }
                    }
                }

                Ok(ast::Ident {
                    location: loc,
                    id: id,
                    indexes: indexes
                })
            },
            Ident(_) => {
                let id = Symbol::<F>::parse(lexer)?;
                Ok(ast::Ident {
                    location: loc,
                    id: id,
                    indexes: Vec::new()
                })
            },
            unexpected => return Err(error::Kind::UnexpectedToken(unexpected, None).at(loc))
        }
    }
}

impl<F: Clone> Parsable<F> for Keyword<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Keyword<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
        let token = consume(lexer)?;
        let loc = token.location().clone();
        match token.kind {
            Ident(name) => Ok(Keyword {
                location: loc,
                id: name.clone()
            }),
            unexpected => Err(error::Kind::UnexpectedToken(unexpected, None).at(loc))
        }
    }
}

impl<F: Clone> Parsable<F> for Attribute<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Attribute<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        let key = Keyword::<F>::parse(lexer)?;
        let token = peek(lexer)?;
        use token::Kind::*;

        let value = match token.kind {
            Ident(name) => {
                match name.chars().next() {
                    Some(':') => None,
                    Some(_) => Some(AttributeValue::<F>::parse(lexer)?),
                    _ => None
                }
            },
            Litteral(_) => Some(AttributeValue::<F>::parse(lexer)?),
            Begin => Some(AttributeValue::<F>::parse(lexer)?),
            _ => None
        };

        let loc = match value {
            Some(ref value) => key.location().union(value.location()),
            None => key.location().clone()
        };

        Ok(Attribute {
            location: loc,
            key: key,
            value: value
        })
    }
}

impl<F: Clone> Parsable<F> for AttributeValue<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<AttributeValue<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        let token = peek(lexer)?;
        let mut loc = token.location().clone();

        use token::Kind::*;
        let kind = match token.kind {
            Ident(_) => {
                let id = ast::Symbol::<F>::parse(lexer)?;
                AttributeValueKind::Sym(id)
            },

            // Litteral(_) => {
            //     let c = Constant::parse(lexer)?;
            //     AttributeValueKind::Const(c)
            // },

            Begin => {
                consume(lexer)?;
                let mut exprs = Vec::new();

                loop {
                    let token = peek(lexer)?;
                    match token.kind {
                        End => {
                            consume(lexer)?;
                            loc = loc.union(token.location());
                            break;
                        },
                        _ => {
                            let expr = SExpr::<F>::parse(lexer)?;
                            exprs.push(expr);
                        }
                    }
                }

                AttributeValueKind::List(exprs)
            },

            unexpected => {
                consume(lexer)?;
                return Err(error::Kind::UnexpectedToken(unexpected, None).at(loc))
            }
        };

        Ok(AttributeValue {
            location: loc,
            kind: kind
        })
    }
}

impl<F: Clone> Parsable<F> for SExpr<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<SExpr<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        let token = peek(lexer)?;
        let mut loc = token.location().clone();

        use token::Kind::*;
        let kind = match token.kind {
            Ident(name) => {
                match name.chars().next() {
                    Some(':') => {
                        let key = Keyword::<F>::parse(lexer)?;
                        SExprKind::Keyword(key)
                    },
                    _ => {
                        let id = ast::Symbol::<F>::parse(lexer)?;
                        SExprKind::Sym(id)
                    }
                }
            },

            // Litteral(_) => {
            //     let c = Constant::parse(lexer)?;
            //     SExprKind::Const(c)
            // },

            Begin => {
                consume(lexer)?;
                let mut exprs = Vec::new();

                loop {
                    let token = peek(lexer)?;
                    match token.kind {
                        End => {
                            consume(lexer)?;
                            loc = loc.union(token.location());
                            break;
                        },
                        _ => {
                            let expr = SExpr::<F>::parse(lexer)?;
                            exprs.push(expr);
                        }
                    }
                }

                SExprKind::List(exprs)
            },

            unexpected => {
                consume(lexer)?;
                return Err(error::Kind::UnexpectedToken(unexpected, None).at(loc))
            }
        };

        Ok(SExpr {
            location: loc,
            kind: kind
        })
    }
}

impl<F: Clone> Parsable<F> for Sort<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Sort<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
        let token = peek(lexer)?;
        let mut loc = token.location().clone();

        match token.kind {
            Ident(_) => {
                let id = ast::Ident::<F>::parse(lexer)?;

                Ok(Sort {
                    location: loc,
                    id: id,
                    parameters: Vec::new()
                })
            },
            Begin => {
				consume(lexer)?;
                let id = ast::Ident::<F>::parse(lexer)?;
                let mut parameters = Vec::new();

                loop {
                    let token = peek(lexer)?;
                    match token.kind {
                        End => {
                            consume(lexer)?;
                            loc = loc.union(token.location());
                            break;
                        },
                        _ => {
                            let param = Sort::<F>::parse(lexer)?;
                            parameters.push(param);
                        }
                    }
                }

                Ok(Sort {
                    location: loc,
                    id: id,
                    parameters: parameters
                })
            }
            unexpected => Err(error::Kind::UnexpectedToken(unexpected, None).at(loc))
        }
    }
}

impl<F: Clone> Parsable<F> for Term<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Term<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
        let token = peek(lexer)?;
        let mut loc = token.location().clone();

        let kind = match token.kind {
            Begin => {
				consume(lexer)?;
                let token = peek(lexer)?;

                match token.kind {
                    Ident(name) => {
                        match name.as_str() {
                            "let" => {
								consume(lexer)?;
								consume_token(lexer, Begin)?; // begining of the bindings list
                                let bindings = parse_list(lexer, &mut loc)?;
                                let body = Term::<F>::parse(lexer)?;
								consume_token(lexer, End)?; // end of the term.

                                TermKind::Let {
                                    bindings: bindings,
                                    body: Box::new(body)
                                }
                            },

                            "forall" => {
								consume(lexer)?;
								consume_token(lexer, Begin)?; // begining of the vars list
                                let vars = parse_list(lexer, &mut loc)?;
                                let body = Term::<F>::parse(lexer)?;
								consume_token(lexer, End)?; // end of the term.

                                TermKind::Forall {
                                    vars: vars,
                                    body: Box::new(body)
                                }
                            },

                            "exists" => {
								consume(lexer)?;
								consume_token(lexer, Begin)?; // begining of the vars list
                                let vars = parse_list(lexer, &mut loc)?;
                                let body = Term::<F>::parse(lexer)?;
								consume_token(lexer, End)?; // end of the term.

                                TermKind::Exists {
                                    vars: vars,
                                    body: Box::new(body)
                                }
                            },

                            _ => {
								let id = ast::Ident::<F>::parse(lexer)?;
								//println!("APPLY list");
								let args = parse_list(lexer, &mut loc)?;
								//println!("APPLY done");

                                TermKind::Apply {
									id: id,
									args: Box::new(args)
								}
                            }
                        }
                    },

                    unexpected => return Err(error::Kind::UnexpectedToken(unexpected, None).at(loc))
                }
            },

            // Litteral(_) => {
            //     let c = Constant::parse(lexer)?;
            //     TermKind::Const(c)
            // },

			_ => {
                let id = ast::Ident::<F>::parse(lexer)?;
				TermKind::Ident(id)
            }
        };

        Ok(Term {
            location: loc,
            kind: kind
        })
    }
}

impl<F: Clone> Parsable<F> for Binding<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Binding<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
        let mut loc = consume_token(lexer, Begin)?;
        let id = Symbol::<F>::parse(lexer)?;
        let term = Term::<F>::parse(lexer)?;
        loc = loc.union(&consume_token(lexer, End)?);

        Ok(Binding {
            location: loc,
            id: id,
            value: Box::new(term)
        })
    }
}

impl<F: Clone> Parsable<F> for SortedVar<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<SortedVar<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
        let mut loc = consume_token(lexer, Begin)?;
        let id = Symbol::<F>::parse(lexer)?;
        let sort = Sort::<F>::parse(lexer)?;
        loc = loc.union(&consume_token(lexer, End)?);

        Ok(SortedVar {
            location: loc,
            id: id,
            sort: sort
        })
    }
}

impl<F: Clone> Parsable<F> for DataTypeDeclaration<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<DataTypeDeclaration<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
		let constructors;
		let parameters;
        let mut loc = consume_token(lexer, Begin)?;

		let next_token = peek(lexer)?;
		match next_token.kind {
			Ident(ref id) if id == "par" => {
				consume(lexer)?;
				consume_token(lexer, Begin)?;
				parameters = parse_list(lexer, &mut loc)?;
				consume_token(lexer, Begin)?;
				constructors = parse_list(lexer, &mut loc)?;
				loc = loc.union(&consume_token(lexer, End)?);
			},
			_ => {
				parameters = Vec::new();
				constructors = parse_list(lexer, &mut loc)?;
			}
		}

        Ok(DataTypeDeclaration {
            location: loc,
			parameters: parameters,
            constructors: constructors
        })
    }
}

impl<F: Clone> Parsable<F> for ConstructorDeclaration<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<ConstructorDeclaration<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
        let mut loc = consume_token(lexer, Begin)?;
        let id = Symbol::<F>::parse(lexer)?;
        let selectors = parse_list(lexer, &mut loc)?;

        Ok(ConstructorDeclaration {
            location: loc,
            id: id,
            selectors: selectors
        })
    }
}

impl<F: Clone> Parsable<F> for SelectorDeclaration<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<SelectorDeclaration<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
        let mut loc = consume_token(lexer, Begin)?;
        let id = Symbol::<F>::parse(lexer)?;
        let sort = Sort::<F>::parse(lexer)?;
        loc = loc.union(&consume_token(lexer, End)?);

        Ok(SelectorDeclaration {
            location: loc,
            id: id,
            sort: sort
        })
    }
}

fn parse_numeral<F: Clone, L>(lexer: &mut Peekable<L>) -> Result<Located<i64, F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
    use token::Kind::*;
    let token = consume(lexer)?;
    let loc = token.location().clone();

    match token.kind {
        Litteral(token::Litteral::Int(i)) => {
            Ok(Located::new(i, loc))
        },
        unexpected => {
            Err(error::Kind::UnexpectedToken(unexpected, None).at(loc))
        }
    }
}

impl<F: Clone> Parsable<F> for SortDeclaration<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<SortDeclaration<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
        let mut loc = consume_token(lexer, Begin)?;
        let id = Symbol::<F>::parse(lexer)?;
        let arity = parse_numeral(lexer)?;
        loc = loc.union(&consume_token(lexer, End)?);

        Ok(SortDeclaration {
            location: loc,
            id: id,
            arity: arity
        })
    }
}

impl<F: Clone> Parsable<F> for Command<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Command<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;
        let mut loc = consume_token(lexer, Begin)?;

        let token = consume(lexer)?;
        let name_loc = token.location().clone();
        let kind = match token.kind {
            Ident(ref name) => {
                match name.as_str() {
                    "assert" => {
                        let term = Term::<F>::parse(lexer)?;
                        CommandKind::Assert(term)
                    },

                    "check-sat" => {
                        CommandKind::CheckSat
                    },

                    "declare-const" => {
                        let id = Symbol::<F>::parse(lexer)?;
                        let sort = Sort::<F>::parse(lexer)?;
                        CommandKind::DeclareConst(id, sort)
                    },

                    "declare-datatype" => {
                        let id = Symbol::<F>::parse(lexer)?;
                        let decl = DataTypeDeclaration::<F>::parse(lexer)?;
                        CommandKind::DeclareDatatype(id, decl)
                    },

                    "declare-datatypes" => {
                        consume_token(lexer, Begin)?;
                        let sort_decls = parse_list(lexer, &mut loc)?;
                        consume_token(lexer, Begin)?;
                        let decls = parse_list(lexer, &mut loc)?;
                        CommandKind::DeclareDatatypes(sort_decls, decls)
                    },

					"declare-fun" => {
						let id = Symbol::<F>::parse(lexer)?;
						consume_token(lexer, Begin)?;
						let args = parse_list(lexer, &mut loc)?;
						let return_sort = Sort::<F>::parse(lexer)?;
						CommandKind::DeclareFun(id, args, return_sort)
					},

                    "exit" => {
                        CommandKind::Exit
                    },

					"get-model" => {
						CommandKind::GetModel
					},

                    "set-info" => {
                        let attr = Attribute::<F>::parse(lexer)?;
                        CommandKind::SetInfo(attr)
                    },

                    "set-logic" => {
                        let logic = Symbol::<F>::parse(lexer)?;
                        CommandKind::SetLogic(logic)
                    },

                    _ => {
                        return Err(error::Kind::UnknownCommand(name.clone()).at(name_loc))
                    }
                }
            },

            unexpected => return Err(error::Kind::UnexpectedToken(unexpected, None).at(name_loc))
        };

        loc = loc.union(&consume_token(lexer, End)?);

        Ok(Command {
            location: loc,
            kind: kind
        })
    }
}
