use std::iter::Peekable;
use source_span::Span;
use crate::Located;
use crate::syntax::{
    token,
    Token,
    Parsable,
    error,
    Error,
    Result,
    peek,
    consume,
    consume_token,
    parse_list,
    parse_numeral
};

mod ast;
pub mod display;

pub use ast::*;

fn server_error<L>(lexer: &mut Peekable<L>, mut loc: Span) -> Result<Located<Error>> where L: Iterator<Item=Result<Located<Token>>> {
    use Token::*;

    let token = consume(lexer)?;
    let id_loc = token.span();
    match *token {
        Ident(name) => {
            match name.as_str() {
                "error" => {
                    let token = consume(lexer)?;
                    let message_loc = token.span();
                    match *token {
                        Litteral(token::Litteral::String(message)) => {
                            loc = loc.union(consume_token(lexer, End)?);
                            Ok(Error::Server(message).at(loc))
                        },
                        unexpected => Err(Error::UnexpectedToken(Ident(unexpected.to_string()), None).at(message_loc))
                    }
                },
                unexpected => Err(Error::UnexpectedToken(Ident(unexpected.to_string()), None).at(id_loc))
            }
        },
        unexpected => Err(Error::UnexpectedToken(unexpected, None).at(id_loc))
    }
}

fn peek_server_error<L>(lexer: &mut Peekable<L>, loc: &Span) -> Result<()> where L: Iterator<Item=Result<Located<Token>>> {
    use Token::*;

    let token = peek(lexer)?;
    match *token {
        Ident(name) => {
            match name.as_str() {
                "error" => Err(server_error(lexer, loc.clone())?),
                _ => Ok(())
            }
        },
        _ => Ok(())
    }
}

impl Parsable for CheckSat {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<CheckSat>> where L: Iterator<Item=Result<Located<Token>>> {
        use Token::*;

        let token = consume(lexer)?;
        let loc = token.span();
        match *token {
            Ident(name) => {
                match name.as_str() {
                    "sat" => {
                        Ok(Located::new(crate::response::CheckSat::Sat, loc))
                    },
                    "unsat" => {
                        Ok(Located::new(crate::response::CheckSat::Unsat, loc))
                    },
                    "unknown" => {
                        Ok(Located::new(crate::response::CheckSat::Unknown, loc))
                    },
                    unexpected => Err(Error::UnexpectedToken(Ident(unexpected.to_string()), None).at(loc))
                }
            },
            Begin => Err(server_error(lexer, loc)?),
            unexpected => Err(Error::UnexpectedToken(unexpected, None).at(loc))
        }
    }
}

impl Parsable for Model {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Model>> where L: Iterator<Item=Result<Located<Token>>> {
        use Token::*;

        let mut loc = consume_token(lexer, Begin)?;
        peek_server_error(lexer, &loc)?;

        let mut definitions;
        let mut sorts = Vec::new();

        match *peek(lexer)? {
            // this "model" keyword token does not appear in the SMT2-lib specification.
            // however it seems to be pretty standard... In this case we can also have sorts
            // declarations in the model.
            Ident(ref name) if name.as_str() == "model" => {
                consume(lexer)?;
                definitions = Vec::new();
                loop {
                    let token = consume(lexer)?;
                    let item_loc = token.span();
                    match *token {
                        Begin => {
                            let token = peek(lexer)?;
                            let id_loc = token.span();
                            match *token {
                                Ident(ref name) => {
                                    match name.as_ref() {
                                        "define-fun" | "define-fun-rec" | "define-funs-rec" => {
                                            let def = Definition::parse_at(lexer, item_loc)?;
                                            definitions.push(def);
                                        },
                                        "declare-sort" => {
                                            consume(lexer)?;
                                            let id = Symbol::parse(lexer)?;
                                            let arity = parse_numeral(lexer)?;

                                            let decl_loc = item_loc.union(consume_token(lexer, End)?);

                                            let decl = Located::new(SortDeclaration {
                                                id: id,
                                                arity: arity
                                            }, decl_loc);

                                            sorts.push(decl);
                                        },
                                        unexpected => return Err(Error::UnexpectedToken(Ident(unexpected.to_string()), None).at(id_loc))
                                    }
                                },
                                unexpected => return Err(Error::UnexpectedToken(unexpected, None).at(id_loc))
                            }
                        },
                        End => {
                            break
                        },
                        unexpected => return Err(Error::UnexpectedToken(unexpected, None).at(item_loc))
                    }
                }
            },
            _ => {
                definitions = parse_list(lexer, &mut loc)?;
            }
        }

        Ok(Located::new(Model {
            sorts: sorts,
            definitions: definitions
        }, loc))
    }
}

impl Definition {
    fn parse_at<L>(lexer: &mut Peekable<L>, mut loc: Span) -> Result<Located<Definition>> where L: Iterator<Item=Result<Located<Token>>> {
        use Token::*;

        let token = consume(lexer)?;
        let id_loc = token.span();

        let rec;
        let declarations;
        let bodies;

        match *token {
            Ident(name) => {
                match name.as_str() {
                    "define-fun" => {
                        rec = true;
                        let id = Symbol::parse(lexer)?;
                        consume_token(lexer, Begin)?;
                        let args = parse_list(lexer, &mut loc)?;
                        let return_sort = Sort::parse(lexer)?;
                        let body = Term::parse(lexer)?;

                        let def_loc = id.span().union(body.span());

                        declarations = vec![Located::new(Declaration {
                            id: id,
                            args: args,
                            return_sort: return_sort
                        }, def_loc)];

                        bodies = vec![body];
                    },
                    "define-fun-rec" => {
                        rec = true;
                        let id = Symbol::parse(lexer)?;
                        consume_token(lexer, Begin)?;
                        let args = parse_list(lexer, &mut loc)?;
                        let return_sort = Sort::parse(lexer)?;
                        let body = Term::parse(lexer)?;

                        let def_loc = id.span().union(body.span());

                        declarations = vec![Located::new(Declaration {
                            id: id,
                            args: args,
                            return_sort: return_sort
                        }, def_loc)];

                        bodies = vec![body];
                    },
                    "define-funs-rec" => {
                        rec = true;
                        consume_token(lexer, Begin)?;
                        declarations = parse_list(lexer, &mut loc)?;
                        consume_token(lexer, Begin)?;
                        bodies = parse_list(lexer, &mut loc)?;
                    },
                    // "declare-sort" => {
                    //     let id = Symbol::parse(lexer)?;
                    //     let arity = parse_numeral(lexer)?;
                    // },
                    unexpected => return Err(Error::UnexpectedToken(Ident(unexpected.to_string()), None).at(id_loc))
                }
            },
            unexpected => return Err(Error::UnexpectedToken(unexpected, None).at(id_loc))
        }

        loc = loc.union(consume_token(lexer, End)?);

        Ok(Located::new(Definition {
            rec: rec,
            declarations: declarations,
            bodies: bodies
        }, loc))
    }
}

impl Parsable for Definition {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Definition>> where L: Iterator<Item=Result<Located<Token>>> {
        use Token::*;

        let mut loc = consume_token(lexer, Begin)?;
        Self::parse_at(lexer, loc)
    }
}

impl Parsable for Declaration {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Located<Declaration>> where L: Iterator<Item=Result<Located<Token>>> {
        use Token::*;

        let mut loc = consume_token(lexer, Begin)?;
        let id = Symbol::parse(lexer)?;
        consume_token(lexer, Begin)?;
        let args = parse_list(lexer, &mut loc)?;
        let return_sort = Sort::parse(lexer)?;
        loc = loc.union(consume_token(lexer, End)?);

        Ok(Located::new(Declaration {
            id: id,
            args: args,
            return_sort: return_sort
        }, loc))
    }
}
