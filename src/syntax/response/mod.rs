use std::iter::Peekable;
use crate::{Location, Located, Localisable};
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
    parse_list
};

mod ast;

pub use ast::*;

fn server_error<L, F: Clone>(lexer: &mut Peekable<L>, mut loc: Location<F>) -> Result<Error<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
    use token::Kind::*;

    let token = consume(lexer)?;
    let id_loc = token.location().clone();
    match token.kind {
        Ident(name) => {
            match name.as_str() {
                "error" => {
                    let token = consume(lexer)?;
                    let message_loc = token.location().clone();
                    match token.kind {
                        Litteral(token::Litteral::String(message)) => {
                            loc = loc.union(&consume_token(lexer, End)?);
                            Ok(error::Kind::Server(message).at(loc))
                        },
                        unexpected => Err(error::Kind::UnexpectedToken(Ident(unexpected.to_string()), None).at(message_loc))
                    }
                },
                unexpected => Err(error::Kind::UnexpectedToken(Ident(unexpected.to_string()), None).at(id_loc))
            }
        },
        unexpected => Err(error::Kind::UnexpectedToken(unexpected, None).at(id_loc))
    }
}

fn peek_server_error<L, F: Clone>(lexer: &mut Peekable<L>, loc: &Location<F>) -> Result<(), F> where L: Iterator<Item=Result<Token<F>, F>> {
    use token::Kind::*;

    let token = peek(lexer)?;
    match token.kind {
        Ident(name) => {
            match name.as_str() {
                "error" => Err(server_error(lexer, loc.clone())?),
                _ => Ok(())
            }
        },
        _ => Ok(())
    }
}

impl<F: Clone> Parsable<F> for CheckSat<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<CheckSat<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;

        let token = consume(lexer)?;
        let loc = token.location().clone();
        match token.kind {
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
                    unexpected => Err(error::Kind::UnexpectedToken(Ident(unexpected.to_string()), None).at(loc))
                }
            },
            Begin => Err(server_error(lexer, loc)?),
            unexpected => Err(error::Kind::UnexpectedToken(unexpected, None).at(loc))
        }
    }
}

impl<F: Clone> Parsable<F> for GetModel<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<GetModel<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;

        let mut loc = consume_token(lexer, Begin)?;
        peek_server_error(lexer, &loc)?;
        let definitions = parse_list(lexer, &mut loc)?;

        Ok(GetModel {
            location: loc,
            definitions: definitions
        })
    }
}

impl<F: Clone> Parsable<F> for Definition<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Definition<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;

        let mut loc = consume_token(lexer, Begin)?;
        let token = consume(lexer)?;
        let id_loc = token.location().clone();

        let rec;
        let declarations;
        let bodies;

        match token.kind {
            Ident(name) => {
                match name.as_str() {
                    "define-fun" => {
                        rec = true;
                        let id = Symbol::parse(lexer)?;
                        consume_token(lexer, Begin)?;
                        let args = parse_list(lexer, &mut loc)?;
                        let return_sort = Sort::parse(lexer)?;
                        let body = Term::parse(lexer)?;

                        let def_loc = id.location().union(body.location());

                        declarations = vec![Declaration {
                            location: def_loc,
                            id: id,
                            args: args,
                            return_sort: return_sort
                        }];

                        bodies = vec![body];
                    },
                    "define-fun-rec" => {
                        rec = true;
                        let id = Symbol::parse(lexer)?;
                        consume_token(lexer, Begin)?;
                        let args = parse_list(lexer, &mut loc)?;
                        let return_sort = Sort::parse(lexer)?;
                        let body = Term::parse(lexer)?;

                        let def_loc = id.location().union(body.location());

                        declarations = vec![Declaration {
                            location: def_loc,
                            id: id,
                            args: args,
                            return_sort: return_sort
                        }];

                        bodies = vec![body];
                    },
                    "define-funs-rec" => {
                        rec = true;
                        consume_token(lexer, Begin)?;
                        declarations = parse_list(lexer, &mut loc)?;
                        consume_token(lexer, Begin)?;
                        bodies = parse_list(lexer, &mut loc)?;
                    },
                    unexpected => return Err(error::Kind::UnexpectedToken(Ident(unexpected.to_string()), None).at(id_loc))
                }
            },
            unexpected => return Err(error::Kind::UnexpectedToken(unexpected, None).at(id_loc))
        }

        loc = loc.union(&consume_token(lexer, End)?);

        Ok(Definition {
            location: loc,
            rec: rec,
            declarations: declarations,
            bodies: bodies
        })
    }
}

impl<F: Clone> Parsable<F> for Declaration<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Declaration<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;

        let mut loc = consume_token(lexer, Begin)?;
        let id = Symbol::parse(lexer)?;
        consume_token(lexer, Begin)?;
        let args = parse_list(lexer, &mut loc)?;
        let return_sort = Sort::parse(lexer)?;
        loc = loc.union(&consume_token(lexer, End)?);

        Ok(Declaration {
            location: loc,
            id: id,
            args: args,
            return_sort: return_sort
        })
    }
}
