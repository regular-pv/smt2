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
    parse_list,
    parse_numeral
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

impl<F: Clone> Parsable<F> for Model<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Model<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;

        let mut loc = consume_token(lexer, Begin)?;
        peek_server_error(lexer, &loc)?;

        let mut definitions;
        let mut sorts = Vec::new();

        match peek(lexer)?.kind {
            // this "model" keyword token does not appear in the SMT2-lib specification.
            // however it seems to be pretty standard... In this case we can also have sorts
            // declarations in the model.
            Ident(ref name) if name.as_str() == "model" => {
                consume(lexer)?;
                definitions = Vec::new();
                loop {
                    let token = consume(lexer)?;
                    let item_loc = token.location().clone();
                    match token.kind {
                        Begin => {
                            let token = peek(lexer)?;
                            let id_loc = token.location().clone();
                            match token.kind {
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

                                            let decl_loc = item_loc.union(&consume_token(lexer, End)?);

                                            let decl = SortDeclaration {
                                                location: decl_loc,
                                                id: id,
                                                arity: arity
                                            };

                                            sorts.push(decl);
                                        },
                                        unexpected => return Err(error::Kind::UnexpectedToken(Ident(unexpected.to_string()), None).at(id_loc))
                                    }
                                },
                                unexpected => return Err(error::Kind::UnexpectedToken(unexpected, None).at(id_loc))
                            }
                        },
                        End => {
                            break
                        },
                        unexpected => return Err(error::Kind::UnexpectedToken(unexpected, None).at(item_loc))
                    }
                }
            },
            _ => {
                definitions = parse_list(lexer, &mut loc)?;
            }
        }

        Ok(Model {
            location: loc,
            sorts: sorts,
            definitions: definitions
        })
    }
}

impl<F: Clone> Definition<F> {
    fn parse_at<L>(lexer: &mut Peekable<L>, mut loc: Location<F>) -> Result<Definition<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;

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
                    // "declare-sort" => {
                    //     let id = Symbol::parse(lexer)?;
                    //     let arity = parse_numeral(lexer)?;
                    // },
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

impl<F: Clone> Parsable<F> for Definition<F> {
    fn parse<L>(lexer: &mut Peekable<L>) -> Result<Definition<F>, F> where L: Iterator<Item=Result<Token<F>, F>> {
        use token::Kind::*;

        let mut loc = consume_token(lexer, Begin)?;
        Self::parse_at(lexer, loc)
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
