// use std::marker::PhantomData;
// use std::fmt;
// use std::io::{Read, Write, Bytes};
// use std::fs::File;
// use std::os::unix::io::{AsRawFd, FromRawFd};
// use std::collections::HashMap;
// use std::hash::Hash;
// use std::iter::Peekable;
// use std::process::{
//     self,
//     Stdio
// };
// use crate::*;
// use syntax::Parsable;

use super::*;
use super::error::InternalError;

impl<L, C: Constant, S: Sort, F: Function> Client<L, C, S, F> {
    pub(crate) fn downgrade_term(&self, term: &Term<Self>) -> ExecResult<Term<Internal<L, C, F>>, Error<L, C, S, F>> {
        use Term::*;
        match term {
            Const(Sorted(c, sort)) => {
                Ok(Const(Sorted(c.clone(), self.downgrade_ground_sort(sort)?)))
            },
            Var { index, id } => Ok(Var { index: *index, id: id.clone() }),
            Let { bindings, body } => {
                let mut internal_bindings = Vec::with_capacity(bindings.len());
                for b in bindings.iter() {
                    internal_bindings.push(self.downgrade_binding(b)?);
                }
                Ok(Let {
                    bindings: internal_bindings,
                    body: Box::new(self.downgrade_term(body)?)
                })
            },
            Forall { vars, body } => {
                let mut internal_vars = Vec::with_capacity(vars.len());
                for x in vars.iter() {
                    internal_vars.push(self.downgrade_sorted_var(x)?);
                }
                Ok(Forall {
                    vars: internal_vars,
                    body: Box::new(self.downgrade_term(body)?)
                })
            },
            Exists { vars, body } => {
                let mut internal_vars = Vec::with_capacity(vars.len());
                for x in vars.iter() {
                    internal_vars.push(self.downgrade_sorted_var(x)?);
                }
                Ok(Exists {
                    vars: internal_vars,
                    body: Box::new(self.downgrade_term(body)?)
                })
            },
            Match { term, cases } => {
                let mut internal_cases = Vec::with_capacity(cases.len());
                for c in cases {
                    internal_cases.push(self.downgrade_case(c)?);
                }
                Ok(Match {
                    term: Box::new(self.downgrade_term(term)?),
                    cases: internal_cases
                })
            },
            Apply { fun, args, sort } => {
                let mut internal_args = Vec::with_capacity(args.len());
                for a in args.iter() {
                    internal_args.push(self.downgrade_term(a)?);
                }
                Ok(Apply {
                    fun: self.downgrade_function(fun)?,
                    args: Box::new(internal_args),
                    sort: self.downgrade_ground_sort(sort)?
                })
            }
        }
    }

    pub(crate) fn downgrade_case(&self, _case: &MatchCase<Self>) -> ExecResult<MatchCase<Internal<L, C, F>>, Error<L, C, S, F>> {
        panic!("TODO")
    }

    pub(crate) fn downgrade_pattern(&self, _pattern: &Pattern<Self>) -> ExecResult<Pattern<Internal<L, C, F>>, Error<L, C, S, F>> {
        panic!("TODO")
    }

    pub(crate) fn downgrade_binding(&self, _binding: &Binding<Self>) -> ExecResult<Binding<Internal<L, C, F>>, Error<L, C, S, F>> {
        panic!("TODO")
    }

    pub(crate) fn downgrade_sorted_var(&self, _x: &SortedVar<Self>) -> ExecResult<SortedVar<Internal<L, C, F>>, Error<L, C, S, F>> {
        panic!("TODO")
    }

    pub(crate) fn downgrade_function(&self, f: &F) -> ExecResult<InternalFunction<F>, Error<L, C, S, F>> {
        if let Some(internal_f) = self.internal.functions_ids.get(f) {
            Ok(internal_f.clone())
        } else {
            Err(Error::UnknownUserFunction(f.clone()))
        }
    }

    pub(crate) fn downgrade_signature(&self, sig: FunctionSignature<S>) -> ExecResult<InternalFunctionSignature, Error<L, C, S, F>> {
        match sig {
            FunctionSignature::User { args, return_sort } => {
                let mut d_args = Vec::with_capacity(args.len());
                for a in &args {
                    d_args.push(self.downgrade_ground_sort(a)?)
                }

                let d_return_sort = self.downgrade_ground_sort(&return_sort)?;

                Ok(InternalFunctionSignature::User {
                    args: d_args,
                    return_sort: d_return_sort
                })
            },
            FunctionSignature::Equality => Ok(InternalFunctionSignature::Equality),
            FunctionSignature::LogicUnary => Ok(InternalFunctionSignature::LogicUnary),
            FunctionSignature::LogicBinary => Ok(InternalFunctionSignature::LogicBinary),
            FunctionSignature::LogicNary => Ok(InternalFunctionSignature::LogicNary),
            FunctionSignature::Ite => Ok(InternalFunctionSignature::Ite)
        }
    }

    pub(crate) fn downgrade_sort(&self, sort: &S) -> ExecResult<Ident, Error<L, C, S, F>> {
        if let Some(id) = self.sorts_ids.get(sort) {
            Ok(id.clone())
        } else {
            Err(Error::UnknownSort)
        }
    }

    pub(crate) fn downgrade_ground_sort(&self, sort: &GroundSort<S>) -> ExecResult<GroundSort<Ident>, Error<L, C, S, F>> {
        let mut parameters = Vec::with_capacity(sort.parameters.len());
        for p in &sort.parameters {
            parameters.push(self.downgrade_ground_sort(p)?);
        }

        Ok(GroundSort {
            sort: self.downgrade_sort(&sort.sort)?,
            parameters: parameters
        })
    }

    pub(crate) fn downgrade_sort_declaration(&self, decl: &SortDeclaration<Self>) -> ExecResult<SortDeclaration<Internal<L, C, F>>, Error<L, C, S, F>> {
        Ok(SortDeclaration {
            id: decl.id.clone(),
            arity: decl.arity
        })
    }

    pub(crate) fn upgrade_term(&self, term: &Term<Internal<L, C, F>>) -> ExecResult<Term<Self>, Error<L, C, S, F>> {
        use Term::*;
        match term {
            Const(Sorted(c, sort)) => {
                Ok(Const(Sorted(c.clone(), self.upgrade_ground_sort(sort)?)))
            },
            Var { index, id } => Ok(Var { index: *index, id: id.clone() }),
            Let { bindings, body } => {
                let mut internal_bindings = Vec::with_capacity(bindings.len());
                for b in bindings.iter() {
                    internal_bindings.push(self.upgrade_binding(b)?);
                }
                Ok(Let {
                    bindings: internal_bindings,
                    body: Box::new(self.upgrade_term(body)?)
                })
            },
            Forall { vars, body } => {
                let mut internal_vars = Vec::with_capacity(vars.len());
                for x in vars.iter() {
                    internal_vars.push(self.upgrade_sorted_var(x)?);
                }
                Ok(Forall {
                    vars: internal_vars,
                    body: Box::new(self.upgrade_term(body)?)
                })
            },
            Exists { vars, body } => {
                let mut internal_vars = Vec::with_capacity(vars.len());
                for x in vars.iter() {
                    internal_vars.push(self.upgrade_sorted_var(x)?);
                }
                Ok(Exists {
                    vars: internal_vars,
                    body: Box::new(self.upgrade_term(body)?)
                })
            },
            Match { term, cases } => {
                let mut u_cases = Vec::with_capacity(cases.len());
                for c in cases {
                    u_cases.push(self.upgrade_case(c)?);
                }
                Ok(Match {
                    term: Box::new(self.upgrade_term(term)?),
                    cases: u_cases
                })
            },
            Apply { fun, args, sort } => {
                let mut internal_args = Vec::with_capacity(args.len());
                for a in args.iter() {
                    internal_args.push(self.upgrade_term(a)?);
                }
                Ok(Apply {
                    fun: self.upgrade_function(fun)?,
                    args: Box::new(internal_args),
                    sort: self.upgrade_ground_sort(sort)?
                })
            }
        }
    }

    pub(crate) fn upgrade_case(&self, _case: &MatchCase<Internal<L, C, F>>) -> ExecResult<MatchCase<Self>, Error<L, C, S, F>> {
        panic!("TODO")
    }

    pub(crate) fn upgrade_pattern(&self, _pattern: &Pattern<Internal<L, C, F>>) -> ExecResult<Pattern<Self>, Error<L, C, S, F>> {
        panic!("TODO")
    }

    pub(crate) fn upgrade_binding(&self, _binding: &Binding<Internal<L, C, F>>) -> ExecResult<Binding<Self>, Error<L, C, S, F>> {
        panic!("TODO")
    }

    pub(crate) fn upgrade_sorted_var(&self, x: &SortedVar<Internal<L, C, F>>) -> ExecResult<SortedVar<Self>, Error<L, C, S, F>> {
        Ok(SortedVar {
            id: x.id.clone(),
            sort: self.upgrade_ground_sort(&x.sort)?
        })
    }

    pub(crate) fn upgrade_function(&self, f: &InternalFunction<F>) -> ExecResult<F, Error<L, C, S, F>> {
        Ok(f.f.clone())
    }

    pub(crate) fn upgrade_sort(&self, sort: &Ident) -> ExecResult<S, Error<L, C, S, F>> {
        if let Some(sort) = self.ids_sorts.get(sort) {
            Ok(sort.clone())
        } else {
            Err(Error::UnknownSort)
        }
    }

    pub(crate) fn upgrade_abstract_sort(&self, sort: &AbstractGroundSort<Ident>) -> ExecResult<AbstractGroundSort<S>, Error<L, C, S, F>> {
        match sort {
            AbstractGroundSort::Param(i) => Ok(AbstractGroundSort::Param(*i)),
            AbstractGroundSort::Sort { sort, parameters } => {
                let mut u_parameters = Vec::with_capacity(parameters.len());
                for p in parameters {
                    u_parameters.push(self.upgrade_abstract_sort(p)?);
                }

                Ok(AbstractGroundSort::Sort {
                    sort: self.upgrade_sort(sort)?,
                    parameters: u_parameters
                })
            }
        }
    }

    pub(crate) fn upgrade_ground_sort(&self, sort: &GroundSort<Ident>) -> ExecResult<GroundSort<S>, Error<L, C, S, F>> {
        let mut parameters = Vec::with_capacity(sort.parameters.len());
        for p in &sort.parameters {
            parameters.push(self.upgrade_ground_sort(p)?);
        }

        Ok(GroundSort {
            sort: self.upgrade_sort(&sort.sort)?,
            parameters: parameters
        })
    }

    pub(crate) fn upgrade_model(&self, model: &response::Model<Internal<L, C, F>>) -> ExecResult<response::Model<Self>, Error<L, C, S, F>> {
        let mut definitions = Vec::with_capacity(model.definitions.len());
        for def in model.definitions.iter() {
            definitions.push(self.upgrade_definition(def)?);
        }

        Ok(response::Model {
            definitions: definitions
        })
    }

    pub(crate) fn upgrade_definition(&self, def: &response::Definition<Internal<L, C, F>>) -> ExecResult<response::Definition<Self>, Error<L, C, S, F>> {
        let mut declarations = Vec::with_capacity(def.declarations.len());
        let mut bodies = Vec::with_capacity(def.bodies.len());

        for decl in def.declarations.iter() {
            declarations.push(self.upgrade_declaration(decl)?);
        }

        for body in def.bodies.iter() {
            bodies.push(self.upgrade_term(body)?);
        }

        Ok(response::Definition {
            rec: def.rec,
            declarations: declarations,
            bodies: bodies
        })
    }

    pub(crate) fn upgrade_declaration(&self, decl: &response::Declaration<Internal<L, C, F>>) -> ExecResult<response::Declaration<Self>, Error<L, C, S, F>> {
        let f = self.upgrade_function(&decl.f)?;

        let mut args = Vec::with_capacity(decl.args.len());
        for a in decl.args.iter() {
            args.push(self.upgrade_sorted_var(a)?);
        }

        let return_sort = self.upgrade_ground_sort(&decl.return_sort)?;

        Ok(response::Declaration {
            f: f,
            args: args,
            return_sort: return_sort
        })
    }

    pub(crate) fn upgrade_result<T>(&self, r: ExecResult<T, InternalError<L, C, F>>) -> ExecResult<T, Error<L, C, S, F>> {
        match r {
            Ok(t) => Ok(t),
            Err(e) => {
                Err(match e {
                    InternalError::IO(e) => Error::IO(e),
                    InternalError::Server(msg) => Error::Server(msg),
                    InternalError::Syntax(e) => Error::Syntax(e),
                    InternalError::Compile(e) => {
                        use crate::Error::*;
                        let location = e.span();
                        let kind = match e.into_inner() {
                            UnknownLogic => UnknownLogic,
                            InvalidSymbol(s) => InvalidSymbol(s),
                            InvalidIdent(id) => InvalidIdent(id),
                            UnknownSort => UnknownSort,
                            UnknownFunction(id) => UnknownFunction(id),
                            UndefinedVariable(id) => UndefinedVariable(id),
                            NegativeArity => NegativeArity,
                            WrongNumberOfArguments(a, b, c) => WrongNumberOfArguments(a, b, c),
                            TypeMissmatch(expected, given) => TypeMissmatch(self.upgrade_abstract_sort(&expected)?, self.upgrade_ground_sort(&given)?),
                            TypeAmbiguity => TypeAmbiguity
                        };

                        Error::Compile(Located::new(kind, location))
                    }
                })
            }
        }
    }
}
