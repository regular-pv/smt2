use std::marker::PhantomData;
use std::fmt;
use std::io::{Read, Write, Bytes};
use std::fs::File;
use std::os::unix::io::{AsRawFd, FromRawFd};
use std::collections::HashMap;
use std::hash::Hash;
use std::iter::Peekable;
use std::process::{
    self,
    Stdio
};
use crate::*;
use syntax::Parsable;

pub enum Error<L, I: Clone + Hash + Eq + FromSyntaxSymbol, S: Clone + Hash + Eq, F: Clone + Hash + Eq> {
    IO(std::io::Error),
    Server(String),
    Syntax(syntax::Error<u32>),
    Compile(error::Error<Client<L, I, S, F>, u32>)
}

impl<L, I: Clone + Hash + Eq + FromSyntaxSymbol, S: Clone + Hash + Eq, F: Clone + Hash + Eq> From<std::io::Error> for Error<L, I, S, F> {
    fn from(e: std::io::Error) -> Error<L, I, S, F> {
        Error::IO(e)
    }
}

impl<L, I: Clone + Hash + Eq + FromSyntaxSymbol, S: Clone + Hash + Eq, F: Clone + Hash + Eq> From<syntax::Error<u32>> for Error<L, I, S, F> {
    fn from(e: syntax::Error<u32>) -> Error<L, I, S, F> {
        if let syntax::error::Kind::Server(message) = e.kind {
            Error::Server(message)
        } else {
            Error::Syntax(e)
        }
    }
}

impl<L: fmt::Display, I: Clone + Hash + Eq + FromSyntaxSymbol + fmt::Display, S: Clone + Hash + Eq + fmt::Display, F: Clone + Hash + Eq + fmt::Display> fmt::Display for Error<L, I, S, F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::IO(e) => write!(f, "IO: {}", e),
            Error::Server(msg) => write!(f, "solver reponded with an error: {}", msg),
            Error::Syntax(e) =>  write!(f, "syntax error in the solver response: {}", e),
            Error::Compile(e) => write!(f, "unable to compile the solver response: {}", e)
        }
    }
}

enum InternalError<L, I: Clone + Eq + Hash + FromSyntaxSymbol> {
    IO(std::io::Error),
    Server(String),
    Syntax(syntax::Error<u32>),
    Compile(error::Error<Internal<L, I>, u32>)
}

impl<L, I: Clone + Eq + Hash + FromSyntaxSymbol> From<std::io::Error> for InternalError<L, I> {
    fn from(e: std::io::Error) -> InternalError<L, I> {
        InternalError::IO(e)
    }
}

impl<L, I: Clone + Eq + Hash + FromSyntaxSymbol> From<syntax::Error<u32>> for InternalError<L, I> {
    fn from(e: syntax::Error<u32>) -> InternalError<L, I> {
        if let syntax::error::Kind::Server(message) = e.kind {
            InternalError::Server(message)
        } else {
            InternalError::Syntax(e)
        }
    }
}

impl<L, I: Clone + Eq + Hash + FromSyntaxSymbol> From<error::Error<Internal<L, I>, u32>> for InternalError<L, I> {
    fn from(e: error::Error<Internal<L, I>, u32>) -> InternalError<L, I> {
        InternalError::Compile(e)
    }
}

pub trait FromSyntaxSymbol: Sized {
    fn from_syntax<F: Clone>(sym: &syntax::Symbol<F>) -> Self;
}

// #[derive(Clone, Copy, PartialEq, Eq, Hash)]
// enum InternalIdent {
//     Raw(&'static str),
//     Fresh(&'static str, usize)
// }

// impl fmt::Display for InternalIdent {
//     fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
//         match self {
//             InternalIdent::Raw(name) => write!(f, "{}", name),
//             InternalIdent::Fresh(prefix, id) => write!(f, "{}{}", prefix, id)
//         }
//     }
// }

/// SMT2-lib solver environment.
pub struct Client<L, I: Clone + Hash + Eq + FromSyntaxSymbol, S: Clone + Hash + Eq, F: Clone + Hash + Eq> {
    internal: Internal<L, I>,
    sort_bool: GroundSort<S>,
    sorts_ids: HashMap<S, I>,
    ids_sorts: HashMap<I, S>,
    functions_ids: HashMap<F, I>,
    ids_functions: HashMap<I, F>,
    l: PhantomData<L>,
}

impl<L, I: Clone + Hash + Eq + FromSyntaxSymbol, S: Clone + Hash + Eq, F: Clone + Hash + Eq> Client<L, I, S, F> {
    pub fn new(mut cmd: process::Command, ident_bool: I, sort_bool: S) -> std::io::Result<Client<L, I, S, F>> {
        let server = cmd.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn()?;

        //let internal_bool = InternalIdent::Raw("Bool");

        let mut sorts_ids = HashMap::new();
        sorts_ids.insert(sort_bool.clone(), ident_bool.clone());
        let mut ids_sorts = HashMap::new();
        ids_sorts.insert(ident_bool.clone(), sort_bool.clone());

        // let file = unsafe { File::from_raw_fd(server.stdout.as_ref().unwrap().as_raw_fd()) };

        let internal = Internal {
            sort_bool: GroundSort::new(ident_bool),
            server: server,
            l: PhantomData,
        };

        Ok(Client {
            internal: internal,
            sort_bool: GroundSort::new(sort_bool),
            sorts_ids: sorts_ids,
            ids_sorts: ids_sorts,
            functions_ids: HashMap::new(),
            ids_functions: HashMap::new(),
            l: PhantomData,
        })
    }

    fn downgrade_term(&self, term: &Term<Self>) -> ExecResult<Term<Internal<L, I>>, Error<L, I, S, F>> {
        use Term::*;
        match term {
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

    fn downgrade_binding(&self, binding: &Binding<Self>) -> ExecResult<Binding<Internal<L, I>>, Error<L, I, S, F>> {
        panic!("TODO")
    }

    fn downgrade_sorted_var(&self, x: &SortedVar<Self>) -> ExecResult<SortedVar<Internal<L, I>>, Error<L, I, S, F>> {
        panic!("TODO")
    }

    fn downgrade_function(&self, f: &F) -> ExecResult<InternalFunction<I>, Error<L, I, S, F>> {
        panic!("TODO")
    }

    fn downgrade_ground_sort(&self, sort: &GroundSort<S>) -> ExecResult<GroundSort<I>, Error<L, I, S, F>> {
        panic!("TODO")
    }

    fn upgrade_term(&self, term: &Term<Internal<L, I>>) -> ExecResult<Term<Self>, Error<L, I, S, F>> {
        use Term::*;
        match term {
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

    fn upgrade_binding(&self, binding: &Binding<Internal<L, I>>) -> ExecResult<Binding<Self>, Error<L, I, S, F>> {
        panic!("TODO")
    }

    fn upgrade_sorted_var(&self, x: &SortedVar<Internal<L, I>>) -> ExecResult<SortedVar<Self>, Error<L, I, S, F>> {
        panic!("TODO")
    }

    fn upgrade_function(&self, f: &InternalFunction<I>) -> ExecResult<F, Error<L, I, S, F>> {
        panic!("TODO")
    }

    fn upgrade_sort(&self, sort: &I) -> ExecResult<S, Error<L, I, S, F>> {
        panic!("TODO")
    }

    fn upgrade_abstract_sort(&self, sort: &AbstractGroundSort<I>) -> ExecResult<AbstractGroundSort<S>, Error<L, I, S, F>> {
        panic!("TODO")
    }

    fn upgrade_ground_sort(&self, sort: &GroundSort<I>) -> ExecResult<GroundSort<S>, Error<L, I, S, F>> {
        panic!("TODO")
    }

    fn upgrade_model(&self, model: &response::Model<Internal<L, I>>) -> ExecResult<response::Model<Self>, Error<L, I, S, F>> {
        let mut definitions = Vec::with_capacity(model.definitions.len());
        for def in model.definitions.iter() {
            definitions.push(self.upgrade_definition(def)?);
        }

        Ok(response::Model {
            definitions: definitions
        })
    }

    fn upgrade_definition(&self, def: &response::Definition<Internal<L, I>>) -> ExecResult<response::Definition<Self>, Error<L, I, S, F>> {
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

    fn upgrade_declaration(&self, decl: &response::Declaration<Internal<L, I>>) -> ExecResult<response::Declaration<Self>, Error<L, I, S, F>> {
        let id = decl.id.clone();

        let mut args = Vec::with_capacity(decl.args.len());
        for a in decl.args.iter() {
            args.push(self.upgrade_sorted_var(a)?);
        }

        let return_sort = self.upgrade_ground_sort(&decl.return_sort)?;

        Ok(response::Declaration {
            id: id,
            args: args,
            return_sort: return_sort
        })
    }

    fn upgrade_result<T>(&self, r: ExecResult<T, InternalError<L, I>>) -> ExecResult<T, Error<L, I, S, F>> {
        match r {
            Ok(t) => Ok(t),
            Err(e) => {
                Err(match e {
                    InternalError::IO(e) => Error::IO(e),
                    InternalError::Server(msg) => Error::Server(msg),
                    InternalError::Syntax(e) => Error::Syntax(e),
                    InternalError::Compile(e) => {
                        use error::Kind::*;
                        let kind = match e.kind {
                            UnknownLogic => UnknownLogic,
                            InvalidSymbol(s) => InvalidSymbol(s),
                            InvalidIdent(id) => InvalidIdent(id),
                            UnknownSort => UnknownSort,
                            UnknownFunction => UnknownFunction,
                            UndefinedVariable(id) => UndefinedVariable(id),
                            NegativeArity => NegativeArity,
                            WrongNumberOfArguments(a, b, c) => WrongNumberOfArguments(a, b, c),
                            TypeMissmatch(expected, given) => TypeMissmatch(self.upgrade_abstract_sort(&expected)?, self.upgrade_ground_sort(&given)?),
                            TypeAmbiguity => TypeAmbiguity
                        };

                        Error::Compile(error::Error {
                            location: e.location,
                            kind: kind
                        })
                    }
                })
            }
        }
    }
}

impl<L, I: Clone + Hash + Eq + FromSyntaxSymbol, S: Clone + Eq + Hash, F: Clone + Eq + Hash> Environment for Client<L, I, S, F> {
    type Logic = L;
    type Ident = I;
    type Sort = S;
    type Function = F;
    type Error = Error<L, I, S, F>;

    /// Find a sort.
    fn sort(&self, id: &Self::Ident) -> Option<Self::Sort> {
        None
    }

    /// Get the Bool sort, which is the only required sort.
    fn sort_bool(&self) -> GroundSort<Self::Sort> {
        self.sort_bool.clone()
    }
}

impl<L, I: Clone + Hash + Eq + FromSyntaxSymbol, S: Clone + Eq + Hash, F: Clone + Eq + Hash> Server for Client<L, I, S, F>
where L: fmt::Display, I: fmt::Display {
    /// Assert.
    fn assert(&mut self, term: &Term<Self>) -> ExecResult<(), Self::Error> {
        let term = self.downgrade_term(term)?;
        let r = self.internal.assert(&term);
        self.upgrade_result(r)
    }

    /// Check satifiability.
    fn check_sat(&mut self) -> ExecResult<response::CheckSat, Self::Error> {
        let r = self.internal.check_sat();
        self.upgrade_result(r)
    }

    /// Declare a new constant.
    fn declare_const(&mut self, id: &Self::Ident, sort: &GroundSort<Self::Sort>) -> ExecResult<(), Self::Error> {
        panic!("TODO declare_const")
    }

    /// Declare new sort.
    fn declare_sort(&mut self, decl: &SortDeclaration<Self>) -> ExecResult<(), Self::Error> {
        panic!("TODO declare_sort")
    }

    /// Declare new function.
    fn declare_fun(&mut self, id: &Self::Ident, args: &Vec<GroundSort<Self::Sort>>, return_sort: &GroundSort<Self::Sort>) -> ExecResult<(), Self::Error> {
        panic!("TODO declare_fun")
    }

    /// Define previously declared sort.
    fn define_sort(&mut self, id: &Self::Ident, def: &DataTypeDeclaration<Self>) -> ExecResult<(), Self::Error> {
        panic!("TODO define_sort")
    }

    /// Exit the solver.
    fn exit(&mut self) -> ExecResult<(), Self::Error> {
        let r = self.internal.exit();
        self.upgrade_result(r)
    }

    fn get_model(&mut self) -> ExecResult<response::Model<Self>, Self::Error> {
        let model = self.internal.get_model();
        self.upgrade_model(&self.upgrade_result(model)?)
    }

    /// Set the solver's logic.
    fn set_logic(&mut self, logic: &Self::Logic) -> ExecResult<(), Self::Error> {
        let r = self.internal.set_logic(logic);
        self.upgrade_result(r)
    }
}

struct Internal<L, I: FromSyntaxSymbol> {
    sort_bool: GroundSort<I>,
    server: process::Child,
    l: PhantomData<L>
}

impl<L, I: FromSyntaxSymbol> Internal<L, I> {
    fn lexer(&mut self) -> Peekable<Lexer<Decoder<std::io::Bytes<&mut std::process::ChildStdout>>, u32>> {
        let id = self.server.id();
        Lexer::new(Decoder::new_verbose(self.server.stdout.as_mut().unwrap().by_ref().bytes()), id, Cursor::default()).peekable()
    }
}

impl<L, I: Clone + Hash + Eq + FromSyntaxSymbol> Environment for Internal<L, I> {
    type Logic = L;
    type Ident = I;
    type Sort = I;
    type Function = InternalFunction<I>;
    type Error = InternalError<L, I>;

    /// Find a sort.
    fn sort(&self, id: &Self::Ident) -> Option<I> {
        None
    }

    /// Get the Bool sort, which is the only required sort.
    fn sort_bool(&self) -> GroundSort<I> {
        self.sort_bool.clone()
    }
}

impl<L, I: Clone + Hash + Eq + FromSyntaxSymbol> Server for Internal<L, I>
where L: fmt::Display, I: fmt::Display {
    /// Assert.
    fn assert(&mut self, term: &Term<Self>) -> ExecResult<(), Self::Error> {
        write!(self.server.stdin.as_mut().unwrap(), "(assert {})\n", term)?;
        Ok(())
    }

    /// Check satifiability.
    fn check_sat(&mut self) -> ExecResult<response::CheckSat, Self::Error> {
        write!(self.server.stdin.as_mut().unwrap(), "(check-sat)\n")?;
        let ast = syntax::response::CheckSat::parse(&mut self.lexer())?;
        Ok(response::compile_check_sat(self, &ast)?)
    }

    /// Declare a new constant.
    fn declare_const(&mut self, id: &Self::Ident, sort: &GroundSort<Self::Sort>) -> ExecResult<(), Self::Error> {
        panic!("TODO declare_const")
    }

    /// Declare new sort.
    fn declare_sort(&mut self, decl: &SortDeclaration<Self>) -> ExecResult<(), Self::Error> {
        panic!("TODO declare_sort")
    }

    /// Declare new function.
    fn declare_fun(&mut self, id: &Self::Ident, args: &Vec<GroundSort<Self::Sort>>, return_sort: &GroundSort<Self::Sort>) -> ExecResult<(), Self::Error> {
        panic!("TODO declare_fun")
    }

    /// Define previously declared sort.
    fn define_sort(&mut self, id: &Self::Ident, def: &DataTypeDeclaration<Self>) -> ExecResult<(), Self::Error> {
        panic!("TODO define_sort")
    }

    /// Exit the solver.
    fn exit(&mut self) -> ExecResult<(), Self::Error> {
        write!(self.server.stdin.as_mut().unwrap(), "(exit)")?;
        Ok(())
    }

    /// Get model.
    fn get_model(&mut self) -> ExecResult<response::Model<Self>, Self::Error> {
        write!(self.server.stdin.as_mut().unwrap(), "(get-model)\n")?;
        let ast = syntax::response::Model::parse(&mut self.lexer())?;
        Ok(response::compile_model(self, &ast)?)
    }

    /// Set the solver's logic.
    fn set_logic(&mut self, logic: &Self::Logic) -> ExecResult<(), Self::Error> {
        write!(self.server.stdin.as_mut().unwrap(), "(set-logic {})", logic)?;
        Ok(())
    }
}

impl<L, I: Clone + Hash + Eq + FromSyntaxSymbol> Compiler for Internal<L, I> {
    /// Find the ident for the iven syntax symbol.
    fn ident_of_symbol<F: Clone>(&self, sym: &syntax::Symbol<F>) -> Option<I> {
        Some(I::from_syntax(sym))
    }

    /// Find the ident for the given syntax ident.
    fn ident<F: Clone>(&self, id: &syntax::Ident<F>) -> Option<I> {
        if id.indexes.is_empty() {
            self.ident_of_symbol(&id.id)
        } else {
            panic!("TODO indexed idents")
        }
    }

    /// Find the logic with the given id.
    fn logic(&self, id: &Self::Ident) -> Option<Self::Logic> {
        None
    }

    /// Find a function.
    fn function(&self, id: &I) -> Option<InternalFunction<I>> {
        panic!("TODO function")
        // Some(id.clone())
    }
}

struct InternalFunction<I> {
    id: I,
    args: Vec<GroundSort<I>>,
    return_sort: GroundSort<I>
}

impl<I: fmt::Display> fmt::Display for InternalFunction<I> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.id.fmt(f)
    }
}

impl<L, I: Clone + Hash + Eq + FromSyntaxSymbol> Function<Internal<L, I>> for InternalFunction<I> {
    fn arity(&self, _env: &Internal<L, I>) -> (usize, usize) {
        (self.args.len(), self.args.len())
    }

    fn typecheck(&self, _env: &Internal<L, I>, args: &[GroundSort<I>]) -> std::result::Result<GroundSort<I>, TypeCheckError<I>> {
        for i in 0..args.len() {
            if self.args[i] != args[i] {
                return Err(TypeCheckError::Missmatch(i, (&self.args[i]).into()))
            }
        }

        Ok(self.return_sort.clone())
    }
}
