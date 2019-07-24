#![feature(trait_alias)]

extern crate source_span;

use std::fmt;
use std::hash::{Hash, Hasher};
use source_span::Span;

pub mod location;
pub mod error;
pub mod syntax;
pub mod response;
pub mod client;

pub use location::*;
pub use error::{Error, Result};
pub use syntax::lexer::{self, Lexer};
pub use client::Client;

pub type ExecResult<T, E> = std::result::Result<T, E>;

/**
 * Printable list.
 */
pub(crate) struct PList<'a, T: 'a>(&'a Vec<T>);

impl<'a, T: 'a + fmt::Display> fmt::Display for PList<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0.split_first() {
            Some((e, list)) => {
                e.fmt(f)?;
                for e in list.iter() {
                    write!(f, " ")?;
                    e.fmt(f)?
                }
            },
            None => ()
        }

        Ok(())
    }
}

impl<'a, T: 'a + fmt::Debug> fmt::Debug for PList<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0.split_first() {
            Some((e, list)) => {
                e.fmt(f)?;
                for e in list.iter() {
                    write!(f, " ")?;
                    e.fmt(f)?
                }
            },
            None => ()
        }

        Ok(())
    }
}

/// Evaluation context.
/// Maps each variable to its sort.
pub struct Context<'p, E: 'p + Environment> {
    parent: Option<&'p Context<'p, E>>,
    offset: usize,
    locals: Vec<(E::Ident, GroundSort<E::Sort>)>
}

impl<'p, E: 'p + Environment> Context<'p, E> {
    /// Create a new empty context.
    pub fn new() -> Context<'p, E> {
        Context {
            parent: None,
            offset: 0,
            locals: Vec::new()
        }
    }

    pub fn from(parent: &'p Context<'p, E>) -> Context<'p, E> {
        Context {
            parent: Some(parent),
            offset: parent.offset+parent.locals.len(),
            locals: Vec::new()
        }
    }

    pub fn find(&self, id: &E::Ident) -> Option<(usize, &GroundSort<E::Sort>)> {
        for (local_index, (xid, sort)) in self.locals.iter().enumerate().rev() {
            if id == xid {
                return Some((self.offset+local_index, sort))
            }
        }

        match self.parent {
            Some(parent) => parent.find(id),
            None => None
        }
    }

    /// Get the sort of the given variable (identified with its index).
    /// Panics if the variable is not defined in the context.
    pub fn sort(&self, x: usize) -> &GroundSort<E::Sort> {
        if x < self.offset {
            self.parent.unwrap().sort(x)
        } else {
            &self.locals[x-self.offset].1
        }
    }

    /// Push a new sort on the stack and return the unique identifier of the
    /// corresponding variable.
    fn push(&mut self, id: &E::Ident, sort: &GroundSort<E::Sort>) -> usize {
        let local_index = self.locals.len();
        self.locals.push((id.clone(), sort.clone()));
        self.offset + local_index
    }
}

/// A term.
pub enum Term<E: Environment> {
    Const(E::Constant),
    Var {
        /// unique identified in the current variable environment.
        index: usize,

        /// non-unique identifier.
        id: E::Ident,

        /// sort
        sort: GroundSort<E::Sort>
    },
    Let {
        bindings: Vec<Binding<E>>,
        body: Box<Term<E>>
    },
    Forall {
        vars: Vec<SortedVar<E>>,
        body: Box<Term<E>>
    },
    Exists {
        vars: Vec<SortedVar<E>>,
        body: Box<Term<E>>
    },
    Match {
        term: Box<Term<E>>,
        cases: Vec<MatchCase<E>>
    },
    Apply {
        fun: E::Function,
        args: Box<Vec<Term<E>>>,
        sort: GroundSort<E::Sort>
    }
}

impl<E: Environment> Term<E> {
    pub fn apply(fun: E::Function, args: Vec<Term<E>>, sort: GroundSort<E::Sort>) -> Term<E> {
        Term::Apply {
            fun: fun,
            args: Box::new(args),
            sort: sort
        }
    }

    pub fn sort(&self, env: &E) -> GroundSort<E::Sort> {
        use Term::*;
        match self {
            Const(c) => env.const_sort(c),
            Var { sort, .. } => sort.clone(),
            Let { body, .. } => {
                body.sort(env)
            },
            Forall { .. } => env.sort_bool(),
            Exists { .. } => env.sort_bool(),
            Match { term, .. } => term.sort(env),
            Apply { sort, .. } => sort.clone()
        }
    }
}

impl<E: Environment> From<Term<E>> for Located<syntax::Term> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn from(term: Term<E>) -> Self {
        use self::Term::*;
        let kind = match term {
            Const(c) => syntax::Term::Apply {
                id: Located::new(syntax::Symbol::format(c), Span::default()).into(),
                args: Box::new(Vec::new())
            },
            Var { id, .. } => syntax::Term::Ident(Located::new(syntax::Symbol::format(id), Span::default()).into(),),
            Let { bindings, body } => {
                syntax::Term::Let {
                    bindings: bindings.into_iter().map(|b| b.into()).collect(),
                    body: Box::new((*body).into())
                }
            },
            Forall { vars, body } => {
                syntax::Term::Forall {
                    vars: vars.into_iter().map(|v| v.into()).collect(),
                    body: Box::new((*body).into())
                }
            },
            Exists { vars, body } => {
                syntax::Term::Exists {
                    vars: vars.into_iter().map(|v| v.into()).collect(),
                    body: Box::new((*body).into())
                }
            },
            Match { term, cases } => {
                syntax::Term::Match {
                    term: Box::new((*term).into()),
                    cases: cases.into_iter().map(|c| c.into()).collect()
                }
            },
            Apply { fun, args, .. } => {
                syntax::Term::Apply {
                    id: Located::new(syntax::Symbol::format(fun), Span::default()).into(),
                    args: Box::new(args.into_iter().map(|a| a.into()).collect())
                }
            }
        };

        Located::new(kind, Span::default())
    }
}

impl<E: Environment> fmt::Display for Term<E> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Term::*;
        match self {
            Const(c) => write!(f, "{}", c),
            Var { id, .. } => write!(f, "{}", id),
            Let { bindings, body } => {
                write!(f, "(let ({}) {})", PList(bindings), body)
            },
            Forall { vars, body } => {
                write!(f, "(forall ({}) {})", PList(vars), body)
            },
            Exists { vars, body } => {
                write!(f, "(exists ({}) {})", PList(vars), body)
            },
            Match { term, cases } => {
                write!(f, "(match {} ({}))", term, PList(cases))
            },
            Apply { fun, args, .. } => {
                if args.is_empty() {
                    write!(f, "{}", fun)
                } else {
                    write!(f, "({} {})", fun, PList(args))
                }
            }
        }
    }
}

pub struct MatchCase<E: Environment> {
    pub pattern: Pattern<E>,
    pub term: Box<Term<E>>
}

impl<E: Environment> From<MatchCase<E>> for Located<syntax::MatchCase> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn from(case: MatchCase<E>) -> Self {
        Located::new(syntax::MatchCase {
            pattern: case.pattern.into(),
            term: Box::new((*case.term).into())
        }, Span::default())
    }
}

impl<E: Environment> fmt::Display for MatchCase<E> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.pattern, self.term)
    }
}

pub enum Pattern<E: Environment> {
    Var(E::Ident),
    Cons {
        constructor: E::Function,
        args: Vec<E::Ident>
    }
}

impl<E: Environment> From<Pattern<E>> for Located<syntax::Pattern> where E::Function: fmt::Display, E::Ident: fmt::Display {
    fn from(pattern: Pattern<E>) -> Self {
        let ast = match pattern {
            Pattern::Var(id) => {
                syntax::Pattern {
                    id: Located::new(syntax::Symbol::format(id), Span::default()),
                    args: Vec::new()
                }
            },
            Pattern::Cons { constructor, args } => {
                syntax::Pattern {
                    id: Located::new(syntax::Symbol::format(constructor), Span::default()),
                    args: args.into_iter().map(|a| Located::new(syntax::Symbol::format(a), Span::default())).collect()
                }
            }
        };

        Located::new(ast, Span::default())
    }
}

impl<E: Environment> fmt::Display for Pattern<E> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Pattern::Var(id) => {
                write!(f, "{}", id)
            },
            Pattern::Cons { constructor, args } => {
                if args.is_empty() {
                    write!(f, "{}", constructor)
                } else {
                    write!(f, "({} {})", constructor, PList(args))
                }
            }
        }
    }
}

/// Variable binding.
pub struct Binding<E: Environment> {
    pub id: E::Ident,
    pub value: Box<Term<E>>
}

impl<E: Environment> From<Binding<E>> for Located<syntax::Binding> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn from(binding: Binding<E>) -> Self {
        Located::new(syntax::Binding {
            id: Located::new(syntax::Symbol::format(binding.id), Span::default()).into(),
            value: Box::new((*binding.value).into())
        }, Span::default())
    }
}

impl<E: Environment> fmt::Display for Binding<E> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.id, self.value)
    }
}

/// Sorted variable.
pub struct SortedVar<E: Environment> {
    pub id: E::Ident,
    pub sort: GroundSort<E::Sort>
}

impl<E: Environment> From<SortedVar<E>> for Located<syntax::SortedVar> where E::Ident: fmt::Display, E::Sort: fmt::Display {
    fn from(var: SortedVar<E>) -> Self {
        Located::new(syntax::SortedVar {
            id: Located::new(syntax::Symbol::format(var.id), Span::default()),
            sort: var.sort.into()
        }, Span::default())
    }
}

impl<E: Environment> fmt::Display for SortedVar<E> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Sort: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.id, self.sort)
    }
}

/// A ground sort is a sort fully applied (arity 0).
#[derive(PartialEq, Eq)]
pub struct GroundSort<T> {
    pub sort: T,
    pub parameters: Vec<GroundSort<T>>
}

impl<T> GroundSort<T> {
    pub fn new(sort: T) -> GroundSort<T> {
        GroundSort {
            sort: sort,
            parameters: Vec::new()
        }
    }
}

impl<T> From<GroundSort<T>> for Located<syntax::Sort> where T: fmt::Display {
    fn from(sort: GroundSort<T>) -> Self {
        Located::new(syntax::Sort {
            id: Located::new(syntax::Symbol::format(sort.sort), Span::default()).into(),
            parameters: sort.parameters.into_iter().map(|p| p.into()).collect()
        }, Span::default())
    }
}

impl<T: fmt::Display> fmt::Display for GroundSort<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.parameters.is_empty() {
            self.sort.fmt(f)
        } else {
            write!(f, "{} {}", self.sort, PList(&self.parameters))
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for GroundSort<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.parameters.is_empty() {
            self.sort.fmt(f)
        } else {
            write!(f, "{:?} {:?}", self.sort, PList(&self.parameters))
        }
    }
}

impl<T: Clone> Clone for GroundSort<T> {
    fn clone(&self) -> GroundSort<T> {
        GroundSort {
            sort: self.sort.clone(),
            parameters: self.parameters.clone()
        }
    }
}

impl<T: Hash> Hash for GroundSort<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.sort.hash(state);
        for p in self.parameters.iter() {
            p.hash(state)
        }
    }
}

/// A ground sort with sort parameter variables, used in a datatype declaration.
/// Parameters are identified with their index.
pub enum AbstractGroundSort<T> {
    Sort {
        sort: T,
        parameters: Vec<AbstractGroundSort<T>>
    },
    Param(usize)
}

impl<T: Clone + PartialEq> AbstractGroundSort<T> {
    /// Check that the given ground sort matches this abstract ground sort with the given
    /// type parameter context.
    /// If it does not match, return the expected sort. Since all the type parameters may not have
    /// been resolved when a missmatch is detected, the expected sort is abstract.
    pub fn typecheck(&self, context: &mut [Option<GroundSort<T>>], arg: &GroundSort<T>) -> std::result::Result<(), AbstractGroundSort<T>> {
        match self {
            AbstractGroundSort::Sort { sort, parameters } => {
                if *sort == arg.sort {
                    for (i, p) in arg.parameters.iter().enumerate() {
                        parameters[i].typecheck(context, p)?
                    }

                    Ok(())
                } else {
                    Err(self.clone())
                }
            },
            AbstractGroundSort::Param(i) => {
                match &context[*i] {
                    Some(expected) => {
                        if *expected == *arg {
                            Ok(())
                        } else {
                            Err(expected.into())
                        }
                    },
                    None => {
                        context[*i] = Some(arg.clone());
                        Ok(())
                    }
                }
            }
        }
    }

    /// Try to instanciate the abstract ground sort with the given parameters.
    pub fn instanciate(&self, context: &[GroundSort<T>]) -> std::result::Result<GroundSort<T>, ()> {
        match self {
            AbstractGroundSort::Param(i) => {
                if let Some(sort) = context.get(*i) {
                    Ok(sort.clone())
                } else {
                    Err(())
                }
            },
            AbstractGroundSort::Sort { sort, parameters } => {
                let mut instanciated_parameters = Vec::with_capacity(parameters.len());
                for p in parameters {
                    instanciated_parameters.push(p.instanciate(context)?);
                }

                Ok(GroundSort {
                    sort: sort.clone(),
                    parameters: instanciated_parameters
                })
            }
        }
    }
}

impl<T: Clone> Clone for AbstractGroundSort<T> {
    fn clone(&self) -> AbstractGroundSort<T> {
        use AbstractGroundSort::*;
        match self {
            Sort { sort, parameters } => Sort {
                sort: sort.clone(),
                parameters: parameters.clone()
            },
            Param(index) => Param(*index)
        }
    }
}

impl<'a, T: Clone> From<&'a GroundSort<T>> for AbstractGroundSort<T> {
    fn from(sort: &'a GroundSort<T>) -> AbstractGroundSort<T> {
        AbstractGroundSort::Sort {
            sort: sort.sort.clone(),
            parameters: sort.parameters.iter().map(|p| p.into()).collect()
        }
    }
}

impl<T: fmt::Display> fmt::Display for AbstractGroundSort<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AbstractGroundSort::Sort { sort, parameters } => {
                if parameters.is_empty() {
                    sort.fmt(f)
                } else {
                    write!(f, "{} {}", sort, PList(&parameters))
                }
            },
            AbstractGroundSort::Param(x) => {
                write!(f, "#{}", x)
            }
        }

    }
}

/// A structure able to replace unresolved symbols to return a new type T.
trait Solvable<T, E: Environment> {
    fn resolve(self, env: &E) -> T;
}

impl<E: Environment> Solvable<E::Sort, E> for Located<E::Ident> {
    fn resolve(self, env: &E) -> E::Sort {
        match env.sort(&self.into_inner()) {
            Some(sort) => sort,
            None => panic!("broken sort reference!")
        }
    }
}

impl<E: Environment, U, T: Solvable<U, E>> Solvable<AbstractGroundSort<U>, E> for AbstractGroundSort<T> {
    fn resolve(self, env: &E) -> AbstractGroundSort<U> {
        use AbstractGroundSort::*;
        match self {
            Sort { sort, mut parameters } => {
                let solved_sort = sort.resolve(env);
                let mut solved_parameters : Vec<AbstractGroundSort<U>> = Vec::with_capacity(parameters.len());
                for p in parameters.drain(..) {
                    solved_parameters.push(p.resolve(env));
                }

                Sort {
                    sort: solved_sort,
                    parameters: solved_parameters
                }
            },
            Param(x) => Param(x)
        }
    }
}

/// Data type declaration.
pub struct UnresolvedDataTypeDeclaration<E: Environment> {
    pub parameters: Vec<E::Ident>,
    pub constructors: Vec<UnresolvedConstructorDeclaration<E>>
}

impl<E: Environment> UnresolvedDataTypeDeclaration<E> {
    fn resolve(mut self, env: &E) -> DataTypeDeclaration<E> {
        let mut constructors = Vec::with_capacity(self.constructors.len());
        for unresolved_decl in self.constructors.drain(..) {
            constructors.push(unresolved_decl.resolve(env))
        }

        DataTypeDeclaration {
            parameters: self.parameters,
            constructors: constructors
        }
    }
}

/// Data type declaration.
pub struct DataTypeDeclaration<E: Environment> {
    pub parameters: Vec<E::Ident>,
    pub constructors: Vec<ConstructorDeclaration<E>>
}

impl<E: Environment> Clone for DataTypeDeclaration<E> where E::Ident: Clone, E::Sort: Clone {
    fn clone(&self) -> DataTypeDeclaration<E> {
        DataTypeDeclaration {
            parameters: self.parameters.clone(),
            constructors: self.constructors.clone()
        }
    }
}

// Unresolved constructor declaration.
pub struct UnresolvedConstructorDeclaration<E: Environment> {
    /// Constructor identifier.
    pub id: E::Ident,

    /// Selectors.
    pub selectors: Vec<UnresolvedSelectorDeclaration<E>>
}

impl<E: Environment> UnresolvedConstructorDeclaration<E> {
    fn resolve(mut self, env: &E) -> ConstructorDeclaration<E> {
        let mut selectors = Vec::with_capacity(self.selectors.len());
        for unresolved_sel in self.selectors.drain(..) {
            selectors.push(unresolved_sel.resolve(env))
        }

        ConstructorDeclaration {
            id: self.id,
            selectors: selectors
        }
    }
}

// Constructor declaration.
pub struct ConstructorDeclaration<E: Environment> {
    /// Constructor identifier.
    pub id: E::Ident,

    /// Selectors.
    pub selectors: Vec<SelectorDeclaration<E>>
}

impl<E: Environment> ConstructorDeclaration<E> {
    pub fn simple<Id: Into<E::Ident>>(id: Id) -> ConstructorDeclaration<E> {
        ConstructorDeclaration {
            id: id.into(),
            selectors: Vec::new()
        }
    }
}

impl<E: Environment> Clone for ConstructorDeclaration<E> where E::Ident: Clone, E::Sort: Clone {
    fn clone(&self) -> ConstructorDeclaration<E> {
        ConstructorDeclaration {
            id: self.id.clone(),
            selectors: self.selectors.clone()
        }
    }
}

/// Selector declaration, where sorts are unresolved references.
pub struct UnresolvedSelectorDeclaration<E: Environment> {
    /// Selector identifier.
    pub id: E::Ident,

    /// Sort reference.
    pub sort: AbstractGroundSort<Located<E::Ident>>
}

impl<E: Environment> UnresolvedSelectorDeclaration<E> {
    fn resolve(self, env: &E) -> SelectorDeclaration<E> {
        SelectorDeclaration {
            id: self.id,
            sort: self.sort.resolve(env)
        }
    }
}

/// Selector declaration.
pub struct SelectorDeclaration<E: Environment> {
    /// Selector identifier.
    pub id: E::Ident,

    /// Sort reference.
    pub sort: AbstractGroundSort<E::Sort>
}

impl<E: Environment> Clone for SelectorDeclaration<E> where E::Ident: Clone, E::Sort: Clone {
    fn clone(&self) -> SelectorDeclaration<E> {
        SelectorDeclaration {
            id: self.id.clone(),
            sort: self.sort.clone()
        }
    }
}

/// Sort declaration.
pub struct SortDeclaration<E: Environment> {
    /// Sort name.
    pub id: E::Ident,

    /// arity.
    pub arity: usize
}

/// SMT2-lib command.
pub enum Command<E: Environment> {
    /// Assertion.
    Assert(Term<E>),

    /// Check sat.
    CheckSat,

    /// Declare a cosntant.
    DeclareConst(E::Ident, GroundSort<E::Sort>),

    /// Declare new datatypes.
    /// The `declare-datatype` is desigarized into `declare-datatypes`.
    DeclareDatatypes(Vec<SortDeclaration<E>>, Vec<UnresolvedDataTypeDeclaration<E>>),

    /// Declare a new uninterpreted function.
    DeclareFun(E::Ident, Vec<GroundSort<E::Sort>>, GroundSort<E::Sort>),

    /// Exit the program.
    Exit,

    /// Get a model.
    GetModel,

    // SetInfo()
    /// Set the solver logic.
    SetLogic(E::Logic)
}

impl<E: Server> Command<E> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    /// Execute the command on the given environment.
    pub fn exec(self, env: &mut E) -> ExecResult<(), E::Error> {
        use Command::*;
        match self {
            Assert(term) => env.assert(&term)?,
            CheckSat => {
                use response::CheckSat::*;
                match env.check_sat()? {
                    Sat => println!("sat"),
                    Unsat => println!("unsat"),
                    Unknown => println!("unknown")
                }
            },
            DeclareConst(id, sort) => env.declare_const(&id, &sort)?,
            DeclareDatatypes(mut sort_decls, mut decls) => {
                let mut ids = Vec::with_capacity(sort_decls.len());
                for sort_decl in sort_decls.drain(..) {
                    env.declare_sort(&sort_decl)?;
                    ids.push(sort_decl.id);
                }

                let mut i = 0;
                for unresolved_decl in decls.drain(..) {
                    // at this point, sorts should be declared so we can resolve the sort references.
                    let decl = unresolved_decl.resolve(env);
                    env.define_sort(&ids[i], &decl)?;
                    i += 1;
                }
            },
            DeclareFun(id, args, return_sort) => env.declare_fun(&id, &args, &return_sort)?,
            Exit => env.exit()?,
            GetModel => {
                let model = env.get_model()?;
                let ast: Located<syntax::response::Model> = model.into();
                println!("{}", syntax::PrettyPrint(&ast));
            },
            SetLogic(logic) => env.set_logic(&logic)?
        }

        Ok(())
    }
}

/// Functions type check errors.
pub enum TypeCheckError<T> {
    /// The given function argument (given by it's index) has a wrong type.
    /// The second parameter is the expected sort of the argument.
    Missmatch(usize, AbstractGroundSort<T>),

    /// There is an ambiguity on the given type parameter (given by it's index).
    /// To solve the ambiguity, the user should use the `(as <term> <sort>)` term construction.
    Ambiguity(usize)
}

/// SMT2-lib function.
pub trait Function<E: Environment> {
    /// Return the arity of the function.
    /// It is assumed that, for a given environment, the result of this function will always be
    /// the same.
    fn arity(&self, env: &E) -> (usize, usize);

    /// Check the type of the given arguments, and return the ground sort of the function's
    /// output with those arguments.
    /// It can be assumed that the number of arguments lies in the range given by `arity`.
    fn typecheck(&self, env: &E, args: &[GroundSort<E::Sort>]) -> std::result::Result<GroundSort<E::Sort>, TypeCheckError<E::Sort>>;
}

/// SMT2-lib solver environment.
pub trait Environment: Sized {
    type Logic;
    type Constant: Clone + PartialEq;
    type Ident: Clone + PartialEq;
    type Sort: Clone + PartialEq;
    type Function;
    type Error;

    /// Find a sort.
    fn sort(&self, id: &Self::Ident) -> Option<Self::Sort>;

    /// Get the Bool sort, which is the only required sort.
    fn sort_bool(&self) -> GroundSort<Self::Sort>;

    /// Get the sort of the given constant.
    fn const_sort(&self, cst: &Self::Constant) -> GroundSort<Self::Sort>;
}

pub trait Compiler: Environment {
    /// Find the ident for the iven syntax symbol.
    fn ident_of_symbol(&self, sym: &syntax::Symbol) -> Option<Self::Ident>;

    /// Find the ident for the given syntax ident.
    fn ident(&self, id: &syntax::Ident) -> Option<Self::Ident>;

    /// Find the logic with the given id.
    fn logic(&self, id: &Self::Ident) -> Option<Self::Logic>;

    /// Find the constant with the given id.
    fn constant(&self, id: &Self::Ident) -> Option<Self::Constant>;

    /// Find a function.
    fn function(&self, id: &Self::Ident) -> Option<Self::Function>;
}

pub trait Server: Environment {
    /// Assert.
    fn assert(&mut self, term: &Term<Self>) -> ExecResult<(), Self::Error>;

    /// Check satifiability.
    fn check_sat(&mut self) -> ExecResult<response::CheckSat, Self::Error>;

    /// Get model.
    fn get_model(&mut self) -> ExecResult<response::Model<Self>, Self::Error>;

    /// Declare a new constant.
    fn declare_const(&mut self, id: &Self::Ident, sort: &GroundSort<Self::Sort>) -> ExecResult<(), Self::Error>;

    /// Declare new sort.
    fn declare_sort(&mut self, decl: &SortDeclaration<Self>) -> ExecResult<(), Self::Error>;

    /// Declare new function.
    fn declare_fun(&mut self, id: &Self::Ident, args: &Vec<GroundSort<Self::Sort>>, return_sort: &GroundSort<Self::Sort>) -> ExecResult<(), Self::Error>;

    /// Define previously declared sort.
    fn define_sort(&mut self, id: &Self::Ident, def: &DataTypeDeclaration<Self>) -> ExecResult<(), Self::Error>;

    /// Exit the solver.
    fn exit(&mut self) -> ExecResult<(), Self::Error>;

    /// Set the solver's logic.
    fn set_logic(&mut self, logic: &Self::Logic) -> ExecResult<(), Self::Error>;
}

pub fn compile_term<E: Compiler>(env: &E, ctx: &Context<E>, term: &Located<syntax::Term>) -> Result<Term<E>, E> where <E as Environment>::Function: Function<E> {
    let loc = term.span().clone();
    match term.as_ref() {
        syntax::Term::Ident(id) => {
            let id = compile_ident(env, &id)?;
            match ctx.find(&id) {
                Some((index, sort)) => {
                    Ok(Term::Var {
                        index: index,
                        id: id,
                        sort: sort.clone()
                    })
                },
                None => {
                    match compile_function(env, &id, &loc) {
                        Ok(fun) => {
                            let (arity_min, arity_max) = fun.arity(env);
                            if arity_min > 0 {
                                Err(Error::WrongNumberOfArguments(arity_min, arity_max, 0).at(loc))
                            } else {
                                let sort = match fun.typecheck(env, &[]) {
                                    Ok(sort) => sort,
                                    Err(TypeCheckError::Missmatch(i, expected_type)) => panic!("argument type missmatch on constant!"),
                                    Err(TypeCheckError::Ambiguity(_)) => {
                                        return Err(Error::TypeAmbiguity.at(loc))
                                    }
                                };
                                Ok(Term::Apply {
                                    fun: fun,
                                    args: Box::new(Vec::new()),
                                    sort: sort
                                })
                            }
                        },
                        Err(e) => {
                            if let Some(cst) = env.constant(&id) {
                                Ok(Term::Const(cst))
                            } else {
                                Err(e)
                            }
                        }
                    }
                }
            }
        },
        syntax::Term::Let { bindings, body } => {
            let mut compiled_bindings = Vec::with_capacity(bindings.len());
            for binding in bindings.iter() {
                compiled_bindings.push(compile_binding(env, ctx, &binding)?)
            }

            let body = compile_term(env, ctx, &body)?;

            Ok(Term::Let {
                bindings: compiled_bindings,
                body: Box::new(body)
            })
        },
        syntax::Term::Forall { vars, body } => {
            let mut compiled_vars = Vec::with_capacity(vars.len());
            let mut new_ctx = Context::from(ctx);
            for var in vars.iter() {
                let compiled_var = compile_sorted_var(env, &var)?;
                new_ctx.push(&compiled_var.id, &compiled_var.sort);
                compiled_vars.push(compiled_var)
            }
            let body = compile_term(env, &new_ctx, &body)?;

            Ok(Term::Forall {
                vars: compiled_vars,
                body: Box::new(body)
            })
        },
        syntax::Term::Exists { vars, body } => {
            let mut compiled_vars = Vec::with_capacity(vars.len());
            let mut new_ctx = Context::from(ctx);
            for var in vars.iter() {
                let compiled_var = compile_sorted_var(env, &var)?;
                new_ctx.push(&compiled_var.id, &compiled_var.sort);
                compiled_vars.push(compiled_var)
            }
            let body = compile_term(env, &new_ctx, &body)?;

            Ok(Term::Exists {
                vars: compiled_vars,
                body: Box::new(body)
            })
        },
        syntax::Term::Match { .. } => {
            panic!("TODO compile match")
        },
        syntax::Term::Apply { id, args } => {
            let id_loc = id.span();
            let id = compile_ident(env, &id)?;
            match compile_function(env, &id, &id_loc) {
                Ok(fun) => {
                    let (arity_min, arity_max) = fun.arity(env);
                    if args.len() < arity_min || args.len() > arity_max {
                        Err(Error::WrongNumberOfArguments(arity_min, arity_max, args.len()).at(loc))
                    } else {
                        let mut compiled_args = Vec::with_capacity(args.len());
                        let mut args_types = Vec::with_capacity(args.len());
                        for arg in args.iter() {
                            let term = compile_term(env, ctx, &arg)?;
                            args_types.push(term.sort(env));
                            compiled_args.push(term);
                        }

                        // let expected_type = fun.sort(env, i).unwrap();
                        // let given_type = term.sort(env, ctx);
                        // if given_type != expected_type {
                        //     return Err(Error::TypeMissmatch(expected_type, given_type).at(arg.location().clone()))
                        // }

                        let sort = match fun.typecheck(env, &args_types) {
                            Ok(sort) => sort,
                            Err(TypeCheckError::Missmatch(i, expected_type)) => {
                                return Err(Error::TypeMissmatch(expected_type, args_types[i].clone()).at(args[i].span()))
                            },
                            Err(TypeCheckError::Ambiguity(_)) => {
                                return Err(Error::TypeAmbiguity.at(loc))
                            }
                        };

                        Ok(Term::Apply {
                            fun: fun,
                            args: Box::new(compiled_args),
                            sort: sort
                        })
                    }
                },
                Err(e) => {
                    if let Some(cst) = env.constant(&id) {
                        Ok(Term::Const(cst))
                    } else {
                        Err(e)
                    }
                }
            }
        },
        syntax::Term::Coerce { term, sort } => {
            panic!("TODO compile type coercion")
        }
    }
}

pub fn compile_binding<E: Compiler>(env: &E, ctx: &Context<E>, sym: &Located<syntax::Binding>) -> Result<Binding<E>, E> where <E as Environment>::Function: Function<E> {
    let id = compile_symbol(env, &sym.id)?;
    let value = compile_term(env, ctx, &sym.value)?;

    Ok(Binding {
        id: id,
        value: Box::new(value)
    })
}

pub fn compile_sorted_var<E: Compiler>(env: &E, var: &Located<syntax::SortedVar>) -> Result<SortedVar<E>, E> where <E as Environment>::Function: Function<E> {
    let id = compile_symbol(env, &var.id)?;
    let sort = compile_sort(env, &var.sort)?;

    Ok(SortedVar {
        id: id,
        sort: sort
    })
}

pub fn compile_symbol<E: Compiler>(env: &E, sym: &Located<syntax::Symbol>) -> Result<E::Ident, E> where <E as Environment>::Function: Function<E> {
    match env.ident_of_symbol(sym) {
        Some(id) => Ok(id),
        None => Err(Error::InvalidSymbol(sym.clone().into_inner()).at(sym.span()))
    }
}

pub fn compile_ident<E: Compiler>(env: &E, id: &Located<syntax::Ident>) -> Result<E::Ident, E> where <E as Environment>::Function: Function<E> {
    match env.ident(id) {
        Some(id) => Ok(id),
        None => Err(Error::InvalidIdent(id.clone().into_inner()).at(id.span()))
    }
}

pub fn compile_function<E: Compiler>(env: &E, id: &E::Ident, loc: &Span) -> Result<E::Function, E> where <E as Environment>::Function: Function<E> {
    match env.function(&id) {
        Some(f) => Ok(f),
        None => Err(Error::UnknownFunction(id.clone()).at(loc.clone()))
    }
}

pub fn compile_sort<E: Compiler>(env: &E, sort: &Located<syntax::Sort>) -> Result<GroundSort<E::Sort>, E> where <E as Environment>::Function: Function<E> {
    let id = compile_ident(env, &sort.id)?;
    match env.sort(&id) {
        Some(s) => {
            let mut parameters : Vec<GroundSort<E::Sort>> = Vec::with_capacity(sort.parameters.len());
            for p in sort.parameters.iter() {
                parameters.push(compile_sort(env, p)?);
            }

            Ok(GroundSort {
                sort: s,
                parameters: parameters
            })
        },
        None => Err(Error::UnknownSort.at(sort.span()))
    }
}

pub fn compile_sort_declaration<E: Compiler>(env: &E, decl: &Located<syntax::SortDeclaration>) -> Result<SortDeclaration<E>, E> where <E as Environment>::Function: Function<E> {
    let id = compile_symbol(env, &decl.id)?;
    if *decl.arity >= 0 {
        let arity = *decl.arity as usize;
        Ok(SortDeclaration {
            id: id,
            arity: arity
        })
    } else {
        Err(Error::NegativeArity.at(decl.span()))
    }
}

pub fn compile_datatype_declaration<E: Compiler>(env: &E, decl: &Located<syntax::DataTypeDeclaration>) -> Result<UnresolvedDataTypeDeclaration<E>, E> where <E as Environment>::Function: Function<E> {
    let mut parameters = Vec::with_capacity(decl.parameters.len());
    for param in decl.parameters.iter() {
        parameters.push(compile_symbol(env, &param)?)
    }

    let mut constructors = Vec::with_capacity(decl.constructors.len());
    for cons_decl in decl.constructors.iter() {
        constructors.push(compile_constructor_declaration(env, cons_decl, &parameters)?)
    }

    Ok(UnresolvedDataTypeDeclaration {
        parameters: parameters,
        constructors: constructors
    })
}

pub fn compile_constructor_declaration<E: Compiler>(env: &E, decl: &Located<syntax::ConstructorDeclaration>, sort_parameters: &Vec<E::Ident>) -> Result<UnresolvedConstructorDeclaration<E>, E> where <E as Environment>::Function: Function<E> {
    let id = compile_symbol(env, &decl.id)?;
    let mut selectors = Vec::with_capacity(decl.selectors.len());
    for sel_decl in decl.selectors.iter() {
        selectors.push(compile_selector_declaration(env, sel_decl, sort_parameters)?)
    }

    Ok(UnresolvedConstructorDeclaration {
        id: id,
        selectors: selectors
    })
}

fn sort_parameter_index<I: PartialEq>(params: &Vec<I>, id: &I) -> Option<usize> {
    for i in 0..params.len() {
        if params[i] == *id {
            return Some(i)
        }
    }

    None
}

pub fn compile_sort_ref<E: Compiler>(env: &E, sort: &Located<syntax::Sort>, sort_parameters: &Vec<E::Ident>) -> Result<AbstractGroundSort<Located<E::Ident>>, E> where <E as Environment>::Function: Function<E> {
    let id = compile_ident(env, &sort.id)?;

    match sort_parameter_index(&sort_parameters, &id) {
        Some(index) => {
            Ok(AbstractGroundSort::Param(index))
        },
        None => {
            let mut parameters : Vec<AbstractGroundSort<Located<E::Ident>>> = Vec::with_capacity(sort.parameters.len());
            for p in sort.parameters.iter() {
                parameters.push(compile_sort_ref(env, p, sort_parameters)?);
            }

            Ok(AbstractGroundSort::Sort {
                sort: Located::new(id, sort.id.span()),
                parameters: parameters
            })
        }
    }
}

pub fn compile_selector_declaration<E: Compiler>(env: &E, decl: &Located<syntax::SelectorDeclaration>, sort_parameters: &Vec<E::Ident>) -> Result<UnresolvedSelectorDeclaration<E>, E> where <E as Environment>::Function: Function<E> {
    let id = compile_symbol(env, &decl.id)?;
    let sort_ref = compile_sort_ref(env, &decl.sort, sort_parameters)?;
    Ok(UnresolvedSelectorDeclaration {
        id: id,
        sort: sort_ref
    })
}

pub fn compile<E: Compiler>(env: &E, cmd: &Located<syntax::Command>) -> Result<Command<E>, E> where <E as Environment>::Function: Function<E> {
    let loc = cmd.span();
    let mut ctx = Context::new();
    match cmd.as_ref() {
        syntax::Command::Assert(term) => {
            Ok(Command::Assert(compile_term(env, &mut ctx, &term)?))
        },
        syntax::Command::CheckSat => {
            Ok(Command::CheckSat)
        },
        syntax::Command::DeclareConst(id, sort) => {
            let id = compile_symbol(env, &id)?;
            let sort = compile_sort(env, &sort)?;
            Ok(Command::DeclareConst(id, sort))
        },
        syntax::Command::DeclareDatatype(id, decl) => {
            let sort_decl = SortDeclaration {
                id: compile_symbol(env, &id)?,
                arity: 0
            };

            let decl = compile_datatype_declaration(env, &decl)?;

            Ok(Command::DeclareDatatypes(vec![sort_decl], vec![decl]))
        },
        syntax::Command::DeclareDatatypes(sort_decls, decls) => {
            let mut compiled_sort_decls = Vec::with_capacity(sort_decls.len());
            for decl in sort_decls.iter() {
                compiled_sort_decls.push(compile_sort_declaration(env, &decl)?)
            }

            let mut compiled_decls = Vec::with_capacity(decls.len());
            for decl in decls.iter() {
                compiled_decls.push(compile_datatype_declaration(env, &decl)?)
            }

            Ok(Command::DeclareDatatypes(compiled_sort_decls, compiled_decls))
        },
        syntax::Command::DeclareFun(id, args, return_sort) => {
            let id = compile_symbol(env, &id)?;
            let mut compiled_args = Vec::with_capacity(args.len());
            for arg in args.iter() {
                compiled_args.push(compile_sort(env, &arg)?)
            }
            let return_sort = compile_sort(env, &return_sort)?;

            Ok(Command::DeclareFun(id, compiled_args, return_sort))
        },
        syntax::Command::Exit => {
            Ok(Command::Exit)
        },
        syntax::Command::GetModel => {
            Ok(Command::GetModel)
        },
        syntax::Command::SetInfo(_) => {
            panic!("set-info")
        },
        syntax::Command::SetLogic(id) => {
            let id = compile_symbol(env, &id)?;
            match env.logic(&id) {
                Some(logic) => Ok(Command::SetLogic(logic)),
                None => Err(Error::UnknownLogic.at(loc))
            }
        }
    }
}
