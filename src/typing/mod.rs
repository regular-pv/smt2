use std::marker::PhantomData;
use std::convert::AsRef;
use std::fmt;
use ena::unify::{UnifyKey, UnifyValue, UnificationTable, InPlace};
use source_span::Span;
use crate::{
    Environment,
    Sort,
    SortedWith,
    GroundSort,
    Term,
    Pattern
};

mod error;

pub use error::*;

#[derive(Debug, Clone)]
pub enum Type<S: Sort> {
    None,
    Some(GroundSort<S>)
}

impl<S: Sort> UnifyValue for Type<S> {
    type Error = Error<S>;

    fn unify_values(a: &Type<S>, b: &Type<S>) -> Result<Type<S>, S> {
        panic!("TODO unify values")
    }
}

pub struct Typed<T: Typable> {
    type_ref: TypeRef<T::Sort>,
    typ: Type<T::Sort>,
    span: Span,
    value: T
}

impl<T: Typable> Typed<T> {
    pub fn new(t: T, span: Span, sort: GroundSort<T::Sort>) -> Typed<T> {
        Typed {
            type_ref: TypeRef::Var(TypeVar::new(0)),
            typ: Type::Some(sort),
            span: span,
            value: t
        }
    }

    pub fn untyped(t: T, span: Span) -> Typed<T> {
        Typed {
            type_ref: TypeRef::Var(TypeVar::new(0)),
            typ: Type::None,
            span: span,
            value: t
        }
    }

    pub fn into_inner(self) -> T {
        self.value
    }
}

impl<T: Typable> AsRef<T> for Typed<T> {
    fn as_ref(&self) -> &T {
        &self.value
    }
}

impl<T: Typable + fmt::Display> fmt::Display for Typed<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt(f)
    }
}

#[derive(Clone)]
pub enum TypeRef<S: Sort> {
    Ground(GroundSort<S>),
    Var(TypeVar<S>)
}

impl<S: Sort> From<GroundSort<S>> for TypeRef<S> {
    fn from(gsort: GroundSort<S>) -> TypeRef<S> {
        TypeRef::Ground(gsort)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeVar<S: Sort> {
    id: u32,
    s: PhantomData<S>
}

impl<S: Sort> TypeVar<S> {
    pub fn new(id: u32) -> TypeVar<S> {
        TypeVar {
            id: id,
            s: PhantomData
        }
    }
}

impl<S: Sort> Copy for TypeVar<S> {}

impl<S: Sort> UnifyKey for TypeVar<S> {
    type Value = Type<S>;

    fn index(&self) -> u32 {
        self.id
    }

    fn from_index(index: u32) -> TypeVar<S> {
        TypeVar {
            id: index,
            s: PhantomData
        }
    }

    fn tag() -> &'static str {
        "typevar"
    }
}

impl<T: Typable> Typed<T> {
    pub fn type_ref(&self) -> &TypeRef<T::Sort> {
        &self.type_ref
    }

    pub fn sort(&self) -> &GroundSort<T::Sort> {
        panic!("untyped!")
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn check(&self, checker: &mut TypeChecker<T::Sort>, env: &T::Environment) {
        panic!("TODO typecheck")
    }
}

pub struct TypeChecker<S: Sort> {
    table: UnificationTable<InPlace<TypeVar<S>>>,
    constraints: Vec<(TypeRef<S>, TypeRef<S>)>
}

impl<S: Sort> TypeChecker<S> {
    /// Add a new constraint to the type checker.
    ///
    /// Even of the system is not satisfiable, this function never fail.
    /// Type errors are detected with the [`TypeChecker::resolve`] method.
    pub fn assert_equal<A: Into<TypeRef<S>>, B: Into<TypeRef<S>>>(&mut self, expected: A, given: B) {
        self.constraints.push((expected.into(), given.into()))
    }

    /// Resolve all the constraints.
    pub fn resolve(&mut self) -> Result<(), S> {
        // loop {
        //     for (a, b) in &self.constraints {
        //         match (a, b) {
        //             (TypeRef::Ground(a), TypeRef::Ground(b)) => {
        //                 if a == b {
        //                     Ok(())
        //                 } else {
        //                     Err(Error::Missmatch(a, b))
        //                 }
        //             },
        //             (TypeRef::Label(a), TypeRef::Label(b)) => {
        //                 // ...
        //             }
        //         }
        //     }
        // }
        panic!("TODO resolve types")
    }
}

pub trait Typable {
    type Sort: Sort;
    type Environment;

    fn check(&self, checker: &mut TypeChecker<Self::Sort>, env: &Self::Environment, this_type: TypeRef<Self::Sort>);
}

impl<E: Environment> Typable for Term<E> {
    type Sort = E::Sort;
    type Environment = E;

    fn check(&self, checker: &mut TypeChecker<E::Sort>, env: &E, this_type: TypeRef<E::Sort>) {
        use Term::*;
        match self {
            Const(cst) => {
                checker.assert_equal(cst.sort().clone(), this_type);
            },
            Var { index, id } => {
                // nothing to check.
            },
            Let { body, .. } => {
                body.check(checker, env);
            },
            Forall { body, .. } => {
                checker.assert_equal(env.sort_bool(), this_type);
                body.check(checker, env);
            },
            Exists { body, .. } => {
                checker.assert_equal(env.sort_bool(), this_type);
                body.check(checker, env);
            },
            Match { term, cases } => {
                for case in cases {
                    checker.assert_equal(term.type_ref().clone(), case.term.type_ref().clone())
                }
                checker.assert_equal(term.type_ref().clone(), this_type);
            },
            Apply { fun, args } => {
                panic!("TODO typecheck function app")
                // fun.typecheck(checker, args, this_type);
            }
        }
    }
}

impl<E: Environment> Typable for Pattern<E> {
    type Sort = E::Sort;
    type Environment = E;

    fn check(&self, checker: &mut TypeChecker<E::Sort>, env: &E, this_type: TypeRef<E::Sort>) {
        panic!("TODO typecheck pattern")
    }
}
