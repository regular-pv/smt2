use std::collections::HashMap;
use std::convert::AsRef;
use std::fmt;
use source_span::Span;
use crate::{
	Environment,
	Sort,
	SortedWith,
	GroundSort,
	Command,
	Term,
	Pattern,
	response
};

mod error;

pub use error::*;

#[derive(Clone, Debug)]
pub enum TypeRef<S: Sort> {
	Var(usize, Span),
	Ground(GroundTypeRef<S>)
}

impl<S: Sort + fmt::Display> fmt::Display for TypeRef<S> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use TypeRef::*;
		match self {
			Var(_, _) => write!(f, "_"),
			Ground(g) => {
				if g.parameters.is_empty() {
					write!(f, "{}", g.sort)
				} else {
					write!(f, "({}", g.sort)?;
					for p in &g.parameters {
						write!(f, " {}", p)?;
					}
					write!(f, ")")
				}
			}
		}
	}
}

#[derive(Clone, Debug)]
pub struct GroundTypeRef<S: Sort> {
	pub sort: S,
	pub parameters: Vec<TypeRef<S>>
}

impl<S: Sort> TypeRef<S> {
	fn into_ground_sort(&self) -> std::result::Result<GroundSort<S>, ()> {
		match self {
			TypeRef::Var(_, _) => {
				println!("ambiguity on {:?}", self);
				Err(())
			},
			TypeRef::Ground(g) => {
				let mut parameters = Vec::with_capacity(g.parameters.len());
				for p in &g.parameters {
					parameters.push(p.into_ground_sort()?)
				}

				Ok(GroundSort {
					sort: g.sort.clone(),
					parameters: parameters
				})
			}
		}
	}
}

impl<S: Sort> From<TypeRef<S>> for SortMissmatch<S> {
	fn from(ty: TypeRef<S>) -> SortMissmatch<S> {
		match ty {
			TypeRef::Var(id, span) => SortMissmatch::Var(id, span),
			TypeRef::Ground(g) => g.into()
		}
	}
}

impl<S: Sort> From<GroundTypeRef<S>> for SortMissmatch<S> {
	fn from(ty: GroundTypeRef<S>) -> SortMissmatch<S> {
		SortMissmatch::Match {
			sort: ty.sort,
			parameters: ty.parameters.into_iter().map(|ty| ty.into()).collect()
		}
	}
}

pub struct Typed<T: Typable> {
	typ: Option<GroundSort<T::Sort>>,
	span: Span,
	value: T
}

impl<T: Typable> Typed<T> {
	pub fn new(t: T, span: Span, sort: GroundSort<T::Sort>) -> Typed<T> {
		Typed {
			typ: Some(sort),
			span: span,
			value: t
		}
	}

	pub fn untyped(t: T, span: Span) -> Typed<T> {
		Typed {
			typ: None,
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

impl<S: Sort> From<GroundSort<S>> for TypeRef<S> {
	fn from(gsort: GroundSort<S>) -> TypeRef<S> {
		TypeRef::Ground(GroundTypeRef {
			sort: gsort.sort,
			parameters: gsort.parameters.into_iter().map(|gs| gs.into()).collect()
		})
	}
}

impl<T: Typable> Typed<T> {
	pub fn sort(&self) -> &GroundSort<T::Sort> {
		if let Some(sort) = &self.typ {
			sort
		} else {
			panic!("untyped!")
		}
	}

	pub fn span(&self) -> Span {
		self.span
	}

	pub fn type_decoration(&mut self, checker: &mut TypeChecker<T::Sort>, env: &T::Environment) -> TypeRef<T::Sort> {
		let type_ref = checker.new_attached_type_variable(self.span(), &mut self.typ as *mut Option<_>);
		checker.enter(self.span());
		self.value.type_decoration(checker, env, type_ref.clone());
		checker.leave();
		type_ref
	}
}

pub type Constraint<S> = (TypeRef<S>, TypeRef<S>, Span);

pub struct TypeChecker<S: Sort> {
	path: Vec<Span>,

	/// Pending constraints to resolve.
	constraints: Vec<Constraint<S>>,

	/// The sort of the currently bound variables.
	///
	/// Modified with `push`/`pop`.
	variables: Vec<TypeRef<S>>,

	knowledge: Vec<TypeRef<S>>,

	spans: Vec<Span>,

	pointers: HashMap<usize, *mut Option<GroundSort<S>>>
}

impl<S: Sort> TypeChecker<S> {
	pub fn new() -> TypeChecker<S> {
		TypeChecker {
			path: Vec::new(),
			constraints: Vec::new(),
			variables: Vec::new(),
			knowledge: Vec::new(),
			spans: Vec::new(),
			pointers: HashMap::new()
		}
	}

	pub fn new_type_variable(&mut self, span: Span) -> TypeRef<S> {
		let id = self.knowledge.len();
		self.knowledge.push(TypeRef::Var(id, span));
		self.spans.push(span);
		TypeRef::Var(id, span)
	}

	pub fn new_attached_type_variable(&mut self, span: Span, pointer: *mut Option<GroundSort<S>>) -> TypeRef<S> {
		let id = self.knowledge.len();
		self.knowledge.push(TypeRef::Var(id, span));
		self.spans.push(span);
		self.pointers.insert(id, pointer);
		TypeRef::Var(id, span)
	}

	/// Add a new constraint to the type checker.
	///
	/// Even of the system is not satisfiable, this function never fail.
	/// Type errors are detected with the [`TypeChecker::resolve`] method.
	pub fn assert_equal<A: Into<TypeRef<S>>, B: Into<TypeRef<S>>>(&mut self, expected: A, given: B) {
		self.constraints.push((expected.into(), given.into(), self.location()))
	}

	pub fn var(&self, index: usize) -> &TypeRef<S> {
		&self.variables[index]
	}

	pub fn push<T: Into<TypeRef<S>>>(&mut self, ty: T) {
		self.variables.push(ty.into())
	}

	pub fn pop(&mut self, len: usize) {
		for _ in 0..len {
			self.variables.pop();
		}
	}

	pub fn enter(&mut self, span: Span) {
		self.path.push(span);
	}

	pub fn leave(&mut self) {
		self.path.pop();
	}

	pub fn location(&self) -> Span {
		match self.path.last() {
			Some(span) => *span,
			None =>  Span::default()
		}
	}

	pub fn representant(&self, id: usize) -> (usize, TypeRef<S>) {
		match &self.knowledge[id] {
			TypeRef::Var(next, _) if *next != id => {
				self.representant(*next)
			},
			ty => (id, ty.clone())
		}
	}

	pub fn redirected(&self, ty: &TypeRef<S>) -> TypeRef<S> {
		match ty {
			TypeRef::Var(id, span) => {
				match &self.knowledge[*id] {
					TypeRef::Var(next, _) if next != id => {
						self.redirected(&TypeRef::Var(*next, *span))
					},
					TypeRef::Var(_, _) => ty.clone(),
					ground => self.redirected(ground)
				}
			},
			TypeRef::Ground(g) => {
				TypeRef::Ground(GroundTypeRef {
					sort: g.sort.clone(),
					parameters: g.parameters.iter().map(|p| self.redirected(p)).collect()
				})
			}
		}
	}

	pub fn unify(&self, expected: TypeRef<S>, given: TypeRef<S>, root: bool, span: Span) -> std::result::Result<(TypeRef<S>, Vec<Constraint<S>>), SortMissmatch<S>> {
		match (self.redirected(&expected), self.redirected(&given)) {
			 (TypeRef::Var(a, span_a), TypeRef::Var(b, span_b)) => {
				 let constraints = if root {
					 Vec::new()
				 } else {
					 vec![(TypeRef::Var(a, span_a), TypeRef::Var(b, span_b), span)]
				 };
				 Ok((TypeRef::Var(std::cmp::min(a, b), span_b), constraints))
			 },
			 (TypeRef::Ground(a), TypeRef::Ground(b)) => {
				 if a.sort != b.sort {
					let m = SortMissmatch::Miss {
						 expected_sort: a.sort.clone(),
						 expected_parameters: a.parameters.clone(),
						 given_sort: b.sort.clone(),
						 given_parameters: b.parameters.clone()
					 };
					 return Err(m)
				 } else {
					 let sort = a.sort;
					 let mut parameters = Vec::new();
					 let mut constraints = Vec::new();

					 let mut mismatch_parameters = Vec::new();

					 for (a, b) in a.parameters.into_iter().zip(b.parameters.into_iter()) {
						 if mismatch_parameters.is_empty() {
							 match self.unify(a, b, false, span) {
								 Ok((c, mut sub_constraints)) => {
									 constraints.append(&mut sub_constraints);
									 parameters.push(c);
								 },
								 Err(e) => {
									 for c in parameters.drain(..) {
										 mismatch_parameters.push(c.into())
									 }
									 mismatch_parameters.push(e);
								 }
							 }
						 } else {
							 mismatch_parameters.push(a.into());
						 }
					 }

					 if !mismatch_parameters.is_empty() {
						 Err(SortMissmatch::Match {
							 sort: sort,
							 parameters: mismatch_parameters
						 })
					 } else {
						 Ok((TypeRef::Ground(GroundTypeRef {
							 sort: sort,
							 parameters: parameters
						 }), constraints))
					 }
				 }
			 },
			 (TypeRef::Var(a, span_a), b) => {
				 let constraints = if root {
					 Vec::new()
				 } else {
					 vec![(TypeRef::Var(a, span_a), b.clone(), span)]
				 };
				 Ok((b, constraints))
			 },
			 (a, TypeRef::Var(b, span_b)) => {
				 let constraints = if root {
					 Vec::new()
				 } else {
					 vec![(a.clone(), TypeRef::Var(b, span_b), span)]
				 };
				 Ok((a, constraints))
			 }
		}
	}

	/// Resolve all the constraints.
	pub fn resolve(&mut self) -> Result<(), S> {
		while !self.constraints.is_empty() {
			let constraints = self.constraints.clone();
			self.constraints.clear();

			for (a, b, span) in constraints.into_iter() {
				// println!("{:?} = {:?}", a, b);
				match (a, b) {
					(TypeRef::Var(expected, expected_span), TypeRef::Var(given, given_span)) => {
						let (expected_rep, expected_ty) = self.representant(expected);
						let (given_rep, given_ty) = self.representant(given);
						match self.unify(expected_ty, given_ty, true, span) {
							Err(e) => return Err(Error::Missmatch(e).at(given_span)),
							Ok((union, mut new_constraints)) => {
								if expected_rep < given_rep {
									self.knowledge[expected_rep] = union;
									self.knowledge[given_rep] = TypeRef::Var(expected_rep, given_span);
								} else {
									self.knowledge[given_rep] = union;
									self.knowledge[expected_rep] = TypeRef::Var(given_rep, expected_span);
								}

								self.constraints.append(&mut new_constraints);
							}
						}
					},
					(TypeRef::Ground(expected), TypeRef::Ground(given)) => {
						let expected_ty = TypeRef::Ground(expected);
						let given_ty = TypeRef::Ground(given);
						match self.unify(expected_ty, given_ty, true, span) {
							Err(e) => return Err(Error::Missmatch(e).at(span)),
							Ok((_, mut new_constraints)) => {
								self.constraints.append(&mut new_constraints);
							}
						}
					},
					(TypeRef::Var(expected, _), given_ty) => {
						let (expected_rep, expected_ty) = self.representant(expected);
						match self.unify(expected_ty, given_ty, true, span) {
							Err(e) => return Err(Error::Missmatch(e).at(span)),
							Ok((union, mut new_constraints)) => {
								self.knowledge[expected_rep] = union;
								self.constraints.append(&mut new_constraints);
							}
						}
					},
					(expected_ty, TypeRef::Var(given, given_span)) => {
						let (given_rep, given_ty) = self.representant(given);
						match self.unify(expected_ty, given_ty, true, span) {
							Err(e) => return Err(Error::Missmatch(e).at(given_span)),
							Ok((union, mut new_constraints)) => {
								// println!("{} union {:?}", given_rep, union);
								self.knowledge[given_rep] = union;
								self.constraints.append(&mut new_constraints);
							}
						}
					}
				}
			}
		}

		Ok(())
	}

	/// Apply the resolved types.
	pub unsafe fn apply(&self) -> Result<(), S> {
		for (id, ptr) in &self.pointers {
			let span = self.spans[*id];
			match self.redirected(&TypeRef::Var(*id, span)).into_ground_sort() {
				Ok(sort) => {
					std::ptr::write(*ptr, Some(sort));
				},
				Err(_) => {
					return Err(Error::Ambiguity.at(span))
				}
			}
		}

		Ok(())
	}
}

pub trait Typable {
	type Sort: Sort;
	type Environment;

	fn type_decoration(&mut self, checker: &mut TypeChecker<Self::Sort>, env: &Self::Environment, this_type: TypeRef<Self::Sort>);
}

pub trait Untypable {
	type Sort: Sort;
	type Environment;

	fn type_decoration(&mut self, checker: &mut TypeChecker<Self::Sort>, env: &Self::Environment);
}

impl<E: Environment> Untypable for Command<E> {
	type Sort = E::Sort;
	type Environment = E;

	fn type_decoration(&mut self, checker: &mut TypeChecker<Self::Sort>, env: &Self::Environment) {
		use Command::*;
		match self {
			Assert(term) => {
				term.type_decoration(checker, env);
			},
			_ => ()
		}
	}
}

impl<E: Environment> Typable for Term<E> {
	type Sort = E::Sort;
	type Environment = E;

	fn type_decoration(&mut self, checker: &mut TypeChecker<E::Sort>, env: &E, this_type: TypeRef<E::Sort>) {
		use Term::*;
		match self {
			Const(cst) => {
				checker.assert_equal(cst.sort().clone(), this_type);
			},
			Var { index, .. } => {
				checker.assert_equal(this_type, checker.var(*index).clone());
			},
			Let { bindings, body } => {
				for binding in bindings.iter_mut() {
					let binding_type = binding.value.type_decoration(checker, env);
					checker.push(binding_type);
				}
				let body_type = body.type_decoration(checker, env);
				checker.pop(bindings.len());
				checker.assert_equal(this_type, body_type);
			},
			Forall { vars, body} => {
				for x in vars.iter_mut() {
					checker.push(x.sort.clone());
				}
				body.type_decoration(checker, env);
				checker.pop(vars.len());
				checker.assert_equal(env.sort_bool(), this_type);
			},
			Exists { vars, body } => {
				for x in vars.iter_mut() {
					checker.push(x.sort.clone());
				}
				body.type_decoration(checker, env);
				checker.pop(vars.len());
				checker.assert_equal(env.sort_bool(), this_type);
			},
			Match { term, cases } => {
				let term_type_ref = term.type_decoration(checker, env);
				for case in cases {
					let pattern_type_ref = case.pattern.type_decoration(checker, env);
					let value_type_ref = case.term.type_decoration(checker, env);
					checker.assert_equal(term_type_ref.clone(), pattern_type_ref);
					checker.assert_equal(term_type_ref.clone(), value_type_ref);
				}
				checker.assert_equal(term_type_ref, this_type);
			},
			Apply { fun, args } => {
				let mut args_types = Vec::new();
				for a in args.iter_mut() {
					let arg_type_ref = a.type_decoration(checker, env);
					args_types.push(arg_type_ref);
				}
				env.typecheck_function(checker, fun, &args_types, this_type);
			}
		}
	}
}

impl<E: Environment> Typable for Pattern<E> {
	type Sort = E::Sort;
	type Environment = E;

	fn type_decoration(&mut self, _checker: &mut TypeChecker<E::Sort>, _env: &E, _this_type: TypeRef<E::Sort>) {
		panic!("TODO typecheck pattern")
	}
}

impl<E: Environment> Untypable for response::Model<E> {
	type Sort = E::Sort;
	type Environment = E;

	fn type_decoration(&mut self, checker: &mut TypeChecker<Self::Sort>, env: &Self::Environment) {
		for def in &mut self.definitions {
			def.type_decoration(checker, env)
		}
	}
}

impl<E: Environment> Untypable for response::Definition<E> {
	type Sort = E::Sort;
	type Environment = E;

	fn type_decoration(&mut self, checker: &mut TypeChecker<Self::Sort>, env: &Self::Environment) {
		for (i, decl) in self.declarations.iter_mut().enumerate() {
			let body = &mut self.bodies[i];
			for arg in &decl.args {
				checker.push(arg.sort.clone());
			}
			body.type_decoration(checker, env);
			checker.pop(decl.args.len());

		}
	}
}
