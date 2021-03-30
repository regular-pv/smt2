use crate::*;
use std::collections::HashMap;
use std::convert::TryFrom;
use std::fmt;
use std::hash::Hash;
use std::io::{Read, Write};
use std::iter::Peekable;
use std::marker::PhantomData;
use std::process::{self, Stdio};
use syntax::Parsable;

pub mod error;
mod ident;
mod interface;
mod internal;

pub mod cvc4;

pub use error::Error;
use ident::*;
use internal::*;

pub trait Sort: Clone + Hash + Eq + fmt::Debug {
	fn arity(&self) -> usize;
}

pub trait Constant: Clone + PartialEq + TryFrom<String> {
	fn sort_id(&self) -> &String;

	fn index(&self) -> u32;
}

pub enum FunctionSignature<S> {
	User {
		args: Vec<GroundSort<S>>,
		return_sort: GroundSort<S>,
	},
	Equality,
	LogicUnary,
	LogicBinary,
	LogicNary,
	Ite,
}

/// SMT2-lib solver environment.
pub struct Client<L, C: Clone + PartialEq, S: Sort, F: Function> {
	internal: Internal<L, C, F>,
	sort_bool: GroundSort<S>,
	sorts_ids: HashMap<S, Ident>,
	ids_sorts: HashMap<Ident, S>,
	count: u32,
	l: PhantomData<L>,
}

impl<L, C: Clone + PartialEq, S: Sort, F: Function> Environment for Client<L, C, S, F> {
	type Logic = L;
	type Ident = Ident;
	type Constant = Sorted<C, GroundSort<S>>;
	type Sort = S;
	type Function = F;
	type Error = Error<L, C, S, F>;

	/// Find a sort.
	fn sort(&self, id: &Ident) -> Option<S> {
		match self.ids_sorts.get(id) {
			Some(sort) => Some(sort.clone()),
			None => {
				println!("unknown sort {}", id);
				None
			}
		}
	}

	/// Get the Bool sort, which is the only required sort.
	fn sort_bool(&self) -> GroundSort<S> {
		self.sort_bool.clone()
	}

	fn typecheck_function(
		&self,
		_checker: &mut TypeChecker<S>,
		_f: &F,
		_args: &[TypeRef<S>],
		_return_sort: TypeRef<S>,
	) {
		panic!("TODO")
	}
}

impl<L, C: Constant, S: Sort, F: Function> Client<L, C, S, F>
where
	L: fmt::Display,
	C: fmt::Display,
{
	pub fn new(
		mut cmd: process::Command,
		sort_bool: S,
		cst_true: F,
		cst_false: F,
	) -> ExecResult<Client<L, C, S, F>, Error<L, C, S, F>> {
		let server = cmd
			.stdin(Stdio::piped())
			.stdout(Stdio::piped())
			.stderr(Stdio::piped())
			.spawn()?;

		let ident_bool = Ident::raw("Bool");

		let mut sorts_ids = HashMap::new();
		sorts_ids.insert(sort_bool.clone(), ident_bool.clone());
		let mut ids_sorts = HashMap::new();
		ids_sorts.insert(ident_bool.clone(), sort_bool.clone());

		// let file = unsafe { File::from_raw_fd(server.stdout.as_ref().unwrap().as_raw_fd()) };

		let internal = Internal::new(GroundSort::new(ident_bool), server);

		let mut client = Client {
			internal: internal,
			sort_bool: GroundSort::new(sort_bool),
			sorts_ids: sorts_ids,
			ids_sorts: ids_sorts,
			count: 0,
			l: PhantomData,
		};

		client.predefined_fun(
			"true",
			cst_true,
			FunctionSignature::User {
				args: Vec::new(),
				return_sort: client.sort_bool.clone(),
			},
		)?;
		client.predefined_fun(
			"false",
			cst_false,
			FunctionSignature::User {
				args: Vec::new(),
				return_sort: client.sort_bool.clone(),
			},
		)?;

		Ok(client)
	}

	pub fn new_id(&mut self) -> Ident {
		let id = self.count;
		self.count += 1;
		Ident::function(id)
	}

	pub fn new_sort_id(&mut self) -> Ident {
		let id = self.count;
		self.count += 1;
		Ident::sort(id)
	}

	/// Assert.
	pub fn assert(&mut self, term: &Typed<Term<Self>>) -> ExecResult<(), Error<L, C, S, F>> {
		let term = self.downgrade_term(term)?;
		let r = self.internal.assert(&term);
		self.upgrade_result(r)
	}

	/// Check satifiability.
	pub fn check_sat(&mut self) -> ExecResult<response::CheckSat, Error<L, C, S, F>> {
		let r = self.internal.check_sat();
		self.upgrade_result(r)
	}

	/// Declare a new constant.
	pub fn declare_const(
		&mut self,
		cst: F,
		sort: &GroundSort<S>,
	) -> ExecResult<(), Error<L, C, S, F>> {
		let id = self.new_id();
		let dsort = self.downgrade_ground_sort(sort)?;
		let sig = InternalFunctionSignature::User {
			args: Vec::new(),
			return_sort: dsort.clone(),
		};
		let internal_f = InternalFunction::new(id.clone(), cst.clone(), sig);
		self.internal.functions_ids.insert(cst, internal_f.clone());
		self.internal.ids_functions.insert(id.clone(), internal_f);
		let r = self.internal.declare_const(&id, &dsort);
		self.upgrade_result(r)
	}

	/// Declare new sort.
	pub fn declare_sort(&mut self, sort: S) -> ExecResult<(), Error<L, C, S, F>> {
		let id = self.new_sort_id();
		self.sorts_ids.insert(sort.clone(), id.clone());
		self.ids_sorts.insert(id.clone(), sort.clone());
		let decl = SortDeclaration {
			id: id,
			arity: sort.arity(),
		};
		let r = self.internal.declare_sort(&decl);
		self.upgrade_result(r)
	}

	/// Set the function object for the given predefined function.
	pub fn predefined_fun<Id: ToString>(
		&mut self,
		id: Id,
		function: F,
		sig: FunctionSignature<S>,
	) -> ExecResult<(), Error<L, C, S, F>> {
		let id = Ident::Raw(id.to_string());
		let sig = self.downgrade_signature(sig)?;
		let internal_f = InternalFunction::new(id.clone(), function.clone(), sig);
		self.internal
			.functions_ids
			.insert(function, internal_f.clone());
		self.internal.ids_functions.insert(id, internal_f);
		Ok(())
	}

	/// Declare new function.
	pub fn declare_fun(
		&mut self,
		function: F,
		args: &Vec<GroundSort<S>>,
		return_sort: &GroundSort<S>,
	) -> ExecResult<(), Error<L, C, S, F>> {
		let id = self.new_id();
		let sig = FunctionSignature::User {
			args: args.clone(),
			return_sort: return_sort.clone(),
		};
		let sig = self.downgrade_signature(sig)?;

		let internal_f = InternalFunction::new(id.clone(), function.clone(), sig);
		self.internal
			.functions_ids
			.insert(function, internal_f.clone());
		self.internal.ids_functions.insert(id.clone(), internal_f);

		let mut dargs = Vec::with_capacity(args.len());
		for a in args {
			dargs.push(self.downgrade_ground_sort(a)?);
		}
		let return_sort = self.downgrade_ground_sort(return_sort)?;
		let r = self.internal.declare_fun(&id, &dargs, &return_sort);
		self.upgrade_result(r)
	}

	/// Define previously declared sort.
	pub fn define_sort(
		&mut self,
		_def: &DataTypeDeclaration<Self>,
	) -> ExecResult<(), Error<L, C, S, F>> {
		let _id = self.new_sort_id();
		panic!("TODO define_sort")
	}

	/// Exit the solver.
	pub fn exit(&mut self) -> ExecResult<(), Error<L, C, S, F>> {
		let r = self.internal.exit();
		self.upgrade_result(r)
	}

	pub fn get_model(&mut self) -> ExecResult<response::Model<Self>, Error<L, C, S, F>> {
		let model = self.internal.get_model();
		self.upgrade_model(&self.upgrade_result(model)?)
	}

	/// Set the solver's logic.
	pub fn set_logic(&mut self, logic: &L) -> ExecResult<(), Error<L, C, S, F>> {
		let r = self.internal.set_logic(logic);
		self.upgrade_result(r)
	}
}

// TODO: unify once the unstable feature is stabilized.
#[cfg(feature = "nightly")]
pub trait Function = Clone + Hash + Eq + fmt::Display;
#[cfg(not(feature = "nightly"))]
pub trait Function: Clone + Hash + Eq + fmt::Display {}
#[cfg(not(feature = "nightly"))]
impl<T> Function for T where T: Clone + Hash + Eq + fmt::Display {}
