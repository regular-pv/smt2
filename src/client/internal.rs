use std::collections::HashMap;
use std::rc::Rc;
use utf8_decode::UnsafeDecoder;
use source_span::Position;
use super::*;
use super::error::InternalError;

pub struct Internal<L, C: Clone + PartialEq, F: Function> {
	pub sort_bool: GroundSort<Ident>,
	pub server: process::Child,
	pub functions_ids: HashMap<F, InternalFunction<F>>,
	pub ids_functions: HashMap<Ident, InternalFunction<F>>,
	pub l: PhantomData<L>,
	pub c: PhantomData<C>
}

impl<L, C: Clone + PartialEq, F: Function> Internal<L, C, F> {
	fn lexer(&mut self) -> Peekable<Lexer<UnsafeDecoder<std::io::Bytes<&mut std::process::ChildStdout>>>> {
		Lexer::new(UnsafeDecoder::new(self.server.stdout.as_mut().unwrap().by_ref().bytes()), Position::default()).peekable()
		// Lexer::new(Decoder::new_verbose(self.server.stdout.as_mut().unwrap().by_ref().bytes()), id, Cursor::default()).peekable()
	}
}

impl<L, C: Clone + PartialEq, F: Function> Environment for Internal<L, C, F> {
	type Logic = L;
	type Ident = Ident;
	type Constant = Sorted<C, GroundSort<Ident>>;
	type Sort = Ident;
	type Function = InternalFunction<F>;
	type Error = InternalError<L, C, F>;

	/// Find a sort.
	fn sort(&self, id: &Ident) -> Option<Ident> {
		Some(id.clone())
	}

	/// Get the Bool sort, which is the only required sort.
	fn sort_bool(&self) -> GroundSort<Ident> {
		self.sort_bool.clone()
	}

	fn typecheck_function(&self, checker: &mut TypeChecker<Ident>, f: &InternalFunction<F>, input: &[TypeRef<Ident>], return_sort_ref: TypeRef<Ident>) {
		use self::InternalFunctionSignature::*;
		match &*f.sig {
			User { args, return_sort } => {
				for i in 0..args.len() {
					checker.assert_equal(args[i].clone(), input[i].clone())
				}
				checker.assert_equal(return_sort.clone(), return_sort_ref);
			},
			Equality => {
				checker.assert_equal(input[0].clone(), input[1].clone());
				checker.assert_equal(self.sort_bool.clone(), return_sort_ref);
			},
			Ite => {
				checker.assert_equal(self.sort_bool.clone(), input[0].clone());
				checker.assert_equal(input[1].clone(), input[2].clone());
				checker.assert_equal(input[1].clone(), return_sort_ref);
			},
			_ => {
				for i in input.iter() {
					checker.assert_equal(self.sort_bool.clone(), i.clone());
				}

				checker.assert_equal(self.sort_bool.clone(), return_sort_ref);
			}
		}
	}
}

impl<L, C: Constant, F: Function> Server for Internal<L, C, F>
where L: fmt::Display, C: fmt::Display {
	/// Assert.
	fn assert(&mut self, term: &Typed<Term<Self>>) -> ExecResult<(), Self::Error> {
		// println!("(assert {})\n", term);
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
		write!(self.server.stdin.as_mut().unwrap(), "(declare-const {} {})\n", id, sort)?;
		Ok(())
	}

	/// Declare new sort.
	fn declare_sort(&mut self, decl: &SortDeclaration<Self>) -> ExecResult<(), Self::Error> {
		write!(self.server.stdin.as_mut().unwrap(), "(declare-sort {} {})\n", decl.id, decl.arity)?;
		Ok(())
	}

	/// Declare new function.
	fn declare_fun(&mut self, id: &Self::Ident, args: &Vec<GroundSort<Self::Sort>>, return_sort: &GroundSort<Self::Sort>) -> ExecResult<(), Self::Error> {
		// let ifun = InternalFunction<F> {
		//	 id: id.clone(),
		//	 args: args.clone(),
		//	 return_sort: return_sort.clone()
		// };
		// self.functions.insert(id.clone(), Rc::new(ifun));
		write!(self.server.stdin.as_mut().unwrap(), "(declare-fun {} ({}) {})\n", id, PList(args), return_sort)?;
		Ok(())
	}

	/// Define previously declared sort.
	fn define_sort(&mut self, _id: &Self::Ident, _def: &DataTypeDeclaration<Self>) -> ExecResult<(), Self::Error> {
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

impl<L, C: Constant, F: Function> Compiler for Internal<L, C, F> {
	/// Find the ident for the iven syntax symbol.
	fn ident_of_symbol(&self, sym: &syntax::Symbol) -> Option<Ident> {
		Some(Ident::from_syntax(sym))
	}

	/// Find the ident for the given syntax ident.
	fn ident(&self, id: &syntax::Ident) -> Option<Ident> {
		if id.indexes.is_empty() {
			self.ident_of_symbol(&id.id)
		} else {
			panic!("TODO indexed idents")
		}
	}

	/// Find the logic with the given id.
	fn logic(&self, _id: &Ident) -> Option<Self::Logic> {
		None
	}

	fn constant(&self, id: &Ident) -> Option<Sorted<C, GroundSort<Ident>>> {
		if let Ident::Raw(name) = id {
			if let Ok(cst) = C::try_from(name.clone()) {
				let sort = Ident::from_string(cst.sort_id());
				let gsort = GroundSort {
					sort: sort,
					parameters: Vec::new()
				};
				Some(Sorted(cst, gsort))
			} else {
				None
			}
		} else {
			None
		}
	}

	/// Find a function.
	fn function(&self, id: &Ident) -> Option<InternalFunction<F>> {
		match self.ids_functions.get(id) {
			Some(f) => Some(f.clone()),
			None => None
		}
	}
}

pub enum InternalFunctionSignature {
	User {
		args: Vec<GroundSort<Ident>>,
		return_sort: GroundSort<Ident>
	},
	Equality,
	LogicUnary,
	LogicBinary,
	LogicNary,
	Ite
}

#[derive(Clone)]
pub struct InternalFunction<F: Function> {
	pub id: Ident,
	pub f: F,
	pub sig: Rc<InternalFunctionSignature>
}

impl<F: Function> InternalFunction<F> {
	pub fn new(id: Ident, f: F, sig: InternalFunctionSignature) -> InternalFunction<F> {
		InternalFunction {
			id: id,
			f: f,
			sig: Rc::new(sig)
		}
	}
}

impl<F: Function> fmt::Display for InternalFunction<F> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self.id.fmt(f)
	}
}

impl<L, C: Clone + PartialEq, F: Function> crate::Function<Internal<L, C, F>> for InternalFunction<F> {
	fn arity(&self, _env: &Internal<L, C, F>) -> (usize, usize) {
		// (self.args.len(), self.args.len())
		use self::InternalFunctionSignature::*;
		match &*self.sig {
			User { args, .. } => (args.len(), args.len()),
			Equality => (2, 2),
			LogicUnary => (1, 1),
			LogicBinary => (2, 2),
			LogicNary => (0, std::usize::MAX),
			Ite => (3, 3)
		}
	}
}

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
