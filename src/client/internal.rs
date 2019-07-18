use std::collections::HashMap;
use std::rc::Rc;
use std::convert::TryFrom;
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
    fn lexer(&mut self) -> Peekable<Lexer<Decoder<std::io::Bytes<&mut std::process::ChildStdout>>, u32>> {
        let id = self.server.id();
        Lexer::new(Decoder::new(self.server.stdout.as_mut().unwrap().by_ref().bytes()), id, Cursor::default()).peekable()
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

    fn const_sort(&self, cst: &Sorted<C, GroundSort<Ident>>) -> GroundSort<Ident> {
        cst.sort().clone()
    }
}

impl<L, C: Constant, F: Function> Server for Internal<L, C, F>
where L: fmt::Display, C: fmt::Display {
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
        //     id: id.clone(),
        //     args: args.clone(),
        //     return_sort: return_sort.clone()
        // };
        // self.functions.insert(id.clone(), Rc::new(ifun));
        write!(self.server.stdin.as_mut().unwrap(), "(declare-fun {} ({}) {})\n", id, PList(args), return_sort)?;
        Ok(())
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

impl<L, C: Constant, F: Function> Compiler for Internal<L, C, F> {
    /// Find the ident for the iven syntax symbol.
    fn ident_of_symbol<File: Clone>(&self, sym: &syntax::Symbol<File>) -> Option<Ident> {
        Some(Ident::from_syntax(sym))
    }

    /// Find the ident for the given syntax ident.
    fn ident<File: Clone>(&self, id: &syntax::Ident<File>) -> Option<Ident> {
        if id.indexes.is_empty() {
            self.ident_of_symbol(&id.id)
        } else {
            panic!("TODO indexed idents")
        }
    }

    /// Find the logic with the given id.
    fn logic(&self, id: &Ident) -> Option<Self::Logic> {
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
    LogicNary
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
            LogicNary => (0, std::usize::MAX)
        }
    }

    fn typecheck(&self, env: &Internal<L, C, F>, input: &[GroundSort<Ident>]) -> std::result::Result<GroundSort<Ident>, TypeCheckError<Ident>> {
        use self::InternalFunctionSignature::*;
        match &*self.sig {
            User { args, return_sort } => {
                for i in 0..args.len() {
                    if args[i] != input[i] {
                        return Err(TypeCheckError::Missmatch(i, (&args[i]).into()))
                    }
                }

                Ok(return_sort.clone())
            },
            Equality => {
                if input[0] == input[1] {
                    Ok(env.sort_bool.clone())
                } else {
                    Err(TypeCheckError::Missmatch(1, (&input[0]).into()))
                }
            },
            _ => {
                for (i, a) in input.iter().enumerate() {
                    if env.sort_bool != *a {
                        return Err(TypeCheckError::Missmatch(i, (&env.sort_bool).into()))
                    }
                }

                Ok(env.sort_bool.clone())
            }
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
