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

pub mod error;
mod ident;
mod internal;
mod interface;

pub use error::Error;
use ident::*;
use internal::*;
use interface::*;

pub trait Sort: Clone + Hash + Eq {
    fn arity(&self) -> usize;
}

pub trait Function = Clone + Hash + Eq;

pub enum FunctionSignature<S> {
    User {
        args: Vec<GroundSort<S>>,
        return_sort: GroundSort<S>
    },
    LogicUnary,
    LogicBinary,
    LogicNary
}

/// SMT2-lib solver environment.
pub struct Client<L, S: Sort, F: Function> {
    internal: Internal<L, F>,
    sort_bool: GroundSort<S>,
    sorts_ids: HashMap<S, Ident>,
    ids_sorts: HashMap<Ident, S>,
    count: u32,
    l: PhantomData<L>,
}

impl<L, S: Sort, F: Clone + Eq + Hash> Environment for Client<L, S, F> {
    type Logic = L;
    type Ident = Ident;
    type Sort = S;
    type Function = F;
    type Error = Error<L, S, F>;

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
}

impl<L, S: Sort, F: Clone + Eq + Hash> Client<L, S, F>
where L: fmt::Display {
    pub fn new(mut cmd: process::Command, sort_bool: S, cst_true: F, cst_false: F) -> std::io::Result<Client<L, S, F>> {
        let server = cmd.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn()?;

        let ident_bool = Ident::raw("Bool");

        let mut sorts_ids = HashMap::new();
        sorts_ids.insert(sort_bool.clone(), ident_bool.clone());
        let mut ids_sorts = HashMap::new();
        ids_sorts.insert(ident_bool.clone(), sort_bool.clone());

        // let file = unsafe { File::from_raw_fd(server.stdout.as_ref().unwrap().as_raw_fd()) };

        let internal = Internal {
            sort_bool: GroundSort::new(ident_bool),
            server: server,
            functions_ids: HashMap::new(),
            ids_functions: HashMap::new(),
            l: PhantomData,
        };

        let mut client = Client {
            internal: internal,
            sort_bool: GroundSort::new(sort_bool),
            sorts_ids: sorts_ids,
            ids_sorts: ids_sorts,
            count: 0,
            l: PhantomData,
        };

        client.predefined_fun("true", cst_true, FunctionSignature::User { args: Vec::new(), return_sort: client.sort_bool.clone() });
        client.predefined_fun("false", cst_false, FunctionSignature::User { args: Vec::new(), return_sort: client.sort_bool.clone() });

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
    pub fn assert(&mut self, term: &Term<Self>) -> ExecResult<(), Error<L, S, F>> {
        let term = self.downgrade_term(term)?;
        let r = self.internal.assert(&term);
        self.upgrade_result(r)
    }

    /// Check satifiability.
    pub fn check_sat(&mut self) -> ExecResult<response::CheckSat, Error<L, S, F>> {
        let r = self.internal.check_sat();
        self.upgrade_result(r)
    }

    /// Declare a new constant.
    pub fn declare_const(&mut self, cst: F, sort: &GroundSort<S>) -> ExecResult<(), Error<L, S, F>> {
        let id = self.new_id();
        let sig = InternalFunctionSignature::User {
            args: Vec::new(),
            return_sort: self.downgrade_ground_sort(sort)?
        };
        self.internal.functions_ids.insert(cst.clone(), id.clone());
        self.internal.ids_functions.insert(id.clone(), InternalFunction::new(id, cst, sig));
        panic!("TODO declare_const")
    }

    /// Declare new sort.
    pub fn declare_sort(&mut self, sort: S) -> ExecResult<(), Error<L, S, F>> {
        let id = self.new_sort_id();
        self.sorts_ids.insert(sort.clone(), id.clone());
        self.ids_sorts.insert(id.clone(), sort.clone());
        let decl = SortDeclaration {
            id: id,
            arity: sort.arity()
        };
        let r = self.internal.declare_sort(&decl);
        self.upgrade_result(r)
    }

    /// Set the function object for the given predefined function.
    pub fn predefined_fun<Id: ToString>(&mut self, id: Id, function: F, sig: FunctionSignature<S>) -> ExecResult<(), Error<L, S, F>> {
        let id = Ident::Raw(id.to_string());
        let sig = self.downgrade_signature(sig)?;
        self.internal.functions_ids.insert(function.clone(), id.clone());
        self.internal.ids_functions.insert(id.clone(), InternalFunction::new(id, function, sig));
        Ok(())
    }

    /// Declare new function.
    pub fn declare_fun(&mut self, function: F, args: &Vec<GroundSort<S>>, return_sort: &GroundSort<S>) -> ExecResult<(), Error<L, S, F>> {
        let id = self.new_id();
        let sig = FunctionSignature::User {
            args: args.clone(),
            return_sort: return_sort.clone()
        };
        let sig = self.downgrade_signature(sig)?;

        self.internal.functions_ids.insert(function.clone(), id.clone());
        self.internal.ids_functions.insert(id.clone(), InternalFunction::new(id.clone(), function, sig));

        let mut dargs = Vec::with_capacity(args.len());
        for a in args {
            dargs.push(self.downgrade_ground_sort(a)?);
        }
        let return_sort = self.downgrade_ground_sort(return_sort)?;
        let r = self.internal.declare_fun(&id, &dargs, &return_sort);
        self.upgrade_result(r)
    }

    /// Define previously declared sort.
    pub fn define_sort(&mut self, def: &DataTypeDeclaration<Self>) -> ExecResult<(), Error<L, S, F>> {
        let id = self.new_sort_id();
        panic!("TODO define_sort")
    }

    /// Exit the solver.
    pub fn exit(&mut self) -> ExecResult<(), Error<L, S, F>> {
        let r = self.internal.exit();
        self.upgrade_result(r)
    }

    pub fn get_model(&mut self) -> ExecResult<response::Model<Self>, Error<L, S, F>> {
        let model = self.internal.get_model();
        self.upgrade_model(&self.upgrade_result(model)?)
    }

    /// Set the solver's logic.
    pub fn set_logic(&mut self, logic: &L) -> ExecResult<(), Error<L, S, F>> {
        let r = self.internal.set_logic(logic);
        self.upgrade_result(r)
    }
}
