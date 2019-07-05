use crate::{Location, Located};
pub use crate::syntax::{
    Symbol,
    Term,
    SortedVar,
    Sort
};

/// (check-sat) command response.
/// <check_sat_response> ::= sat | unsat | unknown
pub type CheckSat<F> = Located<crate::response::CheckSat, F>;

/// (get-model) command response.
/// <get_model_response> ::= ( <model_response>* )
pub struct GetModel<F: Clone> {
    pub location: Location<F>,
    pub definitions: Vec<Definition<F>>
}

/// Model function definition.
/// <model_response> ::= ( define-fun <function_def> )
///                    | ( define-fun-rec <function_def> )
///                    | ( define-funs-rec ( <function_dec>n+1 ) ( <term>n+1 ) )
/// <function_def> ::= <symbol> ( <sorted_var>* ) <sort> <term>
pub struct Definition<F: Clone> {
    pub location: Location<F>,
    pub rec: bool,
    pub declarations: Vec<Declaration<F>>,
    pub bodies: Vec<Term<F>>
}

/// Function declaration.
/// <function_dec> ::= ( <symbol> ( <sorted_var>* ) <sort> )
pub struct Declaration<F: Clone> {
    pub location: Location<F>,
    pub id: Symbol<F>,
    pub args: Vec<SortedVar<F>>,
    pub return_sort: Sort<F>
}
