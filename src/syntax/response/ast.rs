pub use crate::syntax::{Sort, SortDeclaration, SortedVar, Symbol, Term};
use crate::Located;

/// (check-sat) command response.
/// <check_sat_response> ::= sat | unsat | unknown
pub type CheckSat = crate::response::CheckSat;

/// (get-model) command response.
/// <get_model_response> ::= ( <model_response>* )
pub struct Model {
	pub sorts: Vec<Located<SortDeclaration>>,
	pub definitions: Vec<Located<Definition>>,
}

/// Model function definition.
/// <model_response> ::= ( define-fun <function_def> )
///					| ( define-fun-rec <function_def> )
///					| ( define-funs-rec ( <function_dec>n+1 ) ( <term>n+1 ) )
/// <function_def> ::= <symbol> ( <sorted_var>* ) <sort> <term>
pub struct Definition {
	pub rec: bool,
	pub declarations: Vec<Located<Declaration>>,
	pub bodies: Vec<Located<Term>>,
	pub comments: String,
}

/// Function declaration.
/// <function_dec> ::= ( <symbol> ( <sorted_var>* ) <sort> )
pub struct Declaration {
	pub id: Located<Symbol>,
	pub args: Vec<Located<SortedVar>>,
	pub return_sort: Located<Sort>,
}
