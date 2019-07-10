use crate::{
    Result,
    Environment,
    Compiler,
    Term,
    SortedVar,
    GroundSort,
    Context,
    Function,
    compile_symbol,
    compile_term,
    compile_sorted_var,
    compile_sort
};
use crate::syntax::response as syntax;

/// Check-sat command response.
#[derive(Clone, Copy)]
pub enum CheckSat {
    Sat,
    Unsat,
    Unknown
}

/// Model.
pub struct Model<E: Environment> {
    pub definitions: Vec<Definition<E>>
}

/// Model function definition.
pub struct Definition<E: Environment> {
    pub rec: bool,
    pub declarations: Vec<Declaration<E>>,
    pub bodies: Vec<Term<E>>
}

/// Function declaration.
pub struct Declaration<E: Environment> {
    pub id: E::Ident,
    pub args: Vec<SortedVar<E>>,
    pub return_sort: GroundSort<E::Sort>
}

pub fn compile_check_sat<E: Environment, F: Clone>(_env: &E, r: &syntax::CheckSat<F>) -> Result<CheckSat, E, F> {
    Ok(r.as_ref().clone())
}

pub fn compile_model<E: Compiler, F: Clone>(env: &E, ast: &syntax::Model<F>) -> Result<Model<E>, E, F> where E::Function: Function<E> {
    let mut compiled_definitions = Vec::with_capacity(ast.definitions.len());
    for def in ast.definitions.iter() {
        compiled_definitions.push(compile_definition(env, def)?);
    }

    Ok(Model {
        definitions: compiled_definitions
    })
}

pub fn compile_definition<E: Compiler, F: Clone>(env: &E, ast: &syntax::Definition<F>) -> Result<Definition<E>, E, F> where E::Function: Function<E> {
    let mut compiled_declarations = Vec::with_capacity(ast.declarations.len());
    let mut compiled_bodies = Vec::with_capacity(ast.bodies.len());

    for decl in ast.declarations.iter() {
        compiled_declarations.push(compile_declaration(env, decl)?);
    }

    let ctx = Context::new();

    for body in ast.bodies.iter() {
        compiled_bodies.push(compile_term(env, &ctx, body)?);
    }

    Ok(Definition {
        rec: ast.rec,
        declarations: compiled_declarations,
        bodies: compiled_bodies
    })
}

pub fn compile_declaration<E: Compiler, F: Clone>(env: &E, ast: &syntax::Declaration<F>) -> Result<Declaration<E>, E, F> where E::Function: Function<E> {
    let id = compile_symbol(env, &ast.id)?;

    let mut compiled_args = Vec::with_capacity(ast.args.len());
    for a in ast.args.iter() {
        compiled_args.push(compile_sorted_var(env, a)?);
    }

    let return_sort = compile_sort(env, &ast.return_sort)?;

    Ok(Declaration {
        id: id,
        args: compiled_args,
        return_sort: return_sort
    })
}
