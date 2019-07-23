use std::fmt;
use source_span::Span;
use crate::{
    Located,
    Result,
    Error,
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
    compile_sort,
    PList
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
    pub bodies: Vec<Term<E>>,
    pub comments: String
}

/// Function declaration.
pub struct Declaration<E: Environment> {
    pub f: E::Function,
    pub args: Vec<SortedVar<E>>,
    pub return_sort: GroundSort<E::Sort>
}

pub fn compile_check_sat<E: Environment>(_env: &E, r: &Located<syntax::CheckSat>) -> Result<CheckSat, E> {
    Ok((**r).clone())
}

pub fn compile_model<E: Compiler>(env: &E, ast: &syntax::Model) -> Result<Model<E>, E> where E::Function: Function<E> {
    let mut compiled_definitions = Vec::with_capacity(ast.definitions.len());
    for def in ast.definitions.iter() {
        compiled_definitions.push(compile_definition(env, def)?);
    }

    Ok(Model {
        definitions: compiled_definitions
    })
}

pub fn compile_definition<E: Compiler>(env: &E, ast: &syntax::Definition) -> Result<Definition<E>, E> where E::Function: Function<E> {
    let mut compiled_declarations = Vec::with_capacity(ast.declarations.len());
    let mut compiled_bodies = Vec::with_capacity(ast.bodies.len());

    for decl in ast.declarations.iter() {
        compiled_declarations.push(compile_declaration(env, decl)?);
    }

    for (i, body) in ast.bodies.iter().enumerate() {
        let decl = &compiled_declarations[i];
        let mut ctx = Context::new();
        for a in &decl.args {
            ctx.push(&a.id, &a.sort);
        }

        compiled_bodies.push(compile_term(env, &ctx, body)?);
    }

    Ok(Definition {
        rec: ast.rec,
        declarations: compiled_declarations,
        bodies: compiled_bodies,
        comments: String::new()
    })
}

pub fn compile_declaration<E: Compiler>(env: &E, ast: &Located<syntax::Declaration>) -> Result<Declaration<E>, E> where E::Function: Function<E> {
    let id = compile_symbol(env, &ast.id)?;
    let f = env.function(&id).ok_or(Error::UnknownFunction(id.clone()).at(ast.span()))?;

    let mut compiled_args = Vec::with_capacity(ast.args.len());
    for a in ast.args.iter() {
        compiled_args.push(compile_sorted_var(env, a)?);
    }

    let return_sort = compile_sort(env, &ast.return_sort)?;

    Ok(Declaration {
        f: f,
        args: compiled_args,
        return_sort: return_sort
    })
}

impl<E: Environment> fmt::Display for Model<E> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({})", PList(&self.definitions))
    }
}

impl<E: Environment> From<Model<E>> for Located<syntax::Model> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn from(model: Model<E>) -> Self {
        Located::new(syntax::Model {
            sorts: Vec::new(),
            definitions: model.definitions.into_iter().map(|d| d.into()).collect()
        }, Span::default())
    }
}

impl<E: Environment> From<Definition<E>> for Located<syntax::Definition> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn from(def: Definition<E>) -> Self {
        Located::new(syntax::Definition {
            rec: def.rec,
            declarations: def.declarations.into_iter().map(|d| d.into()).collect(),
            bodies: def.bodies.into_iter().map(|b| b.into()).collect(),
            comments: def.comments.clone()
        }, Span::default())
    }
}

impl<E: Environment> fmt::Display for Definition<E> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.declarations.is_empty() {
            if self.rec {
                if self.declarations.len() == 1 {
                    let decl = &self.declarations[0];
                    write!(f, "(define-fun-rec {} ({}) {} {})\n", decl.f, PList(&decl.args), decl.return_sort, self.bodies[0])
                } else {
                    write!(f, "(define-funs-rec (")?;
                    for decl in &self.declarations {
                        write!(f, "({} ({}) {})", decl.f, PList(&decl.args), decl.return_sort)?;
                    }
                    write!(f, ") (")?;
                    for body in &self.bodies {
                        write!(f, "({})", body)?;
                    }
                    write!(f, ")\n")
                }
            } else {
                if self.declarations.len() > 1 {
                    panic!("non-rec definitions must have only one declaration!");
                }

                let decl = &self.declarations[0];
                write!(f, "(define-fun {} ({}) {} {})\n", decl.f, PList(&decl.args), decl.return_sort, self.bodies[0])
            }
        } else {
            Ok(())
        }
    }
}

impl<E: Environment> From<Declaration<E>> for Located<syntax::Declaration> where E::Constant: fmt::Display, E::Ident: fmt::Display, E::Function: fmt::Display, E::Sort: fmt::Display {
    fn from(decl: Declaration<E>) -> Self {
        Located::new(syntax::Declaration {
            id: Located::new(syntax::Symbol::format(decl.f), Span::default()),
            args: decl.args.into_iter().map(|a| a.into()).collect(),
            return_sort: decl.return_sort.into()
        }, Span::default())
    }
}
