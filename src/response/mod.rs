use crate::{Result, Environment};
use crate::syntax::response as syntax;

#[derive(Clone, Copy)]
pub enum CheckSat {
    Sat,
    Unsat,
    Unknown
}

pub fn compile_check_sat<E: Environment, F: Clone>(_env: &E, r: &syntax::CheckSat<F>) -> Result<CheckSat, E, F> {
    Ok(r.as_ref().clone())
}
