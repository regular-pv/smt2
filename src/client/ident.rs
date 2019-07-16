use std::fmt;
use crate::syntax;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Ident {
    Raw(String),
    Sort(u32),
    Fun(u32)
}

impl Ident {
    pub fn raw(name: &'static str) -> Ident {
        Ident::Raw(name.to_string())
    }

    pub fn sort(id: u32) -> Ident {
        Ident::Sort(id)
    }

    pub fn function(id: u32) -> Ident {
        Ident::Fun(id)
    }

    pub fn from_syntax<F: Clone>(sym: &syntax::Symbol<F>) -> Ident {
        if sym.id.len() > 4 {
            if let Some("Sort") = sym.id.get(0..4) {
                let id_str = sym.id.get(4..).unwrap();
                match u32::from_str_radix(id_str, 16) {
                    Ok(id) => return Ident::Sort(id),
                    _ => ()
                }
            }
        }

        if sym.id.len() > 1 {
            if let Some("f") = sym.id.get(0..1) {
                let id_str = sym.id.get(1..).unwrap();
                match u32::from_str_radix(id_str, 16) {
                    Ok(id) => return Ident::Fun(id),
                    _ => ()
                }
            }
        }

        Ident::Raw(sym.id.clone())
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Ident::Raw(name) => write!(f, "{}", name),
            Ident::Sort(id) => write!(f, "Sort{:x}", id),
            Ident::Fun(id) => write!(f, "f{:x}", id)
        }
    }
}
