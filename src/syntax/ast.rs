use std::fmt;
use crate::PList;
use super::Located;

/**
 * Symbol.
 */
#[derive(Clone, Debug)]
pub struct Symbol {
    pub id: String
}

impl Symbol {
    pub fn format<T: fmt::Display>(t: T) -> Symbol {
        Symbol {
            id: format!("{}", t)
        }
    }
}

impl PartialEq<str> for Symbol {
    fn eq(&self, other: &str) -> bool {
        self.id == other
    }
}

impl PartialEq<String> for Symbol {
    fn eq(&self, other: &String) -> bool {
        self.id == *other
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)
    }
}

/**
 * Identifiers index.
 *
 * <index> ::= <numeral> | <symbol>
 */
#[derive(Clone, Debug)]
pub enum Index {
    Numeral(i64),
    Symbol(Symbol)
}

impl fmt::Display for Index {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Index::*;
        match self {
            Numeral(i) => write!(f, "{}", i),
            Symbol(s) => write!(f, "{}", s)
        }
    }
}

/**
 * Identifiers.
 *
 * <identifier> ::= <symbol> | ( _ <symbol> <index>+ )
 */
#[derive(Clone, Debug)]
pub struct Ident {
    pub id: Located<Symbol>,
    pub indexes: Vec<Located<Index>>
}

impl From<Located<Symbol>> for Located<Ident> {
    fn from(sym: Located<Symbol>) -> Self {
        let span = sym.span();
        Located::new(Ident {
            id: sym,
            indexes: Vec::new()
        }, span)
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.indexes.is_empty() {
            self.id.fmt(f)
        } else {
            write!(f, "(_ {} {})", self.id, PList(&self.indexes))
        }
    }
}

#[derive(Clone)]
pub struct Keyword {
    pub id: String
}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.id.fmt(f)
    }
}

/**
 * <attribute> ::= <keyword> | <keyword> <attribute_value>
 */
#[derive(Clone)]
pub struct Attribute {
    pub key: Located<Keyword>,
    pub value: Option<Located<AttributeValue>>
}

impl fmt::Display for Attribute {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.value {
            Some(value) => {
                write!(f, "{} {}", self.key, value)
            },
            None => self.key.fmt(f)
        }
    }
}

/**
 * <attribute_value> ::= <spec_const> | <symbol> | <s_expr*>
 */
#[derive(Clone)]
pub enum AttributeValue {
    // Const(Constant),
    Sym(Located<Symbol>),
    List(Vec<Located<SExpr>>)
}

impl fmt::Display for AttributeValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use AttributeValue::*;
        match self {
            // Const(c) => c.fmt(f),
            Sym(s) => s.fmt(f),
            List(exprs) => PList(&exprs).fmt(f)
        }
    }
}

/**
 * <s_expr> ::= <spec_const> | <symbol> | <keyword> | <s_expr*>
 */
#[derive(Clone)]
pub enum SExpr {
    // Const(Constant),
    Sym(Located<Symbol>),
    Keyword(Located<Keyword>),
    List(Vec<Located<SExpr>>)
}

impl fmt::Display for SExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SExpr::*;
        match self {
            // Const(c) => c.fmt(f),
            Sym(s) => s.fmt(f),
            Keyword(k) => k.fmt(f),
            List(l) => PList(l).fmt(f)
        }
    }
}

/**
 * <sort> ::= <identifier> | (<identifier> <sort>+)
 */
#[derive(Clone)]
pub struct Sort {
    pub id: Located<Ident>,
    pub parameters: Vec<Located<Sort>>
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.parameters.is_empty() {
            self.id.fmt(f)
        } else {
            write!(f, "({} {})", self.id, PList(&self.parameters))
        }
    }
}

/**
 * <term>   ::= <spec_const>
 *            | ( let ( <var_binding>+ ) <term> )
 *            | ( forall ( <sorted_var>+ ) <term> )
 *            | ( exists ( <sorted_var>+ ) <term> )
 */
#[derive(Clone)]
pub enum Term {
    // Const(Constant),
    Ident(Located<Ident>),
    Let {
        bindings: Vec<Located<Binding>>,
        body: Box<Located<Term>>
    },
    Forall {
        vars: Vec<Located<SortedVar>>,
        body: Box<Located<Term>>
    },
    Exists {
        vars: Vec<Located<SortedVar>>,
        body: Box<Located<Term>>
    },
    Match {
        term: Box<Located<Term>>,
        cases: Vec<Located<MatchCase>>
    },
    Apply {
        id: Located<Ident>,
        args: Box<Vec<Located<Term>>>
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Term::*;
        match self {
            // Const(c) => c.fmt(f),
            Ident(id) => id.fmt(f),
            Let { bindings, body } => write!(f, "(let ({}) {})", PList(&bindings), body),
            Forall { vars, body } => write!(f, "(forall ({}) {})", PList(&vars), body),
            Exists { vars, body } => write!(f, "(exists ({}) {})", PList(&vars), body),
            Match { term, cases } => write!(f, "(match {}, ({}))", term, PList(cases)),
            Apply { id, args } => write!(f, "({} {})", id, PList(&args))
        }
    }
}

#[derive(Clone)]
pub struct MatchCase {
    pub pattern: Located<Pattern>,
    pub term: Box<Located<Term>>
}

impl fmt::Display for MatchCase {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.pattern, self.term)
    }
}

#[derive(Clone)]
pub struct Pattern {
    pub constructor: Located<Symbol>,
    pub args: Vec<Located<Symbol>>
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.args.is_empty() {
            write!(f, "{}", self.constructor)
        } else {
            write!(f, "({} {})", self.constructor, PList(&self.args))
        }
    }
}

/**
 * <var_binding> ::= ( <symbol> <term> )
 */
#[derive(Clone)]
pub struct Binding {
    pub id: Located<Symbol>,
    pub value: Box<Located<Term>>
}

impl fmt::Display for Binding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.id, self.value)
    }
}

/**
 * <sorted_var> ::= ( <symbol> <sort> )
 */
#[derive(Clone)]
pub struct SortedVar {
    pub id: Located<Symbol>,
    pub sort: Located<Sort>
}

impl fmt::Display for SortedVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.id, self.sort)
    }
}

/**
 * <datatype_dec> ::= ( <constructor_dec>+ )
 *                  | ( par ( <symbol>+ ) <constructor_dec>+ )
 */
#[derive(Clone)]
pub struct DataTypeDeclaration {
    pub parameters: Vec<Located<Symbol>>,
    pub constructors: Vec<Located<ConstructorDeclaration>>
}

impl fmt::Display for DataTypeDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({})", PList(&self.constructors))
    }
}

/**
 * <constructor_dec> ::= ( <symbol> <selector_dec>* )
 */
#[derive(Clone)]
pub struct ConstructorDeclaration {
    pub id: Located<Symbol>,
    pub selectors: Vec<Located<SelectorDeclaration>>
}

impl fmt::Display for ConstructorDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.id, PList(&self.selectors))
    }
}

/**
 * <selector_dec> ::= ( <symbol> <sort> )
 */
#[derive(Clone)]
pub struct SelectorDeclaration {
    pub id: Located<Symbol>,
    pub sort: Located<Sort>
}

impl fmt::Display for SelectorDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.id, self.sort)
    }
}

/**
 * <sort_dec> ::= ( <symbol> <numeral> )
 */
#[derive(Clone)]
pub struct SortDeclaration {
    pub id: Located<Symbol>,
    pub arity: Located<i64>
}

impl fmt::Display for SortDeclaration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.id, self.arity)
    }
}

/**
 * <command>    ::= ( assert <term> )
 *                | ( check-sat )
 *                | ( declare-const <symbol> <sort> )
 *                | ( declare-datatype <symbol> <datatype_decl> )
 *                | ( declare-datatypes ( <sort_dec>n+1 ) ( <datatype_dec>n+1 ) )
 *                | ( exit )
 *                | ( set-info <attribute> )
 *                | ( set-logic <symbol> )
 */
#[derive(Clone)]
pub enum Command {
    Assert(Located<Term>),
    CheckSat,
    DeclareConst(Located<Symbol>, Located<Sort>),
    DeclareDatatype(Located<Symbol>, Located<DataTypeDeclaration>),
    DeclareDatatypes(Vec<Located<SortDeclaration>>, Vec<Located<DataTypeDeclaration>>),
    DeclareFun(Located<Symbol>, Vec<Located<Sort>>, Located<Sort>),
    Exit,
    GetModel,
    SetInfo(Located<Attribute>),
    SetLogic(Located<Symbol>)
}

impl fmt::Display for Command {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Command::*;
        match self {
            Assert(t) => write!(f, "(assert {})", t),
            CheckSat => write!(f, "(check-sat)"),
            DeclareConst(id, sort) => write!(f, "(declare-const {} {})", id, sort),
            DeclareDatatype(id, decl) => write!(f, "(declare-datatype {} {})", id, decl),
            DeclareDatatypes(sort_decls, decls) => write!(f, "(declare-datatypes ({}) ({}))", PList(&sort_decls), PList(&decls)),
            DeclareFun(id, args, result) => write!(f, "(declare-fun {} ({}) {})", id, PList(args), result),
            Exit => write!(f, "(exit)"),
            GetModel => write!(f, "(get-model)"),
            SetInfo(a) => write!(f, "(set-info {})", a),
            SetLogic(l) => write!(f, "(set-logic {})", l)
        }
    }
}
