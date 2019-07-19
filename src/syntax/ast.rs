use std::fmt;

use super::{Location, Localisable, Located};
use crate::PList;

/**
 * Symbol.
 */
#[derive(Clone, Debug)]
pub struct Symbol<F: Clone> {
    pub location: Location<F>,
    pub id: String
}

impl<F: Clone> Symbol<F> {
    pub fn format<T: fmt::Display>(t: T) -> Symbol<F> {
        Symbol {
            location: Location::nowhere(),
            id: format!("{}", t)
        }
    }
}

impl<F: Clone> Localisable<F> for Symbol<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

impl<F: Clone> PartialEq<str> for Symbol<F> {
    fn eq(&self, other: &str) -> bool {
        self.id == other
    }
}

impl<F: Clone> PartialEq<String> for Symbol<F> {
    fn eq(&self, other: &String) -> bool {
        self.id == *other
    }
}

impl<F: Clone> fmt::Display for Symbol<F> {
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
pub struct Index<F: Clone> {
    pub location: Location<F>,
    pub kind: IndexKind<F>
}

impl<F: Clone> fmt::Display for Index<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

#[derive(Clone, Debug)]
pub enum IndexKind<F: Clone> {
    Numeral(i64),
    Symbol(Symbol<F>)
}

impl<F: Clone> fmt::Display for IndexKind<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use IndexKind::*;
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
pub struct Ident<F: Clone> {
    pub location: Location<F>,
    pub id: Symbol<F>,
    pub indexes: Vec<Index<F>>
}

impl<F: Clone> From<Symbol<F>> for Ident<F> {
    fn from(sym: Symbol<F>) -> Self {
        Ident {
            location: sym.location.clone(),
            id: sym,
            indexes: Vec::new()
        }
    }
}

impl<F: Clone> Localisable<F> for Ident<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

impl<F: Clone> fmt::Display for Ident<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.indexes.is_empty() {
            self.id.fmt(f)
        } else {
            write!(f, "(_ {} {})", self.id, PList(&self.indexes))
        }
    }
}

#[derive(Clone)]
pub struct Keyword<F: Clone> {
    pub location: Location<F>,
    pub id: String
}

impl<F: Clone> Localisable<F> for Keyword<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

impl<F: Clone> fmt::Display for Keyword<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.id.fmt(f)
    }
}

/**
 * <attribute> ::= <keyword> | <keyword> <attribute_value>
 */
#[derive(Clone)]
pub struct Attribute<F: Clone> {
    pub location: Location<F>,
    pub key: Keyword<F>,
    pub value: Option<AttributeValue<F>>
}

impl<F: Clone> fmt::Display for Attribute<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.value {
            Some(value) => {
                write!(f, "{} {}", self.key, value)
            },
            None => self.key.fmt(f)
        }
    }
}

impl<F: Clone> Localisable<F> for Attribute<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

/**
 * <attribute_value> ::= <spec_const> | <symbol> | <s_expr*>
 */
#[derive(Clone)]
pub struct AttributeValue<F: Clone> {
    pub location: Location<F>,
    pub kind: AttributeValueKind<F>
}

impl<F: Clone> fmt::Display for AttributeValue<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

impl<F: Clone> Localisable<F> for AttributeValue<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

#[derive(Clone)]
pub enum AttributeValueKind<F: Clone> {
    // Const(Constant),
    Sym(Symbol<F>),
    List(Vec<SExpr<F>>)
}

impl<F: Clone> fmt::Display for AttributeValueKind<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use AttributeValueKind::*;
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
pub struct SExpr<F: Clone> {
    pub location: Location<F>,
    pub kind: SExprKind<F>
}

impl<F: Clone> fmt::Display for SExpr<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

#[derive(Clone)]
pub enum SExprKind<F: Clone> {
    // Const(Constant),
    Sym(Symbol<F>),
    Keyword(Keyword<F>),
    List(Vec<SExpr<F>>)
}

impl<F: Clone> fmt::Display for SExprKind<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use SExprKind::*;
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
pub struct Sort<F: Clone> {
    pub location: Location<F>,
    pub id: Ident<F>,
    pub parameters: Vec<Sort<F>>
}

impl<F: Clone> Localisable<F> for Sort<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

impl<F: Clone> fmt::Display for Sort<F> {
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
pub struct Term<F: Clone> {
    pub location: Location<F>,
    pub kind: TermKind<F>
}

impl<F: Clone> Localisable<F> for Term<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

impl<F: Clone> fmt::Display for Term<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

#[derive(Clone)]
pub enum TermKind<F: Clone> {
    // Const(Constant),
    Ident(Ident<F>),
    Let {
        bindings: Vec<Binding<F>>,
        body: Box<Term<F>>
    },
    Forall {
        vars: Vec<SortedVar<F>>,
        body: Box<Term<F>>
    },
    Exists {
        vars: Vec<SortedVar<F>>,
        body: Box<Term<F>>
    },
    Match {
        term: Box<Term<F>>,
        cases: Vec<MatchCase<F>>
    },
    Apply {
        id: Ident<F>,
        args: Box<Vec<Term<F>>>
    }
}

impl<F: Clone> fmt::Display for TermKind<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use TermKind::*;
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
pub struct MatchCase<F: Clone> {
    pub location: Location<F>,
    pub pattern: Pattern<F>,
    pub term: Box<Term<F>>
}

impl<F: Clone> fmt::Display for MatchCase<F> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({} {})", self.pattern, self.term)
    }
}

#[derive(Clone)]
pub struct Pattern<F: Clone> {
    pub location: Location<F>,
    pub constructor: Symbol<F>,
    pub args: Vec<Symbol<F>>
}

impl<F: Clone> fmt::Display for Pattern<F> {
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
pub struct Binding<F: Clone> {
    pub location: Location<F>,
    pub id: Symbol<F>,
    pub value: Box<Term<F>>
}

impl<F: Clone> fmt::Display for Binding<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.id, self.value)
    }
}

/**
 * <sorted_var> ::= ( <symbol> <sort> )
 */
#[derive(Clone)]
pub struct SortedVar<F: Clone> {
    pub location: Location<F>,
    pub id: Symbol<F>,
    pub sort: Sort<F>
}

impl<F: Clone> fmt::Display for SortedVar<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.id, self.sort)
    }
}

/**
 * <datatype_dec> ::= ( <constructor_dec>+ )
 *                  | ( par ( <symbol>+ ) <constructor_dec>+ )
 */
#[derive(Clone)]
pub struct DataTypeDeclaration<F: Clone> {
    pub location: Location<F>,
    pub parameters: Vec<Symbol<F>>,
    pub constructors: Vec<ConstructorDeclaration<F>>
}

impl<F: Clone> Localisable<F> for DataTypeDeclaration<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

impl<F: Clone> fmt::Display for DataTypeDeclaration<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({})", PList(&self.constructors))
    }
}

/**
 * <constructor_dec> ::= ( <symbol> <selector_dec>* )
 */
#[derive(Clone)]
pub struct ConstructorDeclaration<F: Clone> {
    pub location: Location<F>,
    pub id: Symbol<F>,
    pub selectors: Vec<SelectorDeclaration<F>>
}

impl<F: Clone> Localisable<F> for ConstructorDeclaration<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

impl<F: Clone> fmt::Display for ConstructorDeclaration<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.id, PList(&self.selectors))
    }
}

/**
 * <selector_dec> ::= ( <symbol> <sort> )
 */
#[derive(Clone)]
pub struct SelectorDeclaration<F: Clone> {
    pub location: Location<F>,
    pub id: Symbol<F>,
    pub sort: Sort<F>
}

impl<F: Clone> Localisable<F> for SelectorDeclaration<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

impl<F: Clone> fmt::Display for SelectorDeclaration<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.id, self.sort)
    }
}

/**
 * <sort_dec> ::= ( <symbol> <numeral> )
 */
#[derive(Clone)]
pub struct SortDeclaration<F: Clone> {
    pub location: Location<F>,
    pub id: Symbol<F>,
    pub arity: Located<i64, F>
}

impl<F: Clone> Localisable<F> for SortDeclaration<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

impl<F: Clone> fmt::Display for SortDeclaration<F> {
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
pub struct Command<F: Clone> {
    pub location: Location<F>,
    pub kind: CommandKind<F>
}

impl<F: Clone> Localisable<F> for Command<F> {
    fn location(&self) -> &Location<F> {
        &self.location
    }
}

impl<F: Clone> fmt::Display for Command<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.kind.fmt(f)
    }
}

#[derive(Clone)]
pub enum CommandKind<F: Clone> {
    Assert(Term<F>),
    CheckSat,
    DeclareConst(Symbol<F>, Sort<F>),
    DeclareDatatype(Symbol<F>, DataTypeDeclaration<F>),
    DeclareDatatypes(Vec<SortDeclaration<F>>, Vec<DataTypeDeclaration<F>>),
    DeclareFun(Symbol<F>, Vec<Sort<F>>, Sort<F>),
    Exit,
    GetModel,
    SetInfo(Attribute<F>),
    SetLogic(Symbol<F>)
}

impl<F: Clone> fmt::Display for CommandKind<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use CommandKind::*;
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
