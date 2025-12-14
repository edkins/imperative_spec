#[derive(Clone, Eq, PartialEq)]
pub struct Type {
    pub name: String,
    pub type_args: Vec<TypeArg>,
}

#[derive(Clone, Eq, PartialEq)]
pub enum TypeArg {
    Type(Type),
    Bound(Bound),
}

#[derive(Clone)]
pub struct Arg {
    pub name: String,
    pub mutable: bool,
    pub arg_type: Type,
}

#[derive(Clone, Eq, PartialEq)]
pub enum FuncAttribute {
    CheckDecisions(Vec<String>),
    Sees(String),
    SideEffect(String),
}

#[derive(Clone)]
pub struct FuncDef {
    pub attributes: Vec<FuncAttribute>,
    pub name: String,
    pub type_params: Vec<String>,
    pub args: Vec<Arg>,
    pub return_name: String,
    pub return_type: Type,
    pub preconditions: Vec<Expr>,
    pub postconditions: Vec<Expr>,
    pub body: Expr,
}

#[derive(Clone)]
pub enum Literal {
    I64(i64),
    U64(u64),
    Str(String),
    Bool(bool),
    Unit,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Literal{literal: Literal},
    Function{name: String, type_instantiations: Vec<Type>, mutable_args: Vec<bool>},
    SquareSequence{len: usize},
    RoundSequence{len: usize},
    UnknownSequenceAt,
    // VectorAt,
    TupleAt{len: usize, index: usize},
    // Semicolon,
    // Assign{op: AssignOp},
}

#[derive(Clone, Copy)]
pub struct CodePos(usize, usize);

impl CodePos {
    pub fn betweem(remainder0: &str, remainder1: &str) -> Self {
        CodePos(remainder0.len(), remainder1.len())
    }
}

#[derive(Clone, Default)]
pub struct ExprInfo {
    pub typ: Option<Type>,
    pub pos: Option<CodePos>,
    pub id: String,
    pub preconditions_checked: bool,
}

#[derive(Clone)]
pub enum Expr {
    Expr {
        kind: ExprKind,
        args: Vec<Expr>,
        info: ExprInfo,
    },
    Variable {
        name: String,
        info: ExprInfo,
    },
    Lambda {
        args: Vec<Arg>,
        body: Box<Expr>,
        info: ExprInfo,
    },
    Let {
        name: String,
        mutable: bool,
        typ: Option<Type>,
        value: Box<Expr>,
        body: Box<Expr>,
        info: ExprInfo,
    }
}

#[derive(Clone, Copy)]
pub enum AssignOp {
    Assign,
    AddAssign,
    SubAssign,
    MulAssign,
}

#[derive(Clone)]
pub struct SourceFile {
    pub functions: Vec<FuncDef>,
}

impl Type {
    pub fn basic(name: &str) -> Self {
        Type {
            name: name.to_owned(),
            type_args: vec![],
        }
    }
}

#[derive(Clone, Copy)]
pub enum Bound {
    MinusInfinity,
    PlusInfinity,
    U64(u64),
    I64(i64),
}

impl PartialEq for Bound {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Bound::U64(a), Bound::U64(b)) => a == b,
            (Bound::I64(a), Bound::I64(b)) => a == b,
            (Bound::U64(a), Bound::I64(b)) => {
                if *b < 0 {
                    false
                } else {
                    *a == (*b as u64)
                }
            }
            (Bound::I64(a), Bound::U64(b)) => {
                if *a < 0 {
                    false
                } else {
                    (*a as u64) == *b
                }
            }
            (Bound::MinusInfinity, Bound::MinusInfinity) => true,
            (Bound::PlusInfinity, Bound::PlusInfinity) => true,
            _ => false,
        }
    }
}

impl PartialOrd for Bound {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Bound {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match (self, other) {
            (Bound::U64(a), Bound::U64(b)) => a.cmp(b),
            (Bound::I64(a), Bound::I64(b)) => a.cmp(b),
            (Bound::U64(a), Bound::I64(b)) => {
                if *b < 0 {
                    std::cmp::Ordering::Greater
                } else {
                    (*a).cmp(&(*b as u64))
                }
            }
            (Bound::I64(a), Bound::U64(b)) => {
                if *a < 0 {
                    std::cmp::Ordering::Less
                } else {
                    (*a as u64).cmp(b)
                }
            }
            (Bound::MinusInfinity, Bound::MinusInfinity) => std::cmp::Ordering::Equal,
            (Bound::PlusInfinity, Bound::PlusInfinity) => std::cmp::Ordering::Equal,
            (Bound::MinusInfinity, _) => std::cmp::Ordering::Less,
            (_, Bound::MinusInfinity) => std::cmp::Ordering::Greater,
            (Bound::PlusInfinity, _) => std::cmp::Ordering::Greater,
            (_, Bound::PlusInfinity) => std::cmp::Ordering::Less,
        }
    }
}

impl Eq for Bound {}
