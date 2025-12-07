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
    pub arg_type: Type,
}

#[derive(Clone)]
pub struct FuncDef {
    pub attributes: Vec<Expr>,
    pub name: String,
    pub args: Vec<Arg>,
    pub return_name: Option<String>,
    pub return_type: Type,
    pub preconditions: Vec<Expr>,
    pub postconditions: Vec<Expr>,
    pub sees: Vec<String>,
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

#[derive(Clone)]
pub enum Expr {
    Literal(Literal),
    Variable(String),
    Semicolon(Box<Stmt>, Box<Expr>),
    FunctionCall { name: String, args: Vec<Expr> },
    Sequence(Vec<Expr>),
}

#[derive(Clone, Copy)]
pub enum AssignOp {
    Assign,
    PlusAssign,
    MinusAssign,
}

#[derive(Clone)]
pub enum Stmt {
    Expr(Expr),
    Let {
        name: String,
        value: Expr,
    },
    LetMut {
        name: String,
        typ: Type,
        value: Expr,
    },
    Assign {
        name: String,
        op: AssignOp,
        value: Expr,
    },
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
