#[derive(Clone, Eq, PartialEq)]
pub struct Type {
    pub name: String,
    pub type_args: Vec<TypeArg>,
}

#[derive(Clone, Eq, PartialEq)]
pub enum TypeArg {
    Type(Type),
    I64(i64),
    U64(u64),
}

#[derive(Clone)]
pub struct Arg {
    pub name: String,
    pub arg_type: Type,
}

#[derive(Clone)]
pub struct FuncDef {
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
