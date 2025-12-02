#[derive(Clone)]
pub struct Type {
    pub name: String,
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
    pub return_type: Type,
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
    FunctionCall {
        name: String,
        args: Vec<Expr>,
    },
}

#[derive(Clone)]
pub enum Stmt {
    Expr(Expr),
    Let {
        name: String,
        value: Expr,
    },
}

#[derive(Clone)]
pub struct SourceFile {
    pub functions: Vec<FuncDef>,
}