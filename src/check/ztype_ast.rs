use crate::syntax::ast::{Arg, Literal, Type, TypeArg};

#[derive(Clone)]
pub enum TExpr {
    Literal(Literal),
    Variable {
        name: String,
        typ: Type,
    },
    Semicolon(Box<TStmt>, Box<TExpr>),
    FunctionCall {
        name: String,
        args: Vec<TExpr>,
        return_type: Type,
    },
    Sequence {
        elements: Vec<TExpr>,
        elem_type: Type,
    },
    EmptySequence,
    Lambda {
        args: Vec<Arg>,
        body: Box<TExpr>,
    },
}

#[derive(Clone)]
pub enum TStmt {
    Expr(TExpr),
    Let {
        name: String,
        typ: Type,
        mutable: bool,
        value: TExpr,
    },
    Assign {
        name: String,
        value: TExpr,
    },
}

impl Literal {
    pub fn typ(&self) -> Type {
        match self {
            Literal::Unit => Type::basic("void"),
            Literal::U64(_) => Type::basic("int"),
            Literal::I64(_) => Type::basic("int"),
            Literal::Str(_) => Type::basic("str"),
            Literal::Bool(_) => Type::basic("bool"),
        }
    }
}

impl TExpr {
    pub fn typ(&self) -> Type {
        match self {
            TExpr::Literal(lit) => lit.typ(),
            TExpr::Variable { typ, .. } => typ.clone(),
            TExpr::Semicolon(_, expr) => expr.typ(),
            TExpr::FunctionCall { return_type, .. } => return_type.clone(),
            TExpr::Sequence { elem_type, .. } => Type {
                name: "Seq".to_owned(),
                type_args: vec![TypeArg::Type(elem_type.clone())],
            },
            TExpr::EmptySequence => Type::basic("EmptySeq"),
            TExpr::Lambda { args, body } => {
                let arg_types = args
                    .iter()
                    .map(|arg| arg.arg_type.clone())
                    .collect::<Vec<_>>();
                Type::lambda(&arg_types, &body.typ())
            }
        }
    }
}

pub struct TFuncDef {
    pub name: String,
    pub args: Vec<Arg>,
    pub return_name: String,
    pub return_type: Type,
    pub preconditions: Vec<TExpr>,
    pub postconditions: Vec<TExpr>,
    pub sees: Vec<String>,
    pub body: TExpr,
}

pub struct TSourceFile {
    pub functions: Vec<TFuncDef>,
}

impl std::fmt::Display for TExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TExpr::Literal(lit) => write!(f, "{}", lit),
            TExpr::Variable { name, typ } => write!(f, "{}:{}", name, typ),
            TExpr::Semicolon(stmt, expr) => write!(f, "{};\n{}", stmt, expr),
            TExpr::FunctionCall { name, args, .. } => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    write!(f, "{}", arg)?;
                    if i != args.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            TExpr::Sequence { elements, .. } => {
                write!(f, "[")?;
                for (i, element) in elements.iter().enumerate() {
                    write!(f, "{}", element)?;
                    if i != elements.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "]")
            }
            TExpr::EmptySequence => write!(f, "[]"),
            TExpr::Lambda { args, body } => {
                write!(f, "|")?;
                for (i, arg) in args.iter().enumerate() {
                    write!(f, "{}: {}", arg.name, arg.arg_type)?;
                    if i != args.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "| {}", body)
            }
        }
    }
}

impl std::fmt::Display for TStmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TStmt::Expr(expr) => write!(f, "{}", expr),
            TStmt::Let {
                name,
                typ,
                mutable,
                value,
            } => {
                if *mutable {
                    write!(f, "let mut {}: {} = {}", name, typ, value)
                } else {
                    write!(f, "let {}: {} = {}", name, typ, value)
                }
            }
            TStmt::Assign { name, value } => {
                write!(f, "{} = {}", name, value)
            }
        }
    }
}

pub fn display_texprs(types: &[TExpr]) -> String {
    let mut result = String::new();
    for (i, expr) in types.iter().enumerate() {
        result.push_str(&format!("{}", expr));
        if i != types.len() - 1 {
            result.push_str(", ");
        }
    }
    result
}

impl std::fmt::Display for TFuncDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "fn {}(", self.name)?;
        for arg in &self.args {
            writeln!(f, "    {}: {},", arg.name, arg.arg_type)?;
        }
        writeln!(f, ") -> {}: {}", self.return_name, self.return_type)?;
        if !self.preconditions.is_empty() {
            writeln!(f, "  requires")?;
            for pre in &self.preconditions {
                writeln!(f, "     {}", pre)?;
            }
        }
        if !self.postconditions.is_empty() {
            writeln!(f, "  ensures")?;
            for post in &self.postconditions {
                writeln!(f, "     {}", post)?;
            }
        }
        writeln!(f, "{{")?;
        writeln!(f, "  {}", self.body)?;
        writeln!(f, "}}")
    }
}

impl std::fmt::Display for TSourceFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for func in &self.functions {
            writeln!(f, "{}", func)?;
        }
        Ok(())
    }
}
