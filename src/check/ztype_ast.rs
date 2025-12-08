use crate::{
    check::overloads::Optimization,
    syntax::ast::{Arg, Literal, Type, TypeArg},
};

// #[derive(Clone)]
// pub enum SizedLiteral {
//     U32(u32),
//     U64(u64),
//     I32(i32),
//     I64(i64),
// }

#[derive(Clone)]
pub enum TExpr {
    Literal(Literal),
    // SizedLiteral(SizedLiteral),
    Variable {
        name: String,
        typ: Type,
    },
    Semicolon(Box<TStmt>, Box<TExpr>),
    FunctionCall {
        name: String,
        args: Vec<TExpr>,
        return_type: Type,
        optimizations: Vec<Optimization>,
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
        type_declared: bool,
        value: TExpr,
    },
    Assign {
        name: String,
        typ: Type,
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

#[derive(Clone, Eq, PartialEq)]
pub enum TFuncAttribute {
    CheckDecisions(Vec<String>),
    Sees(String),
    SideEffect(String),
}

#[derive(Clone)]
pub struct TFuncDef {
    pub attributes: Vec<TFuncAttribute>,
    pub name: String,
    pub args: Vec<Arg>,
    pub return_name: String,
    pub return_type: Type,
    pub preconditions: Vec<TExpr>,
    pub postconditions: Vec<TExpr>,
    pub body: Option<TExpr>,  // None for builtin funcs
    pub optimizations: Vec<Optimization>,
    pub type_params: Vec<String>,
}

pub struct TSourceFile {
    pub functions: Vec<TFuncDef>,
}

impl std::fmt::Debug for TExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl std::fmt::Display for TExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TExpr::Literal(lit) => write!(f, "{}", lit),
            TExpr::Variable { name, typ } => write!(f, "{}:{}", name, typ),
            TExpr::Semicolon(stmt, expr) => write!(f, "{};\n{}", stmt, expr),
            TExpr::FunctionCall {
                name,
                args,
                return_type,
                optimizations,
            } => {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    write!(f, "{}", arg)?;
                    if i != args.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "):{}", return_type)?;
                if !optimizations.is_empty() {
                    write!(f, " {{ ")?;
                    for (i, opt) in optimizations.iter().enumerate() {
                        write!(f, "{}", opt.debug_name)?;
                        if i != optimizations.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, " }}")?;
                }
                Ok(())
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
                type_declared,
                mutable,
                value,
            } => {
                write!(f, "let ")?;
                if *mutable {
                    write!(f, "mut ")?;
                }
                if *type_declared {
                    write!(f, "{}: {} = {}", name, typ, value)
                } else {
                    write!(f, "{}: {{{}}} = {}", name, typ, value)
                }
            }
            TStmt::Assign { name, value, .. } => {
                write!(f, "{} = {}", name, value)
            }
        }
    }
}

impl std::fmt::Display for TFuncDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for attr in &self.attributes {
            match attr {
                TFuncAttribute::CheckDecisions(decisions) => {
                    writeln!(f, "#[check_decisions({})]", decisions.join(", "))?;
                }
                TFuncAttribute::Sees(module) => {
                    writeln!(f, "#[sees({})]", module)?;
                }
                TFuncAttribute::SideEffect(effect) => {
                    writeln!(f, "#[side_effect({})]", effect)?;
                }
            }
        }
        writeln!(f, "fn {}", self.name)?;
        if !self.type_params.is_empty() {
            write!(f, "<")?;
            for (i, param) in self.type_params.iter().enumerate() {
                write!(f, "{}", param)?;
                if i != self.type_params.len() - 1 {
                    write!(f, ", ")?;
                }
            }
            writeln!(f, ">")?;
        }
        writeln!(f, "(")?;
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
        if let Some(body) = &self.body {
            writeln!(f, "{{")?;
            writeln!(f, "  {}", body)?;
            writeln!(f, "}}")?;
        }
        Ok(())
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
