use std::fmt::Display;

use crate::syntax::ast::*;

impl Display for TypeArg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeArg::Type(typ) => write!(f, "{}", typ),
            TypeArg::Bound(bound) => write!(f, "{}", bound),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.name.as_str(), self.type_args.len()) {
            ("Tuple", n) if n >= 1 => {
                write!(f, "(")?;
                let t = &self.type_args[0];
                if self.type_args.len() >= 2 && self.type_args.iter().all(|arg| arg == t) {
                    write!(f, "{}", t)?;
                    write!(f, ";{}", n)?;
                } else {
                    for (i, arg) in self.type_args.iter().enumerate() {
                        write!(f, "{}", arg)?;
                        if i != self.type_args.len() - 1 || self.type_args.len() == 1 {
                            write!(f, ",")?;
                        }
                    }
                }
                write!(f, ")")
            }
            ("Vec", 1) => {
                write!(f, "[{}]", self.type_args[0])
            }
            ("Array", 2) => {
                write!(f, "[{};{}]", self.type_args[0], self.type_args[1])
            }
            _ => {
                write!(f, "{}", self.name)?;
                if !self.type_args.is_empty() {
                    write!(f, "<")?;
                    for (i, arg) in self.type_args.iter().enumerate() {
                        write!(f, "{}", arg)?;
                        if i != self.type_args.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, ">")?;
                }
                Ok(())
            }
        }
    }
}

impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Unit => write!(f, "()"),
            Literal::I64(value) => write!(f, "{}", value),
            Literal::U64(value) => write!(f, "{}", value),
            Literal::Str(value) => write!(f, "{:?}", value),
            Literal::Bool(value) => write!(f, "{}", value),
        }
    }
}

impl Display for Bound {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bound::MinusInfinity => write!(f, "-∞"),
            Bound::PlusInfinity => write!(f, "∞"),
            Bound::U64(value) => write!(f, "{}", value),
            Bound::I64(value) => write!(f, "{}", value),
        }
    }
}

#[derive(PartialEq, PartialOrd, Ord, Eq, Clone, Copy)]
enum BindingStrength {
    NeverBracket,
    Semicolon,
    Comma,
    Comparison,
    PlusMinus,
}

impl BindingStrength {
    fn open_brace(
        self,
        f: &mut std::fmt::Formatter<'_>,
        inner: BindingStrength,
    ) -> std::fmt::Result {
        if inner < self {
            write!(f, "{{")
        } else {
            Ok(())
        }
    }

    fn close_brace(
        self,
        f: &mut std::fmt::Formatter<'_>,
        inner: BindingStrength,
    ) -> std::fmt::Result {
        if inner < self {
            write!(f, "}}")
        } else {
            Ok(())
        }
    }
}

impl CallArg {
    fn fmt_with_binding_strength(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        strength: BindingStrength,
    ) -> std::fmt::Result {
        match self {
            CallArg::Expr(expr) => expr.fmt_with_binding_strength(f, strength),
            CallArg::MutVar { name, typ } => {
                if let Some(typ) = typ {
                    write!(f, "mut {}: {}", name, typ)
                } else {
                    write!(f, "mut {}", name)
                }
            }
        }
    }
}

impl Expr {
    fn fmt_with_binding_strength(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        strength: BindingStrength,
    ) -> std::fmt::Result {
        match self {
            Expr::Literal(literal) => write!(f, "{}", literal),
            Expr::Variable { name, typ } => {
                write!(f, "{}", name)?;
                if let Some(typ) = typ {
                    write!(f, ":{}", typ)
                } else {
                    Ok(())
                }
            }
            Expr::FunctionCall {
                name,
                args,
                type_instantiations,
                return_type,
            } => {
                match name as &str {
                    "==" | "!=" | "<" | "<=" | ">" | ">=" => {
                        strength.open_brace(f, BindingStrength::Comparison)?;
                        args[0].fmt_with_binding_strength(f, BindingStrength::Comparison)?;
                        write!(f, " {} ", name)?;
                        args[1].fmt_with_binding_strength(f, BindingStrength::Comparison)?;
                        strength.close_brace(f, BindingStrength::Comparison)?;
                    }
                    "+" | "-" => {
                        strength.open_brace(f, BindingStrength::PlusMinus)?;
                        args[0].fmt_with_binding_strength(f, BindingStrength::PlusMinus)?;
                        write!(f, " {} ", name)?;
                        args[1].fmt_with_binding_strength(f, BindingStrength::PlusMinus)?;
                        strength.close_brace(f, BindingStrength::PlusMinus)?;
                    }
                    _ => {
                        write!(f, "{}", name)?;
                        if !type_instantiations.is_empty() {
                            write!(f, "<")?;
                            for (i, typ) in type_instantiations.iter().enumerate() {
                                write!(f, "{}", typ)?;
                                if i != type_instantiations.len() - 1 {
                                    write!(f, ",")?;
                                }
                            }
                            write!(f, ">")?;
                        }
                        write!(f, "(")?;
                        for (i, arg) in args.iter().enumerate() {
                            arg.fmt_with_binding_strength(f, BindingStrength::Comma)?;
                            if i != args.len() - 1 {
                                write!(f, ", ")?;
                            }
                        }
                        write!(f, ")")?;
                    }
                }
                if let Some(return_type) = return_type {
                    // write!(f, ":{}", return_type)?;
                    Ok(())
                } else {
                    Ok(())
                }
            }
            Expr::Semicolon(stmt, expr) => {
                strength.open_brace(f, BindingStrength::Semicolon)?;
                stmt.fmt(f)?;
                writeln!(f, ";")?;
                expr.fmt_with_binding_strength(f, BindingStrength::Semicolon)?;
                strength.close_brace(f, BindingStrength::Semicolon)
            }
            Expr::SquareSequence { elems, elem_type } => {
                write!(f, "[")?;
                for (i, element) in elems.iter().enumerate() {
                    element.fmt_with_binding_strength(f, BindingStrength::Comma)?;
                    if i != elems.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                if let Some(typ) = elem_type {
                    write!(f, ":{}", typ)?;
                }
                write!(f, "]")
            }
            Expr::RoundSequence { elems } => {
                write!(f, "(")?;
                for (i, element) in elems.iter().enumerate() {
                    element.fmt_with_binding_strength(f, BindingStrength::Comma)?;
                    if i != elems.len() - 1 || elems.len() == 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            Expr::Lambda { args, body } => {
                write!(f, "|")?;
                for (i, arg) in args.iter().enumerate() {
                    write!(f, "{}: {}", arg.name, arg.arg_type)?;
                    if i != args.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "| ")?;
                body.fmt_with_binding_strength(f, BindingStrength::NeverBracket)
            }
            Expr::SeqAt { seq, index } => {
                seq.fmt_with_binding_strength(f, BindingStrength::NeverBracket)?;
                write!(f, "[")?;
                index.fmt_with_binding_strength(f, BindingStrength::NeverBracket)?;
                write!(f, "]")
            }
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_with_binding_strength(f, BindingStrength::NeverBracket)
    }
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl Display for Arg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.mutable {
            write!(f, "mut {}: {}", self.name, self.arg_type)
        } else {
            write!(f, "{}: {}", self.name, self.arg_type)
        }
    }
}

impl Display for FuncAttribute {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FuncAttribute::CheckDecisions(decisions) => {
                writeln!(f, "#[check_decisions({})]", decisions.join(", "))
            }
            FuncAttribute::Sees(module) => {
                writeln!(f, "#[sees({})]", module)
            }
            FuncAttribute::SideEffect(effect) => {
                writeln!(f, "#[side_effect({})]", effect)
            }
        }
    }
}

impl Display for FuncDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for attrib in &self.attributes {
            writeln!(f, "{}", attrib)?;
        }
        write!(f, "fn {}(", self.name)?;
        for (i, arg) in self.args.iter().enumerate() {
            write!(f, "{}", arg)?;
            if i != self.args.len() - 1 {
                write!(f, ", ")?;
            }
        }
        writeln!(f, ") -> ({}:{})", self.return_name, self.return_type)?;
        if !self.preconditions.is_empty() {
            write!(f, "requires ")?;
            for (i, precond) in self.preconditions.iter().enumerate() {
                precond.fmt_with_binding_strength(f, BindingStrength::Comma)?;
                if i != self.preconditions.len() - 1 {
                    write!(f, ", ")?;
                }
            }
            writeln!(f)?;
        }
        if !self.postconditions.is_empty() {
            write!(f, "ensures ")?;
            for (i, postcond) in self.postconditions.iter().enumerate() {
                postcond.fmt_with_binding_strength(f, BindingStrength::Comma)?;
                if i != self.postconditions.len() - 1 {
                    write!(f, ", ")?;
                }
            }
            writeln!(f)?;
        }
        writeln!(f, "{{")?;
        self.body
            .fmt_with_binding_strength(f, BindingStrength::NeverBracket)?;
        write!(f, "\n}}")
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stmt::Expr(expr) => write!(f, "{}", expr),
            Stmt::Let {
                name,
                mutable,
                typ,
                value,
            } => {
                if let Some(typ) = typ {
                    if *mutable {
                        write!(f, "let mut {}: {} = {}", name, typ, value)
                    } else {
                        write!(f, "let {}: {} = {}", name, typ, value)
                    }
                } else {
                    if *mutable {
                        write!(f, "let mut {} = {}", name, value)
                    } else {
                        write!(f, "let {} = {}", name, value)
                    }
                }
            }
            Stmt::Assign { name, op, value } => {
                let op_str = match op {
                    AssignOp::Assign => "=",
                    AssignOp::AddAssign => "+=",
                    AssignOp::SubAssign => "-=",
                    AssignOp::MulAssign => "*=",
                };
                write!(f, "{} {} ", name, op_str)?;
                value.fmt_with_binding_strength(f, BindingStrength::PlusMinus)
            }
        }
    }
}

impl Display for SourceFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for func in &self.functions {
            writeln!(f, "{}", func)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::syntax::ast::*;

    fn v(name: &str) -> Expr {
        Expr::Variable {
            name: name.to_owned(),
            typ: None,
        }
    }

    #[test]
    fn funcdef() {
        let func = FuncDef {
            attributes: vec![],
            name: "add".to_string(),
            type_params: vec![],
            args: vec![
                Arg {
                    name: "a".to_owned(),
                    mutable: false,
                    arg_type: Type {
                        name: "i32".to_owned(),
                        type_args: vec![],
                    },
                },
                Arg {
                    name: "b".to_owned(),
                    mutable: false,
                    arg_type: Type {
                        name: "i32".to_owned(),
                        type_args: vec![],
                    },
                },
            ],
            preconditions: vec![],
            postconditions: vec![],
            return_name: "__ret__".to_owned(),
            return_type: Type {
                name: "i32".to_owned(),
                type_args: vec![],
            },
            body: Expr::FunctionCall {
                name: "sum".to_owned(),
                args: vec![CallArg::Expr(v("a")), CallArg::Expr(v("b"))],
                type_instantiations: vec![],
                return_type: None,
            },
        };

        let expected = "fn add(a: i32, b: i32) -> i32\n{\nsum(a, b)\n}";
        let actual = format!("{}", func);
        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_semicolons() {
        let semi = Expr::Semicolon(
            Box::new(Stmt::Expr(v("x"))),
            Box::new(Expr::Semicolon(
                Box::new(Stmt::Expr(v("y"))),
                Box::new(v("z")),
            )),
        );
        let expected = "x;\ny;\nz";
        let actual = format!("{}", semi);
        assert_eq!(actual, expected);
    }

    #[test]
    fn func_with_semicolon_arg() {
        let func = FuncDef {
            attributes: vec![],
            name: "example".to_string(),
            type_params: vec![],
            args: vec![Arg {
                name: "x".to_owned(),
                mutable: false,
                arg_type: Type {
                    name: "i32".to_owned(),
                    type_args: vec![],
                },
            }],
            return_type: Type {
                name: "i32".to_owned(),
                type_args: vec![],
            },
            preconditions: vec![],
            postconditions: vec![],
            return_name: "__ret__".to_owned(),
            body: Expr::FunctionCall {
                name: "process".to_owned(),
                args: vec![
                    CallArg::Expr(v("x")),
                    CallArg::Expr(Expr::Semicolon(
                        Box::new(Stmt::Let {
                            name: "y".to_owned(),
                            mutable: false,
                            typ: None,
                            value: Expr::Literal(Literal::I64(10)),
                        }),
                        Box::new(v("y")),
                    )),
                ],
                type_instantiations: vec![],
                return_type: None,
            },
        };

        let expected = "process(x, {let y = 10;\ny})";
        let actual = format!("{}", func.body);
        assert_eq!(actual, expected);
    }
}
