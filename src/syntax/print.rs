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

impl std::fmt::Debug for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
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
    Implication,
    Disjunction,
    Conjunction,
    Comparison,
    PlusMinus,
    TimesDivide,
    AlwaysBracket,
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

    fn open_paren(
        self,
        f: &mut std::fmt::Formatter<'_>,
        inner: BindingStrength,
    ) -> std::fmt::Result {
        if inner < self {
            write!(f, "(")
        } else {
            Ok(())
        }
    }

    fn close_paren(
        self,
        f: &mut std::fmt::Formatter<'_>,
        inner: BindingStrength,
    ) -> std::fmt::Result {
        if inner < self {
            write!(f, ")")
        } else {
            Ok(())
        }
    }
}

fn binop_binding_strength(op: &str) -> Option<BindingStrength> {
    match op {
        "=" | "+=" | "-=" | "*=" => Some(BindingStrength::Semicolon),
        "==>" => Some(BindingStrength::Implication),
        "||" => Some(BindingStrength::Disjunction),
        "&&" => Some(BindingStrength::Conjunction),
        "==" | "!=" | "<" | "<=" | ">" | ">=" => Some(BindingStrength::Comparison),
        "+" | "-" => Some(BindingStrength::PlusMinus),
        "*" | "/" | "%" => Some(BindingStrength::TimesDivide),
        _ => None,
    }
}

impl Expr {
    fn fmt_with_binding_strength(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        strength: BindingStrength,
    ) -> std::fmt::Result {
        match self {
            Expr::Expr { kind, args, .. } => match kind {
                ExprKind::Literal { literal } => write!(f, "{}", literal),
                ExprKind::Function { name, type_instantiations, .. } => {
                    if name == ";" && args.len() == 2 {
                        strength.open_brace(f, BindingStrength::Semicolon)?;
                        args[0].fmt_with_binding_strength(f, BindingStrength::Semicolon)?;
                        writeln!(f, ";")?;
                        args[1].fmt_with_binding_strength(f, BindingStrength::Semicolon)?;
                        strength.close_brace(f, BindingStrength::Semicolon)
                    } else if let Some(op_strength) = binop_binding_strength(name) {
                        strength.open_paren(f, op_strength)?;
                        args[0].fmt_with_binding_strength(f, op_strength)?;
                        write!(f, " {} ", name)?;
                        args[1].fmt_with_binding_strength(f, op_strength)?;
                        strength.close_paren(f, op_strength)
                    } else {
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
                        Ok(())
                    }
                }
                ExprKind::SquareSequence { .. } => {
                    write!(f, "[")?;
                    for (i, element) in args.iter().enumerate() {
                        element.fmt_with_binding_strength(f, BindingStrength::Comma)?;
                        if i != args.len() - 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, "]")
                }
                ExprKind::RoundSequence { .. } => {
                    write!(f, "(")?;
                    for (i, element) in args.iter().enumerate() {
                        element.fmt_with_binding_strength(f, BindingStrength::Comma)?;
                        if i != args.len() - 1 || args.len() == 1 {
                            write!(f, ", ")?;
                        }
                    }
                    write!(f, ")")
                }
                ExprKind::UnknownSequenceAt => {
                    args[0].fmt_with_binding_strength(f, BindingStrength::AlwaysBracket)?;
                    write!(f, "?[")?;
                    args[1].fmt_with_binding_strength(f, BindingStrength::NeverBracket)?;
                    write!(f, "]")
                }
                ExprKind::TupleAt { index, .. } => {
                    args[0].fmt_with_binding_strength(f, BindingStrength::AlwaysBracket)?;
                    write!(f, ".{}", index)
                }
            }
            Expr::Variable { name, .. } => {
                write!(f, "{}", name)
            }
            Expr::Lambda { args, body, .. } => {
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
            Expr::Let { name, mutable, typ, value, body, .. } => {
                strength.open_brace(f, BindingStrength::Semicolon)?;
                if *mutable {
                    write!(f, "let mut {}", name)?;
                } else {
                    write!(f, "let {}", name)?;
                }
                if let Some(typ) = typ {
                    write!(f, ": {}", typ)?;
                }
                write!(f, " = ")?;
                value.fmt_with_binding_strength(f, BindingStrength::NeverBracket)?;
                writeln!(f, ";")?;
                body.fmt_with_binding_strength(f, BindingStrength::Semicolon)?;
                strength.close_brace(f, BindingStrength::Semicolon)
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
            write!(f, "mut {}:{}", self.name, self.arg_type)
        } else {
            write!(f, "{}:{}", self.name, self.arg_type)
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
        write!(f, "fn {}", self.name)?;
        if !self.type_params.is_empty() {
            write!(f, "<")?;
            for (i, tp) in self.type_params.iter().enumerate() {
                write!(f, "{}", tp)?;
                if i != self.type_params.len() - 1 {
                    write!(f, ", ")?;
                }
            }
            write!(f, ">")?;
        }
        write!(f, "(")?;
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
    use crate::syntax::{ast::*, mk};

    fn v(name: &str) -> Expr {
        mk::untyped_var(name.to_owned())
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
            body: mk::immut_function_call(
                "sum",
                vec![v("a"), v("b")],
            ),
        };

        let expected = "fn add(a:i32, b:i32) -> (__ret__:i32)\n{\nsum(a, b)\n}";
        let actual = format!("{}", func);
        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_semicolons() {
        let semi = v("x").semicolon(v("y").semicolon(v("z")));
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
            body: mk::immut_function_call("process",
                vec![
                    v("x"),
                    mk::let_expr(
                        "y".to_owned(),
                        false,
                        None,
                        Literal::I64(10).as_expr(),
                        v("y"),
                    ),
                ],
            ),
        };

        let expected = "process(x, {let y = 10;\ny})";
        let actual = format!("{}", func.body);
        assert_eq!(actual, expected);
    }
}
