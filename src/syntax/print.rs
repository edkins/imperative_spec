use std::fmt::Display;

use crate::syntax::ast::*;

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::I64(value) => write!(f, "{}", value),
            Literal::U64(value) => write!(f, "{}", value),
            Literal::Str(value) => write!(f, "{:?}", value),
        }
    }
}

#[allow(dead_code)]
#[derive(PartialEq, PartialOrd, Ord, Eq, Clone, Copy)]
enum BindingStrength {
    NeverBracket,
    Semicolon,
    Comma,
    AlwaysBracket,
}

impl BindingStrength {
    fn open_brace(self, f: &mut std::fmt::Formatter<'_>, inner: BindingStrength) -> std::fmt::Result {
        if inner < self {
            write!(f, "{{")
        } else {
            Ok(())
        }
    }

    fn close_brace(self, f: &mut std::fmt::Formatter<'_>, inner: BindingStrength) -> std::fmt::Result {
        if inner < self {
            write!(f, "}}")
        } else {
            Ok(())
        }
    }
}

impl Expr {
    fn fmt_with_binding_strength(&self, f: &mut std::fmt::Formatter<'_>, strength: BindingStrength) -> std::fmt::Result {
        match self {
            Expr::Literal(literal) => write!(f, "{}", literal),
            Expr::Variable(x) => write!(f, "{}", x),
            Expr::FunctionCall { name, args } =>
            {
                write!(f, "{}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    arg.fmt_with_binding_strength(f, BindingStrength::Comma)?;
                    if i != args.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            Expr::Semicolon(stmt, expr) => {
                strength.open_brace(f, BindingStrength::Semicolon)?;
                stmt.fmt(f)?;
                write!(f, ";\n")?;
                expr.fmt_with_binding_strength(f, BindingStrength::Semicolon)?;
                strength.close_brace(f, BindingStrength::Semicolon)
            },
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_with_binding_strength(f, BindingStrength::NeverBracket)
    }
}

impl Display for FuncDef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fn {}(", self.name)?;
        for (i, arg) in self.args.iter().enumerate() {
            write!(f, "{}", arg.name)?;
            if i != self.args.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ") {{\n")?;
        self.body.fmt_with_binding_strength(f, BindingStrength::NeverBracket)?;
        write!(f, "\n}}")
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Stmt::Expr(expr) => write!(f, "{}", expr),
            Stmt::Let { name, value } => write!(f, "let {} = {}", name, value),
        }
    }
}

impl Display for SourceFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for func in &self.functions {
            write!(f, "{}\n", func)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::syntax::ast::*;

    #[test]
    fn funcdef() {
        let func = FuncDef {
            name: "add".to_string(),
            args: vec![
                Arg {
                    name: "a".to_owned(),
                    arg_type: Type { name: "i32".to_owned() },
                },
                Arg {
                    name: "b".to_owned(),
                    arg_type: Type { name: "i32".to_owned() },
                },
            ],
            return_type: Type { name: "i32".to_owned() },
            body: Expr::FunctionCall {
                name: "sum".to_owned(),
                args: vec![
                    Expr::Variable("a".to_owned()),
                    Expr::Variable("b".to_owned()),
                ],
            },
        };

        let expected = "add(a, b) {\nsum(a, b)\n}";
        let actual = format!("{}", func);
        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_semicolons() {
        let semi = Expr::Semicolon(
            Box::new(Stmt::Expr(Expr::Variable("x".to_owned()))),
            Box::new(Expr::Semicolon(Box::new(Stmt::Expr(Expr::Variable("y".to_owned()))),
                Box::new(Expr::Variable("z".to_owned())))),
        );
        let expected = "x;\ny;\nz";
        let actual = format!("{}", semi);
        assert_eq!(actual, expected);
    }

    #[test]
    fn func_with_semicolon_arg() {
        let func = FuncDef {
            name: "example".to_string(),
            args: vec![
                Arg {
                    name: "x".to_owned(),
                    arg_type: Type { name: "i32".to_owned() },
                },
            ],
            return_type: Type { name: "i32".to_owned() },
            body: Expr::FunctionCall {
                name: "process".to_owned(),
                args: vec![
                    Expr::Variable("x".to_owned()),
                    Expr::Semicolon(
                        Box::new(Stmt::Let {
                            name: "y".to_owned(),
                            value: Expr::Literal(Literal::I64(10)),
                        }),
                        Box::new(Expr::Variable("y".to_owned())),
                    ),
                ],
            },
        };

        let expected = "process(x, {let y = 10;\ny})";
        let actual = format!("{}", func.body);
        assert_eq!(actual, expected);
    }
}