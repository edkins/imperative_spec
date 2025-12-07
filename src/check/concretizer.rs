use std::collections::HashMap;

use crate::{check::ztype_ast::{TExpr, TStmt}, syntax::ast::Type};

struct CEnv {
    uses: HashMap<String, Vec<Type>>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum TypeSize {
    S32,
    S64,
    Inf,
}

impl Type {
    fn size(&self) -> TypeSize {
        match self.name.as_str() {
            "z32" => TypeSize::S32,
            "z64" => TypeSize::S64,
            _ => TypeSize::Inf,
        }
    }
}

impl CEnv {
    fn add_use(&mut self, name: String, typ: Type) {
        if typ != Type::basic("void") {  // ignore "void" uses
            self.uses.entry(name).or_default().push(typ);
        }
    }

    fn decide_type(&self, name: &String) -> Type {
        if let Some(types) = self.uses.get(name) {
            if types.len() == 1 {
                types[0].clone()
            } else {
                assert!(!types.is_empty());
                types.iter().max_by_key(|t|t.size()).unwrap().clone()
            }
        } else {
            Type::basic("void")
        }
    }
}

impl TExpr {
    pub fn concretize(&self, env: &mut CEnv, expected_type: &Type) -> TExpr {
        match self {
            TExpr::Variable { name, typ } => {
                env.add_use(name.clone(), expected_type.clone());
                TExpr::Variable {
                    name: name.clone(),
                    typ: expected_type.clone(),
                }
            }
            TExpr::Semicolon(stmt, expr) => {
                let expr = expr.concretize(env, expected_type);
                let stmt = stmt.concretize(env);
                TExpr::Semicolon(Box::new(stmt), Box::new(expr))
            }
        }
    }
}

impl TStmt {
    pub fn concretize(&self, env: &mut CEnv) -> TStmt {
        match self {
            TStmt::Expr(expr) => {
                let expr = expr.concretize(env, &Type::basic("void"));
                TStmt::Expr(expr)
            }
            TStmt::Assign { name, typ, value } => {
                let value = value.concretize(env, typ);
                TStmt::Assign {
                    name: name.clone(),
                    typ: typ.clone(),
                    value,
                }
            }
            TStmt::Let { name, typ, mutable, type_declared, value } => {
                let typ = if *type_declared {
                    typ.clone()
                } else {
                    env.decide_type(name)
                };
                let value = value.concretize(env, &typ);
                TStmt::Let {
                    name: name.clone(),
                    typ: typ.clone(),
                    mutable: *mutable,
                    type_declared: *type_declared,
                    value,
                }
            }
        }
    }
}