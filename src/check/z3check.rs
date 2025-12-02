use std::{collections::{HashMap, HashSet}, ffi::NulError, str::FromStr};

use z3;
use crate::syntax::ast::*;

#[allow(dead_code)]
#[derive(Debug)]
pub struct CheckError {
    pub message: String,
}

#[allow(dead_code)]
#[derive(Clone)]
enum Z3Value {
    Void,
    Bool(z3::ast::Bool),
    Int(z3::ast::Int),
    Str(z3::ast::String),
}

#[derive(Clone)]
struct Env {
    vars: HashMap<String, Type>,
    assumptions: Vec<z3::ast::Bool>,
    side_effects: HashSet<String>,
}

impl From<NulError> for CheckError {
    fn from(err: NulError) -> Self {
        CheckError {
            message: format!("NulError: {}", err),
        }
    }
}

impl Z3Value {
    fn get_type(&self) -> Type {
        match self {
            Z3Value::Void => Type { name: "void".to_owned() },
            Z3Value::Bool(_) => Type { name: "bool".to_owned() },
            Z3Value::Int(_) => Type { name: "int".to_owned() },
            Z3Value::Str(_) => Type { name: "str".to_owned() },
        }
    }

    fn eq(&self, other: &Z3Value) -> Result<z3::ast::Bool, CheckError> {
        match (self, other) {
            (Z3Value::Bool(a), Z3Value::Bool(b)) => Ok(a.eq(b)),
            (Z3Value::Int(a), Z3Value::Int(b)) => Ok(a.eq(b)),
            (Z3Value::Str(a), Z3Value::Str(b)) => Ok(a.eq(b)),
            _ => Err(CheckError {
                message: "Type mismatch in equality".to_owned(),
            }),
        }
    }

    fn type_check(&self, typ: &Type) -> Result<(), CheckError> {
        let self_type = self.get_type();
        if self_type.name == typ.name {
            Ok(())
        } else {
            Err(CheckError {
                message: format!(
                    "Type mismatch: expected {}, got {}",
                    typ.name, self_type.name
                ),
            })
        }
    }

    fn bool(&self) -> Result<&z3::ast::Bool, CheckError> {
        match self {
            Z3Value::Bool(b) => Ok(b),
            _ => Err(CheckError {
                message: "Expected Bool type".to_owned(),
            }),
        }
    }

    fn int(&self) -> Result<&z3::ast::Int, CheckError> {
        match self {
            Z3Value::Int(i) => Ok(i),
            _ => Err(CheckError {
                message: "Expected Int type".to_owned(),
            }),
        }
    }

    fn string(&self) -> Result<&z3::ast::String, CheckError> {
        match self {
            Z3Value::Str(s) => Ok(s),
            _ => Err(CheckError {
                message: "Expected String type".to_owned(),
            }),
        }
    }
}

impl Literal {
    fn z3_check(&self) -> Result<Z3Value, CheckError> {
        match self {
            Literal::I64(value) => Ok(Z3Value::Int(z3::ast::Int::from_i64(*value))),
            Literal::U64(value) => Ok(Z3Value::Int(z3::ast::Int::from_u64(*value))),
            Literal::Str(value) => Ok(Z3Value::Str(z3::ast::String::from_str(value)?),),
        }
    }
}

impl Type {
    fn to_z3_const(&self, name: &str) -> Result<Z3Value, CheckError> {
        match self.name.as_str() {
            "int" => Ok(Z3Value::Int(z3::ast::Int::new_const(name))),
            "str" => Ok(Z3Value::Str(z3::ast::String::new_const(name))),
            _ => Err(CheckError {
                message: format!("Unsupported type: {}", self.name),
            }),
        }
    }
}

impl Env {
    fn new() -> Self {
        Env {
            vars: HashMap::new(),
            assumptions: Vec::new(),
            side_effects: HashSet::new(),
        }
    }

    fn get_var(&self, name: &str) -> Result<Z3Value, CheckError> {
        if let Some(ty) = self.vars.get(name) {
            ty.to_z3_const(name)
        } else {
            Err(CheckError {
                message: format!("Undefined variable: {}", name),
            })
        }
    }

    fn insert_var(&mut self, name: &str, ty: &Type) -> Result<Z3Value, CheckError> {
        if self.vars.contains_key(name) {
            return Err(CheckError {
                message: format!("Variable {} already defined", name),
            });
        }
        self.vars.insert(name.to_owned(), ty.clone());
        Ok(ty.to_z3_const(name)?)
    }

    fn assume(&mut self, cond: z3::ast::Bool) {
        self.assumptions.push(cond);
    }

    fn assert(&mut self, cond: &z3::ast::Bool) -> Result<(), CheckError> {
        let solver = z3::Solver::new();
        for assumption in &self.assumptions {
            solver.assert(assumption);
        }
        solver.assert(cond);
        if solver.check() == z3::SatResult::Unsat {
            Err(CheckError {
                message: "Assertion failed".to_owned(),
            })
        } else {
            self.assumptions.push(cond.clone());
            Ok(())
        }
    }

    fn prints(&mut self) {
        self.side_effects.insert("print".to_owned());
    }

    fn mallocs(&mut self) {
        self.side_effects.insert("malloc".to_owned());
    }

    fn print_side_effects(&self) {
        let mut effects: Vec<_> = self.side_effects.iter().collect();
        effects.sort();
        for effect in &effects {
            println!("Side effect: {}", effect);
        }
    }
}

impl Stmt {
    fn z3_check(&self, env: &mut Env) -> Result<(), CheckError> {
        match self {
            Stmt::Expr(expr) => {
                expr.z3_check(env)?;
                Ok(())
            }
            Stmt::Let { name, value } => {
                if env.vars.contains_key(name) {
                    return Err(CheckError {
                        message: format!("Variable {} already defined", name),
                    });
                }
                let z3_value = value.z3_check(env)?;
                let var_type = z3_value.get_type();
                let z3_var = env.insert_var(name, &var_type)?;
                env.assume(z3_var.eq(&z3_value)?);
                Ok(())
            }
        }
    }
}

fn z3_function_call(name: &str, args: &[Z3Value], env: &mut Env) -> Result<Z3Value, CheckError> {
    match (name, args.len()) {
        ("eq", 2) => {
            let eq_ast = args[0].eq(&args[1])?;
            Ok(Z3Value::Bool(eq_ast))
        }
        ("add", 2) => {
            Ok(Z3Value::Int(args[0].int()? + args[1].int()?))
        }
        ("assert", 1) => {
            let bool_arg = args[0].bool()?;
            env.assert(bool_arg)?;
            Ok(Z3Value::Void)
        }
        ("println", 1) => {
            args[0].string()?;
            env.prints();
            Ok(Z3Value::Void)
        }
        _ => Err(CheckError {
            message: format!("User defined functions not implemented yet: {}", name),
        }),
    }
}

impl Expr {
    fn z3_check(&self, env: &mut Env) -> Result<Z3Value, CheckError> {
        match self {
            Expr::Literal(literal) => literal.z3_check(),
            Expr::Variable(name) => env.get_var(name),
            Expr::FunctionCall { name, args } => {
                let z3args = args
                    .iter()
                    .map(|arg| arg.z3_check(env))
                    .collect::<Result<Vec<_>, _>>()?;
                z3_function_call(name, &z3args, env)
            }
            Expr::Semicolon(stmt, expr) => {
                let mut new_env = env.clone();
                stmt.z3_check(&mut new_env)?;
                expr.z3_check(&mut new_env)
            }
        }
    }
}

fn z3_check_funcdef(func: &FuncDef) -> Result<(), CheckError> {
    let mut env = Env::new();
    for arg in &func.args {
        env.insert_var(&arg.name, &arg.arg_type)?;
    }
    let body_z3_value = func.body.z3_check(&mut env)?;
    body_z3_value.type_check(&func.return_type)?;
    println!("Checked function: {}", func.name);
    env.print_side_effects();
    Ok(())
}

pub fn z3_check(source_file: &SourceFile) -> Result<(), CheckError> {
    for func in &source_file.functions {
        z3_check_funcdef(func)?;
    }
    Ok(())
}