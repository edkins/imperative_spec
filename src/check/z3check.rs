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
struct CheckedFunction {
    name: String,
    args: Vec<(String, Type)>,
    return_type: Type,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Bounds {
    None,
    U8,
    I8,
    U16,
    I16,
    U32,
    I32,
    U64,
    I64,
}

#[derive(Clone)]
struct CheckedVar {
    name: String,
    version: usize,
    mutable: bool,
    var_type: Type,
}

#[derive(Clone)]
struct Env {
    vars: HashMap<String, CheckedVar>,
    assumptions: Vec<z3::ast::Bool>,
    side_effects: HashSet<String>,
}

impl Bounds {
    fn applies_to(self, value: Z3Value) -> Result<z3::ast::Bool, CheckError> {
        match (self, value) {
            (Bounds::None, _) => Ok(z3::ast::Bool::from_bool(true)),
            (Bounds::U8, Z3Value::Int(int_ast)) =>
                Ok(int_ast.ge(z3::ast::Int::from_u64(0)) & int_ast.le(&z3::ast::Int::from_u64(255))),
            (Bounds::I8, Z3Value::Int(int_ast)) =>
                Ok(int_ast.ge(&z3::ast::Int::from_i64(-128)) & int_ast.le(&z3::ast::Int::from_i64(127))),
            (Bounds::U16, Z3Value::Int(int_ast)) =>
                Ok(int_ast.ge(&z3::ast::Int::from_u64(0)) & int_ast.le(&z3::ast::Int::from_u64(65535))),
            (Bounds::I16, Z3Value::Int(int_ast)) =>
                Ok(int_ast.ge(&z3::ast::Int::from_i64(-32768)) & int_ast.le(&z3::ast::Int::from_i64(32767))),
            (Bounds::U32, Z3Value::Int(int_ast)) =>
                Ok(int_ast.ge(&z3::ast::Int::from_u64(0)) & int_ast.le(&z3::ast::Int::from_u64(4294967295))),
            (Bounds::I32, Z3Value::Int(int_ast)) =>
                Ok(int_ast.ge(&z3::ast::Int::from_i64(-2147483648)) & int_ast.le(&z3::ast::Int::from_i64(2147483647))),
            (Bounds::U64, Z3Value::Int(int_ast)) =>
                Ok(int_ast.ge(&z3::ast::Int::from_u64(0)) & int_ast.le(&z3::ast::Int::from_u64(18446744073709551615))),
            (Bounds::I64, Z3Value::Int(int_ast)) =>
                Ok(int_ast.ge(&z3::ast::Int::from_i64(-9223372036854775808)) & int_ast.le(&z3::ast::Int::from_i64(9223372036854775807))),
            _ => Err(CheckError {
                message: "Bounds can't be applied to this type".to_owned(),
            }),
        }
    }
}

impl From<NulError> for CheckError {
    fn from(err: NulError) -> Self {
        CheckError {
            message: format!("NulError: {}", err),
        }
    }
}

impl CheckedVar {
    fn z3_name(&self) -> String {
        if self.mutable || self.version > 0 {
            format!("{}:{}", self.name, self.version)
        } else {
            self.name.clone()
        }
    }

    fn z3_const_and_bounds(&self) -> Result<(Z3Value, Bounds), CheckError> {
        self.var_type.to_z3_const(&self.z3_name())
    }

    fn z3_const(&self) -> Result<Z3Value, CheckError> {
        Ok(self.z3_const_and_bounds()?.0)
    }

    fn bounds(&self) -> Result<Bounds, CheckError> {
        Ok(self.z3_const_and_bounds()?.1)
    }

    fn mutate(&mut self) {
        self.version += 1;
    }

    fn replace(&mut self, mutable: bool, typ: &Type) {
        self.version += 1;
        self.mutable = mutable;
        self.var_type = typ.clone();
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

    fn ne(&self, other: &Z3Value) -> Result<z3::ast::Bool, CheckError> {
        self.eq(other).map(|eq_ast| eq_ast.not())
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
    fn to_z3_const(&self, name: &str) -> Result<(Z3Value, Bounds), CheckError> {
        match self.name.as_str() {
            "u8" => Ok((Z3Value::Int(z3::ast::Int::new_const(name)), Bounds::U8)),
            "i8" => Ok((Z3Value::Int(z3::ast::Int::new_const(name)), Bounds::I8)),
            "u16" => Ok((Z3Value::Int(z3::ast::Int::new_const(name)), Bounds::U16)),
            "i16" => Ok((Z3Value::Int(z3::ast::Int::new_const(name)), Bounds::I16)),
            "u32" => Ok((Z3Value::Int(z3::ast::Int::new_const(name)), Bounds::U32)),
            "i32" => Ok((Z3Value::Int(z3::ast::Int::new_const(name)), Bounds::I32)),
            "u64" => Ok((Z3Value::Int(z3::ast::Int::new_const(name)), Bounds::U64)),
            "i64" => Ok((Z3Value::Int(z3::ast::Int::new_const(name)), Bounds::I64)),
            "bool" => Ok((Z3Value::Bool(z3::ast::Bool::new_const(name)), Bounds::None)),
            "str" => Ok((Z3Value::Str(z3::ast::String::new_const(name)), Bounds::None)),
            _ => Err(CheckError {
                message: format!("Unsupported type: {}", self.name),
            }),
        }
    }
}

impl AssignOp {
    fn relate(&self, old_left: Z3Value, new_left: Z3Value, right: Z3Value) -> Result<z3::ast::Bool, CheckError> {
        match self {
            AssignOp::Assign => new_left.eq(&right),
            AssignOp::PlusAssign => {
                let left_int = old_left.int()?;
                let right_int = right.int()?;
                Ok(new_left.int()?.eq(left_int + right_int))
            }
            AssignOp::MinusAssign => {
                let left_int = old_left.int()?;
                let right_int = right.int()?;
                Ok(new_left.int()?.eq(left_int - right_int))
            }
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
        if let Some(info) = self.vars.get(name) {
            info.z3_const()
        } else {
            Err(CheckError {
                message: format!("Undefined variable: {}", name),
            })
        }
    }

    fn insert_var(&mut self, name: &str, mutable: bool, ty: &Type) -> Result<(Z3Value, Bounds), CheckError> {
        self.vars.entry(name.to_owned())
            .and_modify(|info| info.replace(mutable, ty))
            .or_insert_with(|| CheckedVar {
                name: name.to_owned(),
                version: 0,
                mutable,
                var_type: ty.clone(),
            }).z3_const_and_bounds()
    }

    fn assume(&mut self, cond: z3::ast::Bool) {
        self.assumptions.push(cond);
    }

    fn assert(&mut self, cond: &z3::ast::Bool, message: &str) -> Result<(), CheckError> {
        let solver = z3::Solver::new();
        for assumption in &self.assumptions {
            solver.assert(assumption);
        }
        solver.assert(cond.not());
        if solver.check() != z3::SatResult::Unsat {
            Err(CheckError {
                message: message.to_owned(),
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

    fn assign(&mut self, var: &str, op: AssignOp, value: Z3Value) -> Result<(), CheckError> {
        let info = self.vars.get_mut(var).ok_or(CheckError {
            message: format!("Undefined variable: {}", var),
        })?;
        if !info.mutable {
            return Err(CheckError {
                message: format!("Cannot assign to immutable variable: {}", var),
            });
        }
        let old_var = info.z3_const()?;
        info.mutate();
        let new_var = info.z3_const()?;
        let bounds = info.bounds()?;
        self.assume(op.relate(old_var, new_var.clone(), value)?);
        self.assert(&bounds.applies_to(new_var)?, "Bounds check failed")?;
        Ok(())
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
                let z3_value = value.z3_check(env)?;
                let var_type = z3_value.get_type();
                let (z3_var, bounds) = env.insert_var(name, false, &var_type)?;
                env.assume(z3_var.eq(&z3_value)?);
                env.assert(&bounds.applies_to(z3_value)?, "Bounds check failed")?;
                Ok(())
            }
            Stmt::LetMut { name, typ, value } => {
                let z3_value = value.z3_check(env)?;
                let (z3_var, bounds) = env.insert_var(name, true, typ)?;
                env.assume(z3_var.eq(&z3_value)?);
                env.assert(&bounds.applies_to(z3_value)?, "Bounds check failed")?;
                Ok(())
            }
            Stmt::Assign { name, op, value } => {
                let z3_value = value.z3_check(env)?;
                env.assign(name, *op, z3_value)
            }
        }
    }
}

fn z3_function_call(name: &str, args: &[Z3Value], env: &mut Env) -> Result<Z3Value, CheckError> {
    match (name, args.len()) {
        ("==", 2) => {
            let eq_ast = args[0].eq(&args[1])?;
            Ok(Z3Value::Bool(eq_ast))
        }
        ("!=", 2) => {
            let eq_ast = args[0].ne(&args[1])?;
            Ok(Z3Value::Bool(eq_ast))
        }
        ("+", 2) => {
            Ok(Z3Value::Int(args[0].int()? + args[1].int()?))
        }
        ("-", 2) => {
            Ok(Z3Value::Int(args[0].int()? - args[1].int()?))
        }
        ("assert", 1) => {
            let bool_arg = args[0].bool()?;
            env.assert(bool_arg, "Assertion failed")?;
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
        env.insert_var(&arg.name, false, &arg.arg_type)?;
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