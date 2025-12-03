use std::{
    collections::{HashMap, HashSet},
    error::Error,
    ffi::NulError,
    fmt::Display,
    str::FromStr,
};

use crate::syntax::ast::*;
use z3;

#[allow(dead_code)]
#[derive(Debug)]
pub struct CheckError {
    pub message: String,
}

impl Display for CheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CheckError: {}", self.message)
    }
}
impl Error for CheckError {}

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
    args: Vec<Arg>,
    return_type: Type,
    return_value: String,
    side_effects: HashSet<String>,
    preconditions: Vec<Expr>,
    postconditions: Vec<Expr>,
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BareType {
    Int,
    Bool,
    Str,
    Void,
}

#[derive(Clone)]
struct CheckedVar {
    name: String,
    version: usize,
    max_version: usize,
    mutable: bool,
    hidden: bool,
    var_type: Type,
}

#[derive(Clone)]
struct Env {
    vars: HashMap<String, CheckedVar>,
    assumptions: Vec<z3::ast::Bool>,
    side_effects: HashSet<String>,
    other_funcs: Vec<CheckedFunction>,
}

impl CheckedFunction {
    fn z3_func_decl(&self) -> Result<z3::FuncDecl, CheckError> {
        let args = self
            .args
            .iter()
            .map(|arg| arg.arg_type.to_z3_sort())
            .collect::<Result<Vec<_>, _>>()?;
        let arg_refs = args.iter().collect::<Vec<&z3::Sort>>();
        let ret_sort = self.return_type.to_z3_sort()?;
        Ok(z3::FuncDecl::new(self.name.clone(), &arg_refs, &ret_sort))
    }
}

impl Bounds {
    fn applies_to(self, value: &Z3Value) -> Result<z3::ast::Bool, CheckError> {
        match (self, value) {
            (Bounds::None, _) => Ok(z3::ast::Bool::from_bool(true)),
            (Bounds::U8, Z3Value::Int(int_ast)) => Ok(
                int_ast.ge(z3::ast::Int::from_u64(0)) & int_ast.le(&z3::ast::Int::from_u64(255))
            ),
            (Bounds::I8, Z3Value::Int(int_ast)) => Ok(int_ast.ge(&z3::ast::Int::from_i64(-128))
                & int_ast.le(&z3::ast::Int::from_i64(127))),
            (Bounds::U16, Z3Value::Int(int_ast)) => {
                Ok(int_ast.ge(&z3::ast::Int::from_u64(0))
                    & int_ast.le(&z3::ast::Int::from_u64(65535)))
            }
            (Bounds::I16, Z3Value::Int(int_ast)) => Ok(int_ast.ge(&z3::ast::Int::from_i64(-32768))
                & int_ast.le(&z3::ast::Int::from_i64(32767))),
            (Bounds::U32, Z3Value::Int(int_ast)) => Ok(int_ast.ge(&z3::ast::Int::from_u64(0))
                & int_ast.le(&z3::ast::Int::from_u64(4294967295))),
            (Bounds::I32, Z3Value::Int(int_ast)) => Ok(int_ast
                .ge(&z3::ast::Int::from_i64(-2147483648))
                & int_ast.le(&z3::ast::Int::from_i64(2147483647))),
            (Bounds::U64, Z3Value::Int(int_ast)) => Ok(int_ast.ge(&z3::ast::Int::from_u64(0))
                & int_ast.le(&z3::ast::Int::from_u64(18446744073709551615))),
            (Bounds::I64, Z3Value::Int(int_ast)) => Ok(int_ast
                .ge(&z3::ast::Int::from_i64(-9223372036854775808))
                & int_ast.le(&z3::ast::Int::from_i64(9223372036854775807))),
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
    fn z3_name(&self) -> Result<String, CheckError> {
        if self.hidden {
            return Err(CheckError {
                message: "Variable is out of scope".to_owned(),
            });
        } else if self.mutable || self.version > 0 {
            Ok(format!("{}:{}", self.name, self.version))
        } else {
            Ok(self.name.clone())
        }
    }

    fn z3_const_and_bounds(&self) -> Result<(Z3Value, Bounds), CheckError> {
        self.var_type.to_z3_const(&self.z3_name()?)
    }

    fn z3_const(&self) -> Result<Z3Value, CheckError> {
        Ok(self.z3_const_and_bounds()?.0)
    }

    fn bounds(&self) -> Result<Bounds, CheckError> {
        Ok(self.z3_const_and_bounds()?.1)
    }

    fn mutate(&mut self) {
        self.max_version += 1;
        self.version = self.max_version;
    }

    fn replace(&mut self, mutable: bool, typ: &Type) {
        self.max_version += 1;
        self.version = self.max_version;
        self.mutable = mutable;
        self.var_type = typ.clone();
    }
}

impl BareType {
    fn unbounded(self) -> Type {
        match self {
            BareType::Int => Type {
                name: "int".to_owned(),
            },
            BareType::Bool => Type {
                name: "bool".to_owned(),
            },
            BareType::Str => Type {
                name: "str".to_owned(),
            },
            BareType::Void => Type {
                name: "void".to_owned(),
            },
        }
    }

    fn check_z3_dynamic(self, dyn_ast: &z3::ast::Dynamic) -> Result<Z3Value, CheckError> {
        match self {
            BareType::Int => Ok(Z3Value::Int(dyn_ast.as_int().ok_or_else(|| {
                CheckError {
                    message: "Expected Int type".to_owned(),
                }
            })?)),
            BareType::Bool => Ok(Z3Value::Bool(dyn_ast.as_bool().ok_or_else(|| {
                CheckError {
                    message: "Expected Bool type".to_owned(),
                }
            })?)),
            BareType::Str => Ok(Z3Value::Str(dyn_ast.as_string().ok_or_else(|| {
                CheckError {
                    message: "Expected String type".to_owned(),
                }
            })?)),
            BareType::Void => Err(CheckError {
                message: "Void type cannot be converted from Z3 dynamic".to_owned(),
            }),
        }
    }
}

impl Z3Value {
    fn get_bare_type(&self) -> BareType {
        match self {
            Z3Value::Void => BareType::Void,
            Z3Value::Bool(_) => BareType::Bool,
            Z3Value::Int(_) => BareType::Int,
            Z3Value::Str(_) => BareType::Str,
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

    fn type_check(&self, typ: &Type, env: &mut Env) -> Result<(), CheckError> {
        let self_type = self.get_bare_type();
        let (bt, bounds) = typ.to_bare_type_and_bounds()?;
        if self_type == bt {
            env.assert(&bounds.applies_to(&self)?, "Bounds check failed")?;
            Ok(())
        } else {
            Err(CheckError {
                message: format!("Type mismatch: expected {}, got {:?}", typ, self_type),
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

    fn to_z3_dynamic(&self) -> Result<z3::ast::Dynamic, CheckError> {
        match self {
            Z3Value::Bool(b) => Ok(b.clone().into()),
            Z3Value::Int(i) => Ok(i.clone().into()),
            Z3Value::Str(s) => Ok(s.clone().into()),
            Z3Value::Void => Err(CheckError {
                message: "Void type cannot be converted to Z3 dynamic".to_owned(),
            }),
        }
    }
}

impl Literal {
    fn z3_check(&self) -> Result<Z3Value, CheckError> {
        match self {
            Literal::I64(value) => Ok(Z3Value::Int(z3::ast::Int::from_i64(*value))),
            Literal::U64(value) => Ok(Z3Value::Int(z3::ast::Int::from_u64(*value))),
            Literal::Str(value) => Ok(Z3Value::Str(z3::ast::String::from_str(value)?)),
        }
    }
}

impl Type {
    fn to_bare_type_and_bounds(&self) -> Result<(BareType, Bounds), CheckError> {
        match self.name.as_str() {
            "u8" => Ok((BareType::Int, Bounds::U8)),
            "i8" => Ok((BareType::Int, Bounds::I8)),
            "u16" => Ok((BareType::Int, Bounds::U16)),
            "i16" => Ok((BareType::Int, Bounds::I16)),
            "u32" => Ok((BareType::Int, Bounds::U32)),
            "i32" => Ok((BareType::Int, Bounds::I32)),
            "u64" => Ok((BareType::Int, Bounds::U64)),
            "i64" => Ok((BareType::Int, Bounds::I64)),
            "int" => Ok((BareType::Int, Bounds::None)),
            "bool" => Ok((BareType::Bool, Bounds::None)),
            "str" => Ok((BareType::Str, Bounds::None)),
            "void" => Ok((BareType::Void, Bounds::None)),
            _ => Err(CheckError {
                message: format!("Unsupported type: {}", self),
            }),
        }
    }

    fn bare_type(&self) -> Result<BareType, CheckError> {
        Ok(self.to_bare_type_and_bounds()?.0)
    }

    fn bounds(&self) -> Result<Bounds, CheckError> {
        Ok(self.to_bare_type_and_bounds()?.1)
    }

    fn to_z3_sort(&self) -> Result<z3::Sort, CheckError> {
        match self.bare_type()? {
            BareType::Int => Ok(z3::Sort::int()),
            BareType::Bool => Ok(z3::Sort::bool()),
            BareType::Str => Ok(z3::Sort::string()),
            _ => Err(CheckError {
                message: format!("Unsupported type for Z3 sort: {}", self),
            }),
        }
    }

    fn to_z3_const(&self, name: &str) -> Result<(Z3Value, Bounds), CheckError> {
        let (bt, bounds) = self.to_bare_type_and_bounds()?;
        match bt {
            BareType::Int => Ok((Z3Value::Int(z3::ast::Int::new_const(name)), bounds)),
            BareType::Bool => Ok((Z3Value::Bool(z3::ast::Bool::new_const(name)), bounds)),
            BareType::Str => Ok((Z3Value::Str(z3::ast::String::new_const(name)), bounds)),
            _ => Err(CheckError {
                message: format!("Unsupported bare type: {:?}", bt),
            }),
        }
    }
}

impl AssignOp {
    fn relate(
        &self,
        old_left: Z3Value,
        new_left: Z3Value,
        right: Z3Value,
    ) -> Result<z3::ast::Bool, CheckError> {
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
    fn new(other_funcs: &[CheckedFunction]) -> Self {
        Env {
            vars: HashMap::new(),
            assumptions: Vec::new(),
            side_effects: HashSet::new(),
            other_funcs: other_funcs.to_owned(),
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

    fn insert_var(
        &mut self,
        name: &str,
        mutable: bool,
        ty: &Type,
    ) -> Result<(Z3Value, Bounds), CheckError> {
        self.vars
            .entry(name.to_owned())
            .and_modify(|info| info.replace(mutable, ty))
            .or_insert_with(|| CheckedVar {
                name: name.to_owned(),
                version: 0,
                max_version: 0,
                hidden: false,
                mutable,
                var_type: ty.clone(),
            })
            .z3_const_and_bounds()
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
                message: format!("{}: {}", message, cond),
            })
        } else {
            self.assumptions.push(cond.clone());
            Ok(())
        }
    }

    fn prints(&mut self) {
        self.side_effects.insert("print".to_owned());
    }

    #[allow(dead_code)]
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
        self.assert(&bounds.applies_to(&new_var)?, "Bounds check failed")?;
        Ok(())
    }

    fn fold_in_scope(&mut self, other: &Env) {
        for (name, other_var) in &other.vars {
            self.vars.entry(name.clone())
                .and_modify(|var| {
                    assert!(other_var.version >= var.version);
                    var.version = other_var.version;
                })
                .or_insert_with(|| {
                    let mut other_clone = other_var.clone();
                    other_clone.hidden = true;
                    other_clone
                });
        }
        for effect in &other.side_effects {
            self.side_effects.insert(effect.clone());
        }

        for assumption in &other.assumptions {
            if !self.assumptions.contains(assumption) {
                self.assumptions.push(assumption.clone());
            }
        }
    }

    fn enter_call_scope(
        &self,
        func: &CheckedFunction,
        args: &[Z3Value],
    ) -> Result<Env, CheckError> {
        let mut new_env = self.clone();
        if func.args.len() != args.len() {
            return Err(CheckError {
                message: format!(
                    "Function {} expected {} arguments, got {}",
                    func.name,
                    func.args.len(),
                    args.len()
                ),
            });
        }
        for (arg, value) in func.args.iter().zip(args.iter()) {
            let (new_var, bounds) = new_env.insert_var(&arg.name, false, &arg.arg_type)?;
            new_env.assume(new_var.eq(value)?);
            new_env.assert(&bounds.applies_to(value)?, "Bounds check failed")?;
        }
        Ok(new_env)
    }

    fn check_preconditions(&mut self, func: &CheckedFunction) -> Result<(), CheckError> {
        for precondition in &func.preconditions {
            let cond_z3_value = precondition.z3_check(self)?;
            self.assert(cond_z3_value.bool()?, "Precondition failed")?;
        }
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
                let var_type = z3_value.get_bare_type().unbounded(); // don't record bounds for non-mutable variables
                let (z3_var, bounds) = env.insert_var(name, false, &var_type)?;
                env.assume(z3_var.eq(&z3_value)?);
                env.assert(&bounds.applies_to(&z3_value)?, "Bounds check failed")?;
                Ok(())
            }
            Stmt::LetMut { name, typ, value } => {
                let z3_value = value.z3_check(env)?;
                let (z3_var, bounds) = env.insert_var(name, true, typ)?;
                env.assume(z3_var.eq(&z3_value)?);
                env.assert(&bounds.applies_to(&z3_value)?, "Bounds check failed")?;
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
        ("<", 2) => {
            let left_int = args[0].int()?;
            let right_int = args[1].int()?;
            Ok(Z3Value::Bool(left_int.lt(right_int)))
        }
        ("<=", 2) => {
            let left_int = args[0].int()?;
            let right_int = args[1].int()?;
            Ok(Z3Value::Bool(left_int.le(right_int)))
        }
        (">", 2) => {
            let left_int = args[0].int()?;
            let right_int = args[1].int()?;
            Ok(Z3Value::Bool(left_int.gt(right_int)))
        }
        (">=", 2) => {
            let left_int = args[0].int()?;
            let right_int = args[1].int()?;
            Ok(Z3Value::Bool(left_int.ge(right_int)))
        }
        ("+", 2) => Ok(Z3Value::Int(args[0].int()? + args[1].int()?)),
        ("-", 2) => Ok(Z3Value::Int(args[0].int()? - args[1].int()?)),
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
        _ => {
            if let Some(user_func) = env.other_funcs.iter().find(|f| f.name == name) {
                let user_func = user_func.clone(); // clone it because we're doing other things to env and they conflict
                let func_decl = user_func.z3_func_decl()?;
                let mut call_env = env.enter_call_scope(&user_func, args)?;
                call_env.check_preconditions(&user_func)?;

                let z3_args = args
                    .iter()
                    .map(|arg| arg.to_z3_dynamic())
                    .collect::<Result<Vec<_>, _>>()?;
                let z3_argrefs = z3_args
                    .iter()
                    .map(|a| a as &dyn z3::ast::Ast)
                    .collect::<Vec<&dyn z3::ast::Ast>>();

                let (bt_ret, bounds) = user_func.return_type.to_bare_type_and_bounds()?;
                let retvar = call_env.insert_var(&user_func.return_value, false, &user_func.return_type)?.0;
                
                // we can assume the bounds on the return value
                call_env.assume(bounds.applies_to(&retvar)?);
                // we can also assume the postconditions
                for postcondition in &user_func.postconditions {
                    let cond_z3_value = postcondition.z3_check(&mut call_env)?;
                    call_env.assume(cond_z3_value.bool()?.clone());
                }
                // don't forget the side effects
                for effect in &user_func.side_effects {
                    call_env.side_effects.insert(effect.clone());
                }

                // fold back into main env
                env.fold_in_scope(&call_env);

                // unify return value with function call
                let ast = func_decl.apply(&z3_argrefs);
                let val = bt_ret.check_z3_dynamic(&ast)?;
                env.assume(retvar.eq(&val)?);

                Ok(val)
            } else {
                Err(CheckError {
                    message: format!("Undefined function: {}", name),
                })
            }
        }
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

fn z3_check_funcdef(
    func: &FuncDef,
    other_funcs: &[CheckedFunction],
) -> Result<CheckedFunction, CheckError> {
    let mut env = Env::new(other_funcs);
    for arg in &func.args {
        env.insert_var(&arg.name, false, &arg.arg_type)?;
        env.assume(
            arg.arg_type
                .bounds()?
                .applies_to(&env.get_var(&arg.name)?)?,
        );
    }
    for precondition in &func.preconditions {
        let cond_z3_value = precondition.z3_check(&mut env)?;
        env.assume(cond_z3_value.bool()?.clone());
    }
    let body_z3_value = func.body.z3_check(&mut env)?;
    body_z3_value.type_check(&func.return_type, &mut env)?;

    // now check all the postconditions
    if func.postconditions.len() > 0 {
        if let Some(ret) = &func.return_name {
            let ret_var = env.insert_var(ret, false, &func.return_type)?.0;
            env.assume(ret_var.eq(&body_z3_value)?);
            for postcondition in &func.postconditions {
                let cond_z3_value = postcondition.z3_check(&mut env)?;
                env.assert(cond_z3_value.bool()?, "Postcondition failed")?;
            }
        } else {
            return Err(CheckError {
                message: "Postconditions specified but no return variable name provided".to_owned(),
            });
        }
    }

    println!("Checked function: {}", func.name);
    env.print_side_effects();
    Ok(CheckedFunction {
        name: func.name.clone(),
        args: func.args.clone(),
        return_type: func.return_type.clone(),
        return_value: func.return_name.clone().unwrap_or_else(|| "__ret__".to_owned()),
        side_effects: env.side_effects,
        preconditions: func.preconditions.clone(),
        postconditions: func.postconditions.clone(),
    })
}

pub fn z3_check(source_file: &SourceFile) -> Result<(), CheckError> {
    let mut other_funcs = vec![];
    for func in &source_file.functions {
        let checked_func = z3_check_funcdef(func, &other_funcs)?;
        other_funcs.push(checked_func);
    }
    Ok(())
}