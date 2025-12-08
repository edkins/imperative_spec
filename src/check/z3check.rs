use std::{
    collections::{HashMap, HashSet},
    error::Error,
    ffi::NulError,
    fmt::Display,
    str::FromStr,
};

use crate::{
    check::{
        builtins,
        optimization_chooser::OptimizationError,
        ztype_ast::{TExpr, TFuncDef, TSourceFile, TStmt},
        ztype_inference::TypeError,
    },
    syntax::ast::*,
};
use z3::{
    self, SortDiffers,
    ast::{Ast, Dynamic},
};

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

impl From<TypeError> for CheckError {
    fn from(err: TypeError) -> Self {
        CheckError {
            message: format!("TypeError: {}", err),
        }
    }
}

impl From<SortDiffers> for CheckError {
    fn from(err: SortDiffers) -> Self {
        CheckError {
            message: format!("SortDiffers: {}", err),
        }
    }
}

impl From<OptimizationError> for CheckError {
    fn from(err: OptimizationError) -> Self {
        CheckError {
            message: format!("OptimizationError: {}", err),
        }
    }
}

#[derive(Clone)]
struct CheckedVar {
    name: String,
    z3: Dynamic,
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
    builtins: HashMap<String, TFuncDef>,
    other_funcs: Vec<TFuncDef>,
    verbosity: u8,
    type_param_list: Vec<String>,
    sees: Vec<String>,
}

impl TFuncDef {
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

    fn postconditions_and_type_postconditions(&self) -> Result<Vec<TExpr>, CheckError> {
        let mut postconditions = self.postconditions.clone();
        let return_var = TExpr::Variable {
            name: self.return_name.clone(),
            typ: self.return_type.clone(),
        };
        let type_postconditions = self
            .return_type
            .type_assertions(return_var, &[])?;
        postconditions.extend(type_postconditions);
        Ok(postconditions)
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
    // fn z3_name(&self) -> Result<String, CheckError> {
    //     if self.hidden {
    //         Err(CheckError {
    //             message: format!("Variable {} is out of scope", self.name),
    //         })
    //     } else if self.mutable || self.version > 0 {
    //         Ok(format!("{}:{}", self.name, self.version))
    //     } else {
    //         Ok(self.name.clone())
    //     }
    // }

    // fn z3_const(&self) -> Result<Dynamic, CheckError> {
    //     self.var_type.to_z3_const(&self.z3_name()?)
    // }

    fn new(name: &str, mutable: bool, ty: &Type) -> Self {
        let z3name = if mutable {
            format!("{}:0", name)
        } else {
            name.to_owned()
        };
        CheckedVar {
            z3: ty.to_z3_const(&z3name).unwrap(),
            name: name.to_owned(),
            version: 0,
            max_version: 0,
            hidden: false,
            mutable,
            var_type: ty.clone(),
        }
    }

    fn new_with_value(name: &str, ty: &Type, value: &Dynamic) -> Self {
        CheckedVar {
            z3: value.clone(),
            name: name.to_owned(),
            version: 0,
            max_version: 0,
            hidden: false,
            mutable: false,
            var_type: ty.clone(),
        }
    }

    fn mutate(&mut self) {
        assert!(!self.hidden);
        self.max_version += 1;
        self.version = self.max_version;
        self.z3 = self.var_type.to_z3_const(&format!("{}:{}", self.name, self.version)).unwrap();
    }

    fn replace(&mut self, mutable: bool, typ: &Type) {
        self.hidden = false;
        self.max_version += 1;
        self.version = self.max_version;
        self.mutable = mutable;
        self.var_type = typ.clone();
        self.z3 = self.var_type.to_z3_const(&format!("{}:{}", self.name, self.version)).unwrap();
    }
}

impl Literal {
    fn z3_check(&self) -> Result<Dynamic, CheckError> {
        match self {
            Literal::Unit => Ok(void_value()),
            Literal::I64(value) => Ok(z3::ast::Int::from_i64(*value).into()),
            Literal::U64(value) => Ok(z3::ast::Int::from_u64(*value).into()),
            Literal::Str(value) => Ok(z3::ast::String::from_str(value)?.into()),
            Literal::Bool(value) => Ok(z3::ast::Bool::from_bool(*value).into()),
        }
    }
}

impl Type {
    fn to_z3_sort(&self) -> Result<z3::Sort, CheckError> {
        if self.is_int() {
            Ok(z3::Sort::int())
        } else if self.is_bool() {
            Ok(z3::Sort::bool())
        } else if self.is_str() {
            Ok(z3::Sort::string())
        } else if self.is_void() {
            Ok(void_value().get_sort())
        } else if self.is_named_seq() {
            let elem_type = self.one_type_arg()?;
            let elem_sort = elem_type.to_z3_sort()?;
            Ok(z3::Sort::seq(&elem_sort))
        } else {
            Err(CheckError {
                message: format!("Unsupported type for to_z3_sort: {}", self),
            })
        }
    }

    fn to_z3_const(&self, name: &str) -> Result<Dynamic, CheckError> {
        if self.is_int() {
            Ok(z3::ast::Int::new_const(name).into())
        } else if self.is_bool() {
            Ok(z3::ast::Bool::new_const(name).into())
        } else if self.is_str() {
            Ok(z3::ast::String::new_const(name).into())
        } else if self.is_void() {
            Ok(void_value())
        } else if let Some(elem_type) = self.get_named_seq() {
            let elem_sort = elem_type.to_z3_sort()?;
            Ok(z3::ast::Seq::new_const(name, &elem_sort).into())
        } else {
            Err(CheckError {
                message: format!("Unsupported type for to_z3_const: {}", self),
            })
        }
    }
}

impl Env {
    fn new(other_funcs: &[TFuncDef], sees: &[String], verbosity: u8) -> Self {
        Env {
            vars: HashMap::new(),
            assumptions: Vec::new(),
            side_effects: HashSet::new(),
            builtins: builtins::builtins(),
            other_funcs: other_funcs.to_owned(),
            verbosity,
            type_param_list: Vec::new(),
            sees: sees.to_owned(),
        }
    }

    fn get_var(&self, name: &str) -> Result<Dynamic, CheckError> {
        if let Some(info) = self.vars.get(name) {
            Ok(info.z3.clone())
        } else {
            Err(CheckError {
                message: format!("Undefined variable: {}", name),
            })
        }
    }

    fn insert_var(&mut self, name: &str, mutable: bool, ty: &Type) -> Result<Dynamic, CheckError> {
        Ok(self.vars
            .entry(name.to_owned())
            .and_modify(|info| info.replace(mutable, ty))
            .or_insert_with(|| CheckedVar::new(name, mutable, ty))
            .z3.clone())
    }

    fn insert_var_with_value(&mut self, name: &str, ty: &Type, value: &Dynamic) -> Result<(), CheckError> {
        assert!(!self.vars.contains_key(name), "Variable {} already defined", name);
        self.vars.insert(name.to_owned(), CheckedVar::new_with_value(name, ty, value));
        Ok(())
    }

    fn assume_exprs(&mut self, exprs: &[TExpr]) -> Result<(), CheckError> {
        for expr in exprs {
            self.assume_expr(expr)?;
        }
        Ok(())
    }

    fn assume_expr(&mut self, expr: &TExpr) -> Result<(), CheckError> {
        let cond_z3_value = expr.z3_check(self)?.0;
        self.assume(boolean(&cond_z3_value)?);
        Ok(())
    }

    fn assume(&mut self, cond: z3::ast::Bool) {
        if self.verbosity >= 2 {
            println!("Assuming: {}", cond);
        }
        self.assumptions.push(cond);
        if self.verbosity >= 2 {
            self.check_consistency();
        }
    }

    /// Returns true if the condition is known to be true given the current assumptions
    /// Like assert but doesn't return an "error" if it fails.
    /// If true, records the condition as an assumption so it doesn't need to be recomputed in future.
    fn probe(&mut self, cond: &z3::ast::Bool) -> bool {
        let solver = z3::Solver::new();
        for assumption in &self.assumptions {
            solver.assert(assumption);
        }
        solver.assert(cond.not());
        if solver.check() == z3::SatResult::Unsat {
            self.assumptions.push(cond.clone());
            if self.verbosity >= 2 {
                println!("Probing: {} - true", cond);
            }
            true
        } else {
            if self.verbosity >= 2 {
                println!("Probing: {} - false", cond);
            }
            false
        }
    }

    fn check_consistency(&self) {
        let solver = z3::Solver::new();
        for assumption in &self.assumptions {
            solver.assert(assumption);
        }
        println!("  status: {:?}", solver.check());
    }

    fn assert_exprs(&mut self, exprs: &[TExpr], message: &str) -> Result<(), CheckError> {
        for expr in exprs {
            self.assert_expr(expr, message)?;
        }
        Ok(())
    }

    fn assert_expr(&mut self, expr: &TExpr, message: &str) -> Result<(), CheckError> {
        let cond_z3_value = expr.z3_check(self)?.0;
        self.assert(&boolean(&cond_z3_value)?, message)?;
        Ok(())
    }

    fn assert(&mut self, cond: &z3::ast::Bool, message: &str) -> Result<(), CheckError> {
        if self.verbosity >= 2 {
            println!("Asserting: {}", cond);
        }
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
            print!(" {{{}}}", effect);
        }
        println!();
    }

    fn assign(&mut self, var: &str, value: Dynamic) -> Result<(), CheckError> {
        let info = self.vars.get_mut(var).ok_or(CheckError {
            message: format!("Undefined variable: {}", var),
        })?;
        if !info.mutable {
            return Err(CheckError {
                message: format!("Cannot assign to immutable variable: {}", var),
            });
        }
        info.mutate();
        let new_var = info.z3.clone();
        let conds = info.var_type.type_assertions(
            TExpr::Variable {
                name: var.to_owned(),
                typ: info.var_type.clone(),
            },
            &self.type_param_list,
        )?;
        self.assume(new_var.safe_eq(&value)?);
        self.assert_exprs(&conds, "Type assertion failed in assignment")
    }

    fn fold_in_assumptions(&mut self, other: &Env) {
        for assumption in &other.assumptions {
            if !self.assumptions.contains(assumption) {
                self.assumptions.push(assumption.clone());
            }
        }

        if self.verbosity >= 2 {
            println!("Folding in assumptions:");
            self.check_consistency();
        }
    }

    fn fold_in_scope(&mut self, other: &Env) {
        for (name, other_var) in &other.vars {
            self.vars
                .entry(name.clone())
                .and_modify(|var| {
                    assert!(other_var.version >= var.version);
                    assert!(other_var.max_version >= var.max_version);
                    var.max_version = other_var.max_version;
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

        if self.verbosity >= 2 {
            println!("Folding in scope:");
            self.check_consistency();
            for (name, var) in &self.vars {
                println!(
                    "  var {} (version {}, max_version {}, hidden {})",
                    name, var.version, var.max_version, var.hidden
                );
            }
        }
    }

    fn enter_call_scope(&self, func: &TFuncDef, args: &[Dynamic]) -> Result<Env, CheckError> {
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

        // hide all outside variables
        for var in new_env.vars.values_mut() {
            var.hidden = true;
        }

        for (arg, value) in func.args.iter().zip(args.iter()) {
            let new_var = new_env.insert_var(&arg.name, false, &arg.arg_type)?;
            new_env.assume(new_var.safe_eq(value)?);
            // arg.arg_type.check_value(&new_var, &mut new_env)?;
        }
        Ok(new_env)
    }
}

impl TStmt {
    fn z3_check(&self, env: &mut Env) -> Result<TStmt, CheckError> {
        match self {
            TStmt::Expr(expr) => {
                let expr = expr.z3_check(env)?.1;
                Ok(TStmt::Expr(expr))
            }
            TStmt::Let {
                name,
                typ,
                value,
                mutable,
                ..
            } => {
                let (z3_value, new_value) = value.z3_check(env)?;
                let z3_var = env.insert_var(name, *mutable, typ)?;
                env.assume(z3_var.safe_eq(&z3_value)?);
                // check the type
                env.assert_exprs(
                    &typ.type_assertions(
                        TExpr::Variable {
                            name: name.clone(),
                            typ: typ.clone(),
                        },
                        &env.type_param_list,
                    )?,
                    "Type assertion failed in let",
                )?;
                Ok(TStmt::Let {
                    name: name.clone(),
                    typ: typ.clone(),
                    type_declared: true,
                    mutable: *mutable,
                    value: new_value,
                })
            }
            TStmt::Assign { name, value, typ } => {
                let (z3_value, new_value) = value.z3_check(env)?;
                env.assign(name, z3_value)?;
                Ok(TStmt::Assign {
                    name: name.clone(),
                    typ: typ.clone(),
                    value: new_value,
                })
            }
        }
    }
}

fn int(x: &Dynamic) -> Result<z3::ast::Int, CheckError> {
    x.as_int().ok_or_else(|| CheckError {
        message: format!("Expected Int type, got {:?} of sort {:?}", x, x.get_sort()),
    })
}

fn boolean(x: &Dynamic) -> Result<z3::ast::Bool, CheckError> {
    x.as_bool().ok_or_else(|| CheckError {
        message: format!("Expected Bool type, got {:?} of sort {:?}", x, x.get_sort()),
    })
}

fn string(x: &Dynamic) -> Result<z3::ast::String, CheckError> {
    x.as_string().ok_or_else(|| CheckError {
        message: format!(
            "Expected String type, got {:?} of sort {:?}",
            x,
            x.get_sort()
        ),
    })
}

fn void_value() -> Dynamic {
    // There is no direct Void type in Z3, so we can use a dummy value
    z3::ast::Int::from_i64(0).into()
}

fn z3_function_call(name: &str, args: &[Dynamic], env: &mut Env) -> Result<Dynamic, CheckError> {
    match (name, args.len()) {
        ("==", 2) => Ok(args[0].safe_eq(&args[1])?.into()),
        ("!=", 2) => Ok(args[0].safe_eq(&args[1])?.not().into()),
        ("<", 2) => Ok(int(&args[0])?.lt(&int(&args[1])?).into()),
        ("<=", 2) => Ok(int(&args[0])?.le(&int(&args[1])?).into()),
        (">", 2) => Ok(int(&args[0])?.gt(&int(&args[1])?).into()),
        (">=", 2) => Ok(int(&args[0])?.ge(&int(&args[1])?).into()),
        ("+", 2) => Ok((int(&args[0])? + int(&args[1])?).into()),
        ("-", 2) => Ok((int(&args[0])? - int(&args[1])?).into()),
        ("*", 2) => Ok((int(&args[0])? * int(&args[1])?).into()),
        ("%", 2) => Ok((int(&args[0])? % int(&args[1])?).into()),
        ("/", 2) => Ok((int(&args[0])? / int(&args[1])?).into()),
        ("&&", 2) => Ok((boolean(&args[0])? & boolean(&args[1])?).into()),
        ("||", 2) => Ok((boolean(&args[0])? | boolean(&args[1])?).into()),
        ("assert", 1) => {
            let bool_arg = boolean(&args[0])?;
            env.assert(&bool_arg, "Assertion failed")?;
            Ok(void_value())
        }
        ("println", 1) => {
            string(&args[0])?;
            env.prints();
            Ok(void_value())
        }
        ("seq_len", 1) => {
            let seq_arg = args[0].as_seq().ok_or_else(|| CheckError {
                message: "Expected Seq type for seq_len".to_owned(),
            })?;
            Ok(seq_arg.length().into())
        }
        ("seq_at", 2) => {
            let seq_arg = args[0].as_seq().ok_or_else(|| CheckError {
                message: "Expected Seq type for seq_at".to_owned(),
            })?;
            let index_arg = int(&args[1])?;
            Ok(seq_arg.nth(&index_arg))
        }
        ("seq_map", 2) => {
            let seq_arg = args[0].as_seq().ok_or_else(|| CheckError {
                message: "Expected Seq type for seq_map".to_owned(),
            })?;
            let lambda_arg = args[1].as_array().ok_or_else(|| CheckError {
                message: "Expected Lambda type for seq_map".to_owned(),
            })?;
            let mapped_seq = seq_arg.map(&lambda_arg);
            Ok(mapped_seq.into())
        }
        ("seq_foldl", 3) => {
            let seq_arg = args[0].as_seq().ok_or_else(|| CheckError {
                message: "Expected Seq type for seq_foldl".to_owned(),
            })?;
            let lambda_arg = args[1].as_array().ok_or_else(|| CheckError {
                message: "Expected Lambda type for seq_foldl".to_owned(),
            })?;
            let init_arg = &args[2];
            let folded_value = seq_arg.fold_left(&lambda_arg, init_arg);
            Ok(folded_value)
        }
        _ => {
            if let Some(user_func) = env.other_funcs.iter().find(|f| f.name == name) {
                let user_func = user_func.clone(); // clone it because we're doing other things to env and they conflict
                let func_decl = user_func.z3_func_decl()?;

                let z3_argrefs = args
                    .iter()
                    .map(|a| a as &dyn z3::ast::Ast)
                    .collect::<Vec<&dyn z3::ast::Ast>>();
                let ast = func_decl.apply(&z3_argrefs);

                // don't forget the side effects
                for effect in &user_func.side_effects {
                    env.side_effects.insert(effect.clone());
                }

                // If function is visible, check it (which will add relevant assumptions)
                if env.sees.contains(&user_func.name) {
                    assert!(user_func.body.is_some());
                    let mut call_env = env.enter_call_scope(&user_func, args)?;
                    let body_z3_value = user_func.body.as_ref().unwrap().z3_check(&mut call_env)?.0;
                    call_env.assume(ast.safe_eq(&body_z3_value)?);
                    // fold back into main env
                    env.fold_in_scope(&call_env);
                }

                Ok(ast)
            } else {
                Err(CheckError {
                    message: format!("Undefined function: {}", name),
                })
            }
        }
    }
}

impl Env {
    fn get_overloaded_func(&self, name: &str) -> Result<TFuncDef, CheckError> {
        if self.builtins.contains_key(name) {
            Ok(self.builtins.get(name).unwrap().clone())
        } else {
            self.other_funcs
                .iter()
                .find(|f| f.name == name)
                .cloned()
                .ok_or_else(|| CheckError {
                    message: format!("Undefined function: {}", name),
                })
        }
    }

    fn keep_optimizations(
        &mut self,
        func: &TFuncDef,
        exprs: &[TExpr],
    ) -> Result<TFuncDef, CheckError> {
        let arg_types = exprs.iter().map(|e| e.typ()).collect::<Vec<Type>>();
        let func = func.instantiate_from_types(&arg_types)?;
        assert!(arg_types.len() == exprs.len());
        let mut optimizations = vec![];
        assert!(
            func.type_params.is_empty(),
            "Type parameters not supported in z3 check yet"
        );
        for opt in &func.optimizations {
            let assumptions = opt.assumptions_when_applying(&arg_types, exprs)?;
            let mut ok = true;
            for assumption in assumptions {
                let cond_z3_value = assumption.z3_check(self)?.0;
                if !self.probe(&boolean(&cond_z3_value)?) {
                    ok = false;
                    break;
                }
            }
            if ok {
                optimizations.push(opt.clone());
            } else if self.verbosity >= 2 {
                println!("Rejecting optimization {}", opt.debug_name);
            }
        }
        Ok(TFuncDef {
            name: func.name.clone(),
            args: func.args.clone(),
            return_name: func.return_name.clone(),
            return_type: func.return_type.clone(),
            type_params: func.type_params.clone(),
            attributes: func.attributes.clone(),
            preconditions: func.preconditions.clone(),
            postconditions: func.postconditions.clone(),
            side_effects: func.side_effects.clone(),
            sees: func.sees.clone(),
            body: func.body.clone(),
            optimizations,
        })
    }
}

impl TExpr {
    fn z3_check(&self, env: &mut Env) -> Result<(Dynamic, TExpr), CheckError> {
        // println!("Z3 checking expr: {}", self);
        match self {
            TExpr::Literal(literal) => Ok((literal.z3_check()?, self.clone())),
            TExpr::Variable { name, .. } => Ok((env.get_var(name)?, self.clone())),
            TExpr::FunctionCall { name, args, .. } => {
                let argpairs = args
                    .iter()
                    .map(|arg| arg.z3_check(env))
                    .collect::<Result<Vec<_>, _>>()?;
                let z3args = argpairs
                    .iter()
                    .map(|(z3arg, _)| z3arg.clone())
                    .collect::<Vec<_>>();
                let newargs = argpairs
                    .iter()
                    .map(|(_, texpr)| texpr.clone())
                    .collect::<Vec<_>>();
                let func = env.get_overloaded_func(name)?;
                let func = env.keep_optimizations(&func, args)?;
                let preconditions = func.lookup_preconditions(args)?;
                if env.verbosity >= 2 && !func.preconditions.is_empty() {
                    println!(
                        "Begin precondition check for function call {}, preconditions {:?}",
                        name, func.preconditions
                    );
                }
                for cond in preconditions {
                    let cond_z3_value = cond.z3_check(env)?.0;
                    env.assert(&boolean(&cond_z3_value)?, "Type precondition failed")?;
                }
                if env.verbosity >= 2 && !func.preconditions.is_empty() {
                    println!("End precondition check for function call {}", name);
                }
                let ast = z3_function_call(name, &z3args, env)?;
                let new_expr = TExpr::FunctionCall {
                        name: name.clone(),
                        args: newargs,
                        return_type: func.return_type.clone(),
                        optimizations: func.optimizations.clone(),
                    };

                let postconditions = func.postconditions_and_type_postconditions()?;
                if !postconditions.is_empty() {
                    if env.verbosity >= 2 {
                        println!(
                            "Assuming postconditions for function call {}: {:?}",
                            name, postconditions
                        );
                    }
                    let mut new_env = env.enter_call_scope(&func, &z3args)?;
                    new_env.insert_var_with_value(&func.return_name, &func.return_type, &ast)?;
                    for postcondition in &postconditions {
                        let cond_z3_value = postcondition.z3_check(&mut new_env)?.0;
                        // if env.verbosity >= 2 {
                        //     println!(
                        //         "Assuming postcondition for function call {}: {:?}",
                        //         name, cond_z3_value
                        //     );
                        // }
                        new_env.assume(boolean(&cond_z3_value)?);
                    }
                    env.fold_in_assumptions(&new_env);
                }

                Ok((
                    ast,
                    new_expr,
                ))
            }
            TExpr::Semicolon(stmt, expr) => {
                let new_stmt = stmt.z3_check(env)?;
                let new_expr = expr.z3_check(env)?;
                Ok((
                    new_expr.0,
                    TExpr::Semicolon(Box::new(new_stmt), Box::new(new_expr.1)),
                ))
            }
            TExpr::Sequence {
                elements,
                elem_type,
            } => {
                let elempairs = elements
                    .iter()
                    .map(|elem| elem.z3_check(env))
                    .collect::<Result<Vec<_>, _>>()?;
                let z3elems = elempairs
                    .iter()
                    .map(|(z3elem, _)| z3elem.clone())
                    .collect::<Vec<_>>();
                let newelems = elempairs
                    .iter()
                    .map(|(_, texpr)| texpr.clone())
                    .collect::<Vec<_>>();
                Ok((
                    mk_z3_sequence(z3elems, elem_type)?,
                    TExpr::Sequence {
                        elements: newelems,
                        elem_type: elem_type.clone(),
                    },
                ))
            }
            TExpr::EmptySequence => {
                unreachable!("We shouldn't see EmptySequence past type checking");
            }
            TExpr::Lambda { args, body } => {
                let mut new_env = env.clone();
                let mut vars: Vec<Dynamic> = vec![];
                for arg in args {
                    vars.push(new_env.insert_var(&arg.name, false, &arg.arg_type)?);
                }
                let arg_refs = vars
                    .iter()
                    .map(|a| a as &dyn z3::ast::Ast)
                    .collect::<Vec<&dyn z3::ast::Ast>>();
                let (z3_body, new_body) = body.z3_check(&mut new_env)?;
                let array = z3::ast::lambda_const(&arg_refs, &z3_body);
                Ok((
                    array.into(),
                    TExpr::Lambda {
                        args: args.clone(),
                        body: Box::new(new_body),
                    },
                ))
            }
        }
    }
}

fn mk_z3_sequence(elems: Vec<Dynamic>, elem_type: &Type) -> Result<Dynamic, CheckError> {
    if elems.is_empty() {
        return Ok(z3::ast::Seq::empty(&elem_type.to_z3_sort()?).into());
    }
    // let elem_sort = elem_type.to_z3_sort()?;
    let mut z3_units: Vec<z3::ast::Seq> = Vec::new();
    for elem in elems {
        z3_units.push(z3::ast::Seq::unit(&elem));
    }
    let seq_ast = z3::ast::Seq::concat(&z3_units);
    Ok(seq_ast.into())
}

fn z3_check_funcdef(
    func: &TFuncDef,
    other_funcs: &[TFuncDef],
    verbosity: u8,
) -> Result<TFuncDef, CheckError> {
    if verbosity >= 2 {
        println!("\n\n\nChecking function: {}. New env.", func.name);
    }
    let mut env = Env::new(other_funcs, &func.sees, verbosity);
    for arg in &func.args {
        env.insert_var(&arg.name, false, &arg.arg_type)?;
        assert!(
            env.type_param_list.is_empty(),
            "Type parameters not supported in z3 check yet"
        );
        // assume the type assertions on the argument
        env.assume_exprs(&arg.arg_type.type_assertions(
            TExpr::Variable {
                name: arg.name.clone(),
                typ: arg.arg_type.clone(),
            },
            &env.type_param_list,
        )?)?;
    }
    env.assume_exprs(&func.preconditions)?;
    assert!(func.body.is_some());
    let (body_z3_value, new_body) = func.body.as_ref().unwrap().z3_check(&mut env)?;

    let ret = &func.return_name;
    let ret_var = env.insert_var(ret, false, &func.return_type)?;
    env.assume(ret_var.safe_eq(&body_z3_value)?);

    // check return type
    env.assert_exprs(
        &func.return_type.type_assertions(
            TExpr::Variable {
                name: func.return_name.clone(),
                typ: func.return_type.clone(),
            },
            &env.type_param_list,
        )?,
        "Type assertion failed on return",
    )?;

    // now check all the postconditions
    env.assert_exprs(&func.postconditions, "Postcondition failed")?;

    print!("Checked function: {}", func.name);
    env.print_side_effects();
    Ok(TFuncDef {
        attributes: func.attributes.clone(),
        name: func.name.clone(),
        args: func.args.clone(),
        return_type: func.return_type.clone(),
        return_name: func.return_name.clone(),
        side_effects: env.side_effects,
        preconditions: func.preconditions.clone(),
        postconditions: func.postconditions.clone(),
        sees: func.sees.clone(),
        body: Some(new_body),
        type_params: func.type_params.clone(),
        optimizations: func.optimizations.clone(),
    })
}

pub fn z3_check(source_file: &SourceFile, verbosity: u8) -> Result<(), CheckError> {
    let tsource_file = source_file.type_check()?;
    if verbosity >= 1 {
        println!("{}", tsource_file);
        println!("Type checking passed. Starting Z3 checking...");
    }

    let mut other_funcs = vec![];
    for func in &tsource_file.functions {
        let checked_func = z3_check_funcdef(func, &other_funcs, verbosity)?;
        other_funcs.push(checked_func.clone());
        if verbosity >= 2 {
            println!("Checked func body: {}", checked_func.body.unwrap());
        }
    }

    let tsource_file = TSourceFile {
        functions: other_funcs,
    };

    if verbosity >= 1 {
        println!("Z3 checking passed.");
        println!("Running optimization chooser...");
    }
    let optimized_tsource_file = tsource_file.choose_optimization(verbosity)?;
    if verbosity >= 1 {
        println!("Optimization choosing passed.");
        println!("{}", optimized_tsource_file);
        println!("That's it for this file.")
    }

    Ok(())
}
