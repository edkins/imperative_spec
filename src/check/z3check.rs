use std::{
    collections::{HashMap, HashSet},
    error::Error,
    ffi::NulError,
    fmt::Display,
    str::FromStr,
};

use crate::{
    check::{
        builtins::lookup_builtin,
        types::TypeError,
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
    other_funcs: Vec<FuncDef>,
    verbosity: u8,
    type_param_list: Vec<String>,
    sees: Vec<String>,
}

impl FuncDef {
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

    fn postconditions_and_type_postconditions(&self) -> Result<Vec<Expr>, CheckError> {
        let mut postconditions = self.postconditions.clone();
        let return_var = Expr::Variable {
            name: self.return_name.clone(),
            typ: Some(self.return_type.skeleton(&self.type_params)?),
        };
        let type_postconditions = self.return_type.type_assertions(return_var, &self.type_params)?;
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
        self.z3 = self
            .var_type
            .to_z3_const(&format!("{}:{}", self.name, self.version))
            .unwrap();
    }

    fn replace(&mut self, mutable: bool, typ: &Type) {
        self.hidden = false;
        self.max_version += 1;
        self.version = self.max_version;
        self.mutable = mutable;
        self.var_type = typ.clone();
        self.z3 = self
            .var_type
            .to_z3_const(&format!("{}:{}", self.name, self.version))
            .unwrap();
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
    fn z3_datatype_name(&self) -> String {
        let mut name = self.name.to_owned();
        if !self.type_args.is_empty() {
            name.push('<');
            for (i, arg) in self.type_args.iter().enumerate() {
                match arg {
                    TypeArg::Type(t) => {
                        name.push_str(&t.z3_datatype_name());
                    }
                    TypeArg::Bound(b) => {
                        name.push_str(&b.to_string());
                    }
                }
                if i + 1 < self.type_args.len() {
                    name.push(',');
                }
            }
            name.push('>');
        }
        name
    }

    fn to_z3_datatype(&self) -> Result<z3::DatatypeSort, CheckError> {
        if self.is_round_seq() {
            if let Some(elem_types) = self.get_round_elem_type_vector() {
                let datatype_name = self.z3_datatype_name();
                let mut sorts = vec![];
                for (i, et) in elem_types.iter().enumerate() {
                    sorts.push((i.to_string(), et.to_z3_sort()?));
                }
                let sorts = sorts
                    .iter()
                    .map(|(name, sort)| (name.as_str(), z3::DatatypeAccessor::Sort(sort.clone())))
                    .collect::<Vec<_>>();
                Ok(z3::DatatypeBuilder::new(datatype_name)
                    .variant("Tuple", sorts)
                    .finish())
            } else {
                Err(CheckError {
                    message: format!(
                        "Round sequence type {} does not have known element types",
                        self
                    ),
                })
            }
        } else {
            Err(CheckError {
                message: format!("Unsupported type for to_z3_sort: {}", self),
            })
        }
    }

    fn to_z3_sort(&self) -> Result<z3::Sort, CheckError> {
        if self.is_int() {
            Ok(z3::Sort::int())
        } else if self.is_bool() {
            Ok(z3::Sort::bool())
        } else if self.is_str() {
            Ok(z3::Sort::string())
        } else if self.is_void() {
            Ok(void_value().get_sort())
        } else if self.is_square_seq() {
            if let Some(elem_type) = self.get_uniform_square_elem_type() {
                let elem_sort = elem_type.to_z3_sort()?;
                Ok(z3::Sort::seq(&elem_sort))
            } else {
                Err(CheckError {
                    message: format!(
                        "Square sequence type {} does not have known uniform element type",
                        self
                    ),
                })
            }
        } else {
            Ok(self.to_z3_datatype()?.sort)
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
        } else if self.is_square_seq() {
            let elem_sort = self
                .get_uniform_square_elem_type()
                .ok_or_else(|| CheckError {
                    message: format!(
                        "Square sequence type {} does not have known uniform element type",
                        self
                    ),
                })?
                .to_z3_sort()?;
            Ok(z3::ast::Seq::new_const(name, &elem_sort).into())
        } else if self.is_round_seq() {
            let dt = self.to_z3_datatype()?;
            Ok(z3::ast::Datatype::new_const(name, &dt.sort).into())
        } else {
            Err(CheckError {
                message: format!("Unsupported type for to_z3_const: {}", self),
            })
        }
    }
}

impl Env {
    fn new(other_funcs: &[FuncDef], attributes: &[FuncAttribute], verbosity: u8) -> Self {
        let sees = attributes
            .iter()
            .filter_map(|attr| {
                if let FuncAttribute::Sees(name) = attr {
                    Some(name.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<String>>();
        Env {
            vars: HashMap::new(),
            assumptions: Vec::new(),
            side_effects: HashSet::new(),
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
        Ok(self
            .vars
            .entry(name.to_owned())
            .and_modify(|info| info.replace(mutable, ty))
            .or_insert_with(|| CheckedVar::new(name, mutable, ty))
            .z3
            .clone())
    }

    fn insert_var_with_value(
        &mut self,
        name: &str,
        ty: &Type,
        value: &Dynamic,
    ) -> Result<(), CheckError> {
        assert!(
            !self.vars.contains_key(name),
            "Variable {} already defined",
            name
        );
        self.vars
            .insert(name.to_owned(), CheckedVar::new_with_value(name, ty, value));
        Ok(())
    }

    fn assume_exprs(&mut self, exprs: &[Expr]) -> Result<(), CheckError> {
        for expr in exprs {
            self.assume_expr(expr)?;
        }
        Ok(())
    }

    fn assume_expr(&mut self, expr: &Expr) -> Result<(), CheckError> {
        let cond_z3_value = expr.z3_check(self)?;
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

    fn assert_exprs(&mut self, exprs: &[Expr], message: &str) -> Result<(), CheckError> {
        for expr in exprs {
            self.assert_expr(expr, message)?;
        }
        Ok(())
    }

    fn assert_expr(&mut self, expr: &Expr, message: &str) -> Result<(), CheckError> {
        let cond_z3_value = expr.z3_check(self)?;
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

    // fn print_side_effects(&self) {
    //     let mut effects: Vec<_> = self.side_effects.iter().collect();
    //     effects.sort();
    //     for effect in &effects {
    //         print!(" {{{}}}", effect);
    //     }
    //     println!();
    // }

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
            Expr::Variable {
                name: var.to_owned(),
                typ: Some(info.var_type.clone()),
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

    fn enter_call_scope(&self, func: &FuncDef, args: &[Dynamic]) -> Result<Env, CheckError> {
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

impl Stmt {
    fn z3_check(&self, env: &mut Env) -> Result<(), CheckError> {
        match self {
            Stmt::Expr(expr) => {
                expr.z3_check(env)?;
                Ok(())
            }
            Stmt::Let {
                name,
                typ,
                value,
                mutable,
                ..
            } => {
                let z3_value = value.z3_check(env)?;
                let inferred_type = typ.clone().unwrap_or_else(||value.typ());
                let z3_var = env.insert_var(name, *mutable, &inferred_type)?;
                env.assume(z3_var.safe_eq(&z3_value)?);
                // check the type
                env.assert_exprs(
                    &inferred_type.type_assertions(
                        Expr::Variable {
                            name: name.clone(),
                            typ: Some(value.typ()),
                        },
                        &env.type_param_list,
                    )?,
                    "Type assertion failed in let",
                )?;
                Ok(())
            }
            Stmt::Assign { name, value, .. } => {
                let z3_value = value.z3_check(env)?;
                env.assign(name, z3_value)?;
                Ok(())
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
        ("neg", 1) => Ok((-int(&args[0])?).into()),
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
                for effect in &user_func.attributes {
                    if let FuncAttribute::SideEffect(effect) = effect {
                        env.side_effects.insert(effect.clone());
                    }
                }

                // If function is visible, check it (which will add relevant assumptions)
                if env.sees.contains(&user_func.name) {
                    let mut call_env = env.enter_call_scope(&user_func, args)?;
                    let body_z3_value = user_func.body.z3_check(&mut call_env)?;
                    call_env.assume(ast.safe_eq(&body_z3_value)?);
                    // fold back into main env
                    env.fold_in_scope(&call_env);
                }

                Ok(ast)
            } else {
                Err(CheckError {
                    message: format!("No z3 implementation for function: {}", name),
                })
            }
        }
    }
}

impl Env {
    fn get_overloaded_func(&self, name: &str) -> Result<FuncDef, CheckError> {
        if let Some(b) = lookup_builtin(name) {
            Ok(b)
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

    // fn keep_optimizations(
    //     &mut self,
    //     func: &FuncDef,
    //     exprs: &[Expr],
    // ) -> Result<FuncDef, CheckError> {
    //     let arg_types = exprs.iter().map(|e| e.typ()).collect::<Vec<Type>>();
    //     let func = func.instantiate_from_types(&arg_types)?;
    //     assert!(arg_types.len() == exprs.len());
    //     let mut optimizations = vec![];
    //     assert!(
    //         func.type_params.is_empty(),
    //         "Type parameters not supported in z3 check yet"
    //     );
    //     for opt in &func.optimizations {
    //         let assumptions = opt.assumptions_when_applying(&arg_types, exprs)?;
    //         let mut ok = true;
    //         for assumption in assumptions {
    //             let cond_z3_value = assumption.z3_check(self)?.0;
    //             if !self.probe(&boolean(&cond_z3_value)?) {
    //                 ok = false;
    //                 break;
    //             }
    //         }
    //         if ok {
    //             optimizations.push(opt.clone());
    //         } else if self.verbosity >= 2 {
    //             println!("Rejecting optimization {}", opt.debug_name);
    //         }
    //     }
    //     Ok(FuncDef {
    //         name: func.name.clone(),
    //         args: func.args.clone(),
    //         return_name: func.return_name.clone(),
    //         return_type: func.return_type.clone(),
    //         type_params: func.type_params.clone(),
    //         attributes: func.attributes.clone(),
    //         preconditions: func.preconditions.clone(),
    //         postconditions: func.postconditions.clone(),
    //         body: func.body.clone(),
    //         optimizations,
    //     })
    // }
}

impl Expr {
    fn z3_check(&self, env: &mut Env) -> Result<Dynamic, CheckError> {
        // println!("Z3 checking expr: {}", self);
        match self {
            Expr::Literal(literal) => literal.z3_check(),
            Expr::Variable { name, .. } => env.get_var(name),
            Expr::FunctionCall { name, args, .. } => {
                let z3args = args
                    .iter()
                    .map(|arg| arg.z3_check(env))
                    .collect::<Result<Vec<_>, _>>()?;
                let func = env.get_overloaded_func(name)?;
                // let func = env.keep_optimizations(&func, args)?;
                // println!("{}, {:?}", name, args);
                let preconditions = func.lookup_preconditions(args)?;
                if env.verbosity >= 2 && !func.preconditions.is_empty() {
                    println!(
                        "Begin precondition check for function call {}, preconditions {:?}",
                        name, func.preconditions
                    );
                }
                for cond in preconditions {
                    let cond_z3_value = cond.z3_check(env)?;
                    env.assert(&boolean(&cond_z3_value)?, "Type precondition failed")?;
                }
                if env.verbosity >= 2 && !func.preconditions.is_empty() {
                    println!("End precondition check for function call {}", name);
                }
                let ast = z3_function_call(name, &z3args, env)?;

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
                        let cond_z3_value = postcondition.z3_check(&mut new_env)?;
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

                Ok(ast)
            }
            Expr::Semicolon(stmt, expr) => {
                stmt.z3_check(env)?;
                expr.z3_check(env)
            }
            Expr::SquareSequence {
                elems,
                elem_type,
            } => {
                let z3elems = elems
                    .iter()
                    .map(|elem| elem.z3_check(env))
                    .collect::<Result<Vec<_>, _>>()?;
                mk_z3_square_sequence(z3elems, elem_type.as_ref().unwrap())
            }
            Expr::RoundSequence { elems } => {
                let z3elems = elems
                    .iter()
                    .map(|elem| elem.z3_check(env))
                    .collect::<Result<Vec<_>, _>>()?;
                let seq_type = self.typ();
                mk_z3_round_sequence(z3elems, &seq_type)
            }
            Expr::Lambda { args, body } => {
                let mut new_env = env.clone();
                let mut vars: Vec<Dynamic> = vec![];
                for arg in args {
                    vars.push(new_env.insert_var(&arg.name, false, &arg.arg_type)?);
                }
                let arg_refs = vars
                    .iter()
                    .map(|a| a as &dyn z3::ast::Ast)
                    .collect::<Vec<&dyn z3::ast::Ast>>();
                let z3_body = body.z3_check(&mut new_env)?;
                let array = z3::ast::lambda_const(&arg_refs, &z3_body);
                Ok(array.into())
            }
            Expr::SeqAt { seq, index } => {
                if seq.typ().is_square_seq() {
                    let z3_seq = seq.z3_check(env)?;
                    let z3_index = int(&index.z3_check(env)?)?;
                    let seq_ast = z3_seq
                        .as_seq()
                        .ok_or_else(|| CheckError {
                            message: format!(
                                "Expected Seq type for seq_at, got {:?} of sort {:?}",
                                z3_seq,
                                z3_seq.get_sort()
                            ),
                        })?;
                    Ok(seq_ast.nth(&z3_index).into())
                } else {
                    let z3_tuple = seq.z3_check(env)?;
                    let dt = seq.typ().to_z3_datatype()?;
                    let index = index.as_literal_u64()? as usize;
                    let accessor = &dt.variants[0].accessors.get(index).ok_or_else(|| CheckError {
                        message: format!(
                            "Index {} out of bounds for round sequence type {}",
                            index,
                            seq.typ()
                        ),
                    })?;
                    let at_value = accessor.apply(&[&z3_tuple as &dyn z3::ast::Ast]);
                    Ok(at_value)
                }
            }
            // Expr::Cast { expr, to_type } => {
            //     let (z3_expr, new_expr) = expr.z3_check(env)?;
            //     if z3_expr.get_sort() != to_type.to_z3_sort()? {
            //         return Err(CheckError {
            //             message: format!(
            //                 "Cannot cast expression of z3 sort {:?} to type {} of z3 sort {:?}",
            //                 z3_expr.get_sort(),
            //                 to_type,
            //                 to_type.to_z3_sort()?
            //             ),
            //         });
            //     }
            //     Ok((
            //         z3_expr,
            //         Expr::Cast {
            //             expr: Box::new(new_expr),
            //             to_type: to_type.clone(),
            //         },
            //     ))
            // }
        }
    }
}

fn mk_z3_round_sequence(elems: Vec<Dynamic>, seq_type: &Type) -> Result<Dynamic, CheckError> {
    if !seq_type.is_round_seq() {
        return Err(CheckError {
            message: format!("Type {} is not a round sequence type", seq_type),
        });
    }
    let dt = seq_type.to_z3_datatype()?;
    Ok(dt.variants[0].constructor.apply(
        &elems
            .iter()
            .map(|e| e as &dyn z3::ast::Ast)
            .collect::<Vec<&dyn z3::ast::Ast>>(),
    ))
}

fn mk_z3_square_sequence(elems: Vec<Dynamic>, elem_type: &Type) -> Result<Dynamic, CheckError> {
    if elems.is_empty() {
        return Ok(z3::ast::Seq::empty(&elem_type.to_z3_sort()?).into());
    }
    let z3_units = elems
        .into_iter()
        .map(|elem| z3::ast::Seq::unit(&elem))
        .collect::<Vec<_>>();
    let seq_ast = z3::ast::Seq::concat(&z3_units);
    Ok(seq_ast.into())
}

fn z3_check_funcdef(
    func: &FuncDef,
    other_funcs: &[FuncDef],
    verbosity: u8,
) -> Result<(), CheckError> {
    if verbosity >= 2 {
        println!("\n\n\nChecking function: {}. New env.", func.name);
    }
    let mut env = Env::new(other_funcs, &func.attributes, verbosity);
    for arg in &func.args {
        env.insert_var(&arg.name, false, &arg.arg_type.skeleton(&func.type_params)?)?;
        assert!(
            env.type_param_list.is_empty(),
            "Type parameters not supported in z3 check yet"
        );
        // assume the type assertions on the argument
        env.assume_exprs(&arg.arg_type.type_assertions(
            Expr::Variable {
                name: arg.name.clone(),
                typ: Some(arg.arg_type.skeleton(&env.type_param_list)?),
            },
            &env.type_param_list,
        )?)?;
    }
    env.assume_exprs(&func.preconditions)?;
    let body_z3_value = func.body.z3_check(&mut env)?;

    let ret = &func.return_name;
    let return_skel = func.return_type.skeleton(&func.type_params)?;
    let ret_var = env.insert_var(ret, false, &return_skel)?;
    env.assume(ret_var.safe_eq(&body_z3_value)?);

    // check return type
    env.assert_exprs(
        &func.return_type.type_assertions(
            Expr::Variable {
                name: func.return_name.clone(),
                typ: Some(return_skel.clone()),
            },
            &env.type_param_list,
        )?,
        "Type assertion failed on return",
    )?;

    // now check all the postconditions
    env.assert_exprs(&func.postconditions, "Postcondition failed")?;

    // let mut attributes = func.attributes.clone();
    // for effect in &env.side_effects {
    //     let se = FuncAttribute::SideEffect(effect.clone());
    //     if !attributes.contains(&se) {
    //         attributes.push(se);
    //     }
    // }

    println!("Checked function: {}", func.name);
    Ok(())
}

pub fn z3_check(source_file: &SourceFile, verbosity: u8) -> Result<(), CheckError> {
    let mut other_funcs = vec![];
    for func in &source_file.functions {
        z3_check_funcdef(func, &other_funcs, verbosity)?;
        other_funcs.push(func.clone());
    }

    // let tsource_file = TSourceFile {
    //     functions: other_funcs,
    // };

    // if verbosity >= 1 {
    //     println!("Z3 checking passed.");
    //     println!("Running optimization chooser...");
    // }
    // let optimized_tsource_file = tsource_file.choose_optimization(verbosity)?;
    // if verbosity >= 1 {
    //     println!("Optimization choosing passed.");
    //     println!("{}", optimized_tsource_file);
    //     println!("That's it for this file.")
    // }

    Ok(())
}
