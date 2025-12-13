use std::collections::HashMap;

use crate::{
    check::{builtins::all_builtins, types::TypeError},
    syntax::ast::{AssignOp, CallArg, Expr, FuncDef, Literal, SourceFile, Stmt, Type, TypeArg},
};

#[derive(Clone)]
struct DeclaredFuncType {
    arg_types: Vec<Type>,
    ret_type: Type,
    type_params: Vec<String>,
}

#[derive(Clone, Default)]
struct TypeVars {
    debug_func_name: String,
    counter: usize,
    expansions: HashMap<String, Type>,
    functions: HashMap<String, DeclaredFuncType>,
}

#[derive(Clone, Default)]
struct HMEnv {
    vars: HashMap<String, Type>,
    mutable_vars: HashMap<String, Type>,
}

#[derive(Clone, Default)]
struct TypeParamLookup(HashMap<String, Type>);

impl TypeParamLookup {
    fn translate_type_arg(&self, arg: &TypeArg) -> Result<TypeArg, TypeError> {
        match arg {
            TypeArg::Type(typ) => Ok(TypeArg::Type(self.translate_type(typ)?)),
            TypeArg::Bound(b) => Ok(TypeArg::Bound(*b)),
        }
    }

    fn translate_type(&self, typ: &Type) -> Result<Type, TypeError> {
        if let Some(t) = self.0.get(&typ.name) {
            if !t.type_args.is_empty() {
                return Err(TypeError {
                    message: format!("Type parameter {} cannot have type arguments", typ.name),
                });
            }
            Ok(t.clone())
        } else {
            let translated_args = typ
                .type_args
                .iter()
                .map(|arg| self.translate_type_arg(arg))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Type {
                name: typ.name.clone(),
                type_args: translated_args,
            })
        }
    }
}

struct FunctionGeneralizationResult {
    arg_types: Vec<Type>,
    ret_type: Type,
    type_param_lookup: TypeParamLookup,
}

impl Type {
    fn is_type_var(&self) -> bool {
        self.name.starts_with('\'') && self.type_args.is_empty()
    }

    fn occurs_check(&self, var_name: &str) -> bool {
        if self.is_type_var() && self.name == var_name {
            return true;
        }
        for arg in &self.type_args {
            match arg {
                TypeArg::Type(t) => {
                    if t.occurs_check(var_name) {
                        return true;
                    }
                }
                TypeArg::Bound(_) => {}
            }
        }
        false
    }
}

impl Expr {
    pub fn as_literal_u64(&self) -> Result<u64, TypeError> {
        if let Expr::Literal(lit) = self {
            match lit {
                Literal::U64(u) => Ok(*u),
                Literal::I64(i) if *i >= 0 => Ok(*i as u64),
                _ => Err(TypeError {
                    message: format!("Expected u64 literal, got {}", lit),
                }),
            }
        } else {
            Err(TypeError {
                message: format!("Expected literal expression, got {}", self),
            })
        }
    }
}

impl TypeVars {
    fn fresh_type_var(&mut self) -> String {
        let var_name = format!("'{}", self.counter);
        self.counter += 1;
        var_name
    }

    fn unify(&mut self, t0: &Type, t1: &Type) -> Result<(), TypeError> {
        let t0 = self.expand_type(t0, true)?;
        let t1 = self.expand_type(t1, true)?;
        if t0 == t1 {
            return Ok(());
        }
        if t0.is_type_var() {
            if t1.occurs_check(&t0.name) {
                return Err(TypeError {
                    message: format!("Occurs check failed for type variable {}", t0.name),
                });
            }
            self.expansions.insert(t0.name.clone(), t1.clone());
            return Ok(());
        }
        if t1.is_type_var() {
            if t0.occurs_check(&t1.name) {
                return Err(TypeError {
                    message: format!("Occurs check failed for type variable {}", t1.name),
                });
            }
            self.expansions.insert(t1.name.clone(), t0.clone());
            return Ok(());
        }
        if t0.name != t1.name || t0.type_args.len() != t1.type_args.len() {
            return Err(TypeError {
                message: format!("Cannot unify types {} and {}", t0.name, t1.name),
            });
        }
        for (arg0, arg1) in t0.type_args.iter().zip(&t1.type_args) {
            match (arg0, arg1) {
                (TypeArg::Type(ta0), TypeArg::Type(ta1)) => {
                    self.unify(ta0, ta1)?;
                }
                (TypeArg::Bound(b0), TypeArg::Bound(b1)) => {
                    if b0 != b1 {
                        return Err(TypeError {
                            message: format!("Cannot unify bound type arguments {} and {}", b0, b1),
                        });
                    }
                }
                _ => {
                    return Err(TypeError {
                        message: format!("Cannot unify type arguments {} and {}", arg0, arg1),
                    });
                }
            }
        }
        Ok(())
    }

    fn generalize_function(
        &mut self,
        func: &DeclaredFuncType,
    ) -> Result<FunctionGeneralizationResult, TypeError> {
        // Generate type variables for each type param
        let mut type_param_lookup = TypeParamLookup::default();
        for param in &func.type_params {
            let var_name = self.fresh_type_var();
            type_param_lookup
                .0
                .insert(param.clone(), Type::basic(&var_name));
        }

        let mut arg_types = vec![];
        for arg_type in &func.arg_types {
            arg_types.push(type_param_lookup.translate_type(arg_type)?);
        }
        Ok(FunctionGeneralizationResult {
            arg_types,
            ret_type: type_param_lookup.translate_type(&func.ret_type)?,
            type_param_lookup,
        })
    }

    fn infer_call_arg(
        &mut self,
        arg: &mut CallArg,
        env: &HMEnv,
        expected: Option<&Type>,
    ) -> Result<Type, TypeError> {
        match arg {
            CallArg::Expr(e) => self.infer_expr(e, env, expected),
            CallArg::MutVar { name, typ } => {
                assert!(typ.is_none());
                if let Some(t) = env.mutable_vars.get(name) {
                    typ.replace(t.clone());
                    Ok(t.clone())
                } else {
                    Err(TypeError {
                        message: format!(
                            "Unknown mutable variable: {} in function {}",
                            name, self.debug_func_name
                        ),
                    })
                }
            }
        }
    }

    fn infer_expr(
        &mut self,
        expr: &mut Expr,
        env: &HMEnv,
        expected: Option<&Type>,
    ) -> Result<Type, TypeError> {
        let actual_type = match expr {
            Expr::Literal(literal) => literal.typ(),
            Expr::Variable { name, typ } => {
                assert!(typ.is_none());
                if let Some(t) = env.vars.get(name) {
                    *typ = Some(t.clone());
                    t.clone()
                } else {
                    return Err(TypeError {
                        message: format!(
                            "Unknown variable: {} in function {}",
                            name, self.debug_func_name
                        ),
                    });
                }
            }
            Expr::Semicolon(stmt, expr) => {
                let new_env = self.infer_stmt(stmt, env)?;
                self.infer_expr(expr, &new_env, expected)?
            }
            Expr::FunctionCall {
                name,
                args,
                type_instantiations,
                return_type,
            } => {
                assert!(return_type.is_none());
                assert!(type_instantiations.is_empty());
                if let Some(func_type) = self.functions.get(name).cloned() {
                    if func_type.arg_types.len() != args.len() {
                        return Err(TypeError {
                            message: format!(
                                "Function {} expects {} arguments, got {}",
                                name,
                                func_type.arg_types.len(),
                                args.len()
                            ),
                        });
                    }
                    let gen_result = self.generalize_function(&func_type)?;
                    for (arg, expected_type) in args.iter_mut().zip(gen_result.arg_types.iter()) {
                        self.infer_call_arg(arg, env, Some(expected_type))?;
                    }
                    return_type.replace(gen_result.ret_type.clone());
                    *type_instantiations = func_type
                        .type_params
                        .iter()
                        .map(|param| gen_result.type_param_lookup.0.get(param).unwrap().clone())
                        .collect();
                    gen_result.ret_type
                } else {
                    return Err(TypeError {
                        message: format!("Unknown function: {}", name),
                    });
                }
            }
            Expr::RoundSequence { elems } => {
                let mut type_args = vec![];
                for elem in elems.iter_mut() {
                    type_args.push(TypeArg::Type(self.infer_expr(elem, env, None)?));
                }
                Type {
                    name: "Tuple".to_owned(),
                    type_args,
                }
            }
            Expr::SquareSequence { elems, elem_type } => {
                assert!(elem_type.is_none());
                let tvar = self.fresh_type_var();
                elem_type.replace(Type::basic(&tvar));
                for elem in elems.iter_mut() {
                    self.infer_expr(elem, env, Some(&Type::basic(&tvar)))?;
                }
                Type {
                    name: "Vec".to_owned(),
                    type_args: vec![TypeArg::Type(Type::basic(&tvar))],
                }
            }
            Expr::Lambda { args, body } => {
                let mut new_env = env.clone();
                let mut arg_skels = vec![];
                for arg in args.iter() {
                    let arg_skel = arg.arg_type.skeleton(&[])?; // currently lambdas must declare all their types
                    new_env.vars.insert(arg.name.clone(), arg_skel.clone());
                    arg_skels.push(arg_skel);
                }
                let body_type = self.infer_expr(body, &new_env, None)?;
                Type {
                    name: "Lambda".to_owned(),
                    type_args: arg_skels
                        .into_iter()
                        .map(|t| TypeArg::Type(t))
                        .chain(std::iter::once(TypeArg::Type(body_type)))
                        .collect(),
                }
            }
            Expr::SeqAt { seq, index } => {
                let seq_type = self.infer_expr(seq, env, None)?;
                if seq_type.is_square_seq() {
                    let elem_type = seq_type.get_uniform_square_elem_type().unwrap().clone();
                    self.infer_expr(index, env, Some(&Type::basic("int")))?;
                    elem_type
                } else if seq_type.is_round_seq() {
                    let index = index.as_literal_u64()?;
                    if index >= seq_type.get_round_seq_length().unwrap() {
                        return Err(TypeError {
                            message: format!(
                                "Index {} out of bounds for sequence of length {}",
                                index,
                                seq_type.get_round_seq_length().unwrap()
                            ),
                        });
                    }
                    let elem_type = seq_type.get_round_elem_type(index).unwrap();
                    elem_type.clone()
                } else {
                    return Err(TypeError {
                        message: format!("Type {} is not a sequence type", seq_type),
                    });
                }
            }
        };

        if let Some(expected_type) = expected {
            println!("For expression {}, unifying actual type {} with expected type {}", expr, actual_type, expected_type);
            self.unify(&actual_type, expected_type)?;
        }
        Ok(actual_type)
    }

    fn infer_stmt(&mut self, stmt: &mut Stmt, env: &HMEnv) -> Result<HMEnv, TypeError> {
        match stmt {
            Stmt::Expr(expr) => {
                self.infer_expr(expr, env, None)?;
                Ok(env.clone())
            }
            Stmt::Let {
                name,
                typ,
                value,
                mutable,
            } => {
                let styp = typ.as_ref().map(|t| t.skeleton(&[])).transpose()?;
                let inferred = self.infer_expr(value, env, styp.as_ref())?;
                let mut new_env = env.clone();
                new_env.vars.insert(name.clone(), inferred.clone());
                if *mutable {
                    assert!(typ.is_some());
                    new_env
                        .mutable_vars
                        .insert(name.clone(), typ.as_ref().unwrap().clone());
                }
                Ok(new_env)
            }
            Stmt::Assign { name, op, value } => {
                *stmt = Stmt::Expr(Expr::FunctionCall {
                    name: op.function_name().to_owned(),
                    args: vec![
                        CallArg::MutVar {
                            name: name.clone(),
                            typ: None,
                        },
                        CallArg::Expr(value.clone()),
                    ],
                    type_instantiations: vec![],
                    return_type: None,
                });
                self.infer_stmt(stmt, env)
            }
        }
    }

    fn expand_type(&self, typ: &Type, allow_unbound: bool) -> Result<Type, TypeError> {
        if typ.is_type_var() {
            if let Some(expanded) = self.expansions.get(&typ.name) {
                self.expand_type(expanded, allow_unbound)
            } else {
                if allow_unbound {
                    Ok(typ.clone())
                } else {
                    Err(TypeError {
                        message: format!("Unbound type variable: {} in function {}", typ.name, self.debug_func_name),
                    })
                }
            }
        } else {
            let expanded_args = typ
                .type_args
                .iter()
                .map(|arg| match arg {
                    TypeArg::Type(t) => Ok(TypeArg::Type(self.expand_type(t, allow_unbound)?)),
                    TypeArg::Bound(b) => Ok(TypeArg::Bound(*b)),
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Type {
                name: typ.name.clone(),
                type_args: expanded_args,
            })
        }
    }

    fn expand_stmt(&self, stmt: &mut Stmt, allow_unbound: bool) -> Result<(), TypeError> {
        match stmt {
            Stmt::Expr(expr) => self.expand_expr(expr, allow_unbound),
            Stmt::Let { typ, value, .. } => {
                if let Some(t) = typ {
                    *t = self.expand_type(t, allow_unbound)?;
                }
                self.expand_expr(value, allow_unbound)
            }
            Stmt::Assign { value, .. } => self.expand_expr(value, allow_unbound),
        }
    }

    fn expand_call_arg(&self, arg: &mut CallArg, allow_unbound: bool) -> Result<(), TypeError> {
        match arg {
            CallArg::Expr(e) => self.expand_expr(e, allow_unbound),
            CallArg::MutVar { typ, .. } => {
                if let Some(t) = typ {
                    *t = self.expand_type(t, allow_unbound)?;
                }
                Ok(())
            }
        }
    }

    fn expand_expr(&self, expr: &mut Expr, allow_unbound: bool) -> Result<(), TypeError> {
        match expr {
            Expr::Literal(_) => Ok(()),
            Expr::Variable { typ, .. } => {
                if let Some(t) = typ {
                    *t = self.expand_type(t, allow_unbound)?;
                }
                Ok(())
            }
            Expr::Semicolon(stmt, expr) => {
                self.expand_stmt(stmt, allow_unbound)?;
                self.expand_expr(expr, allow_unbound)
            }
            Expr::FunctionCall {
                args,
                return_type,
                type_instantiations,
                ..
            } => {
                for arg in args.iter_mut() {
                    self.expand_call_arg(arg, allow_unbound)?;
                }
                if let Some(t) = return_type {
                    *t = self.expand_type(t, allow_unbound)?;
                }
                for t in type_instantiations.iter_mut() {
                    *t = self.expand_type(t, allow_unbound)?;
                }
                Ok(())
            }
            Expr::RoundSequence { elems } => {
                for elem in elems.iter_mut() {
                    self.expand_expr(elem, allow_unbound)?;
                }
                Ok(())
            }
            Expr::SquareSequence { elems, elem_type } => {
                for elem in elems.iter_mut() {
                    self.expand_expr(elem, allow_unbound)?;
                }
                if let Some(t) = elem_type {
                    *t = self.expand_type(t, allow_unbound)?;
                }
                Ok(())
            }
            Expr::Lambda { args, body } => {
                for arg in args.iter_mut() {
                    arg.arg_type = self.expand_type(&arg.arg_type, allow_unbound)?;
                }
                self.expand_expr(body, allow_unbound)
            }
            Expr::SeqAt { seq, index } => {
                self.expand_expr(seq, allow_unbound)?;
                self.expand_expr(index, allow_unbound)
            }
        }
    }

    fn expand_funcdef(&self, func: &mut FuncDef) -> Result<(), TypeError> {
        for arg in func.args.iter_mut() {
            arg.arg_type = self.expand_type(&arg.arg_type, false)?;
        }
        func.return_type = self.expand_type(&func.return_type, false)?;
        self.expand_expr(&mut func.body, false)?;
        for pre in func.preconditions.iter_mut() {
            self.expand_expr(pre, false)?;
        }
        for post in func.postconditions.iter_mut() {
            self.expand_expr(post, false)?;
        }
        Ok(())
    }
}

impl CallArg {
    pub fn to_expr(&self) -> Expr {
        match self {
            CallArg::Expr(e) => e.clone(),
            CallArg::MutVar { name, typ } => Expr::Variable {
                name: name.clone(),
                typ: Some(typ.as_ref().unwrap().skeleton(&[]).unwrap()),
            },
        }
    }
}

impl AssignOp {
    fn function_name(&self) -> &'static str {
        match self {
            AssignOp::Assign => "=",
            AssignOp::AddAssign => "+=",
            AssignOp::SubAssign => "-=",
            AssignOp::MulAssign => "*=",
        }
    }
}

impl Type {
    /// Strip out type constraints and just return the type that z3/hindley-milner can work with
    /// u32 -> int
    /// Vec<u32> -> Vec<int>
    /// (u32,u64,bool) -> (int,int,bool)
    /// etc.
    pub fn skeleton(&self, type_params: &[String]) -> Result<Type, TypeError> {
        match (self.name.as_str(), self.type_args.len()) {
            ("u8" | "u16" | "u32" | "u64" | "i8" | "i16" | "i32" | "i64" | "nat", 0) => {
                Ok(Type::basic("int"))
            }
            ("bool" | "int" | "str" | "void", 0) => Ok(self.clone()),
            ("Array", 2) => Ok(Type {
                name: "Vec".to_owned(),
                type_args: vec![self.type_args[0].skeleton(type_params)?],
            }),
            ("Vec", 1) | ("Tuple", _) | ("Lambda", _) => {
                let skel_args = self
                    .type_args
                    .iter()
                    .map(|arg| arg.skeleton(type_params))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Type {
                    name: self.name.clone(),
                    type_args: skel_args,
                })
            }
            _ => {
                if type_params.contains(&self.name) {
                    Ok(Type::basic(&self.name))
                } else {
                    Err(TypeError {
                        message: format!("Unknown type: {}", self.name),
                    })
                }
            }
        }
    }
}

impl TypeArg {
    fn skeleton(&self, type_params: &[String]) -> Result<TypeArg, TypeError> {
        match self {
            TypeArg::Type(typ) => Ok(TypeArg::Type(typ.skeleton(type_params)?)),
            TypeArg::Bound(b) => Ok(TypeArg::Bound(*b)),
        }
    }
}

impl FuncDef {
    fn skeleton(&self) -> Result<DeclaredFuncType, TypeError> {
        let skel_params = self
            .args
            .iter()
            .map(|p| p.arg_type.skeleton(&self.type_params))
            .collect::<Result<Vec<_>, _>>()?;
        let skel_ret_type = self.return_type.skeleton(&self.type_params)?;
        Ok(DeclaredFuncType {
            arg_types: skel_params,
            ret_type: skel_ret_type,
            type_params: self.type_params.clone(),
        })
    }
}

pub fn hindley_milner_infer(source_file: &mut SourceFile, verbosity: u8) -> Result<(), TypeError> {
    let mut type_vars = TypeVars::default();

    // Register builtin functions
    for builtin in all_builtins().values() {
        let declared_type = builtin.skeleton()?;
        type_vars
            .functions
            .insert(builtin.name.clone(), declared_type);
    }

    // First, register all function declarations
    for func in &source_file.functions {
        let declared_type = func.skeleton()?;
        type_vars.functions.insert(func.name.clone(), declared_type);
    }

    // Now infer types for each function body
    for func in &mut source_file.functions {
        if verbosity >= 1 {
            println!("HM inferring types for function {}", func.name);
        }
        let mut local_type_vars = type_vars.clone();
        local_type_vars.debug_func_name = func.name.clone();
        let funcdef = type_vars.functions.get(&func.name).unwrap().clone();
        assert!(funcdef.arg_types.len() == func.args.len());
        let mut env = HMEnv::default();
        for (param, arg) in funcdef.arg_types.iter().zip(&func.args) {
            env.vars.insert(arg.name.clone(), param.clone());
        }
        local_type_vars.infer_expr(&mut func.body, &env, Some(&funcdef.ret_type))?;

        // Infer types for expressions in preconditions and postconditions
        for pre in &mut func.preconditions {
            local_type_vars.infer_expr(pre, &env, Some(&Type::basic("bool")))?;
        }
        env.vars
            .insert(func.return_name.clone(), funcdef.ret_type.clone());
        for post in &mut func.postconditions {
            local_type_vars.infer_expr(post, &env, Some(&Type::basic("bool")))?;
        }

        local_type_vars.expand_funcdef(func)?;

        if verbosity >= 2 {
            println!("Inferred types for function {}:", func.name);
            for (var, typ) in &env.vars {
                println!("  {} : {}", var, typ);
            }
            // println!("Expansions:");
            // for (var, typ) in &local_type_vars.expansions {
            //     println!("  {} => {}", var, typ);
            // }
            println!("{}", func);
        }
    }

    Ok(())
}
