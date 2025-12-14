use std::collections::HashMap;

use crate::{
    check::{builtins::all_builtins, types::TypeError},
    syntax::ast::{Expr, ExprKind, FuncDef, Literal, SourceFile, Type, TypeArg},
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
        if let Expr::Expr{kind:ExprKind::Literal{literal}, ..} = self {
            match literal {
                Literal::U64(u) => Ok(*u),
                Literal::I64(i) if *i >= 0 => Ok(*i as u64),
                _ => Err(TypeError {
                    message: format!("Expected u64 literal, got {}", literal),
                }),
            }
        } else {
            Err(TypeError {
                message: format!("Expected literal expression, got {}", self),
            })
        }
    }
}

/// May include type vars '0 etc.
struct Signature {
    arg_types: Vec<Type>,
    ret_type: Type,
}

impl ExprKind {
    fn set_type_instantiations(&mut self, type_instantiations: &[Type]) {
        match self {
            ExprKind::Function {
                type_instantiations: ti,
                ..
            } => {
                assert!(ti.is_empty());
                *ti = type_instantiations.to_vec();
            }
            _ => {}
        }
    }
}

impl Expr {
    pub fn type_mut(&mut self) -> &mut Option<Type> {
        match self {
            Expr::Variable { info, .. } => &mut info.typ,
            Expr::Expr { info, .. } => &mut info.typ,
            Expr::Lambda { info, .. } => &mut info.typ,
            Expr::Let { info, .. } => &mut info.typ,
        }
    }
}

impl TypeVars {
    fn fresh_type_var(&mut self) -> String {
        let var_name = format!("'{}", self.counter);
        self.counter += 1;
        var_name
    }

    fn fresh_type_var_wrapped(&mut self) -> Type {
        Type::basic(&self.fresh_type_var())
    }

    fn fresh_type_vars_wrapped(&mut self, n: usize) -> Vec<Type> {
        (0..n).map(|_| self.fresh_type_var_wrapped()).collect()
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
    ) -> Result<(Signature, Vec<Type>), TypeError> {
        // Generate type variables for each type param
        let type_vars = self.fresh_type_vars_wrapped(func.type_params.len());

        let mut arg_types = vec![];
        for arg_type in &func.arg_types {
            arg_types.push(arg_type.instantiate(&func.type_params, &type_vars)?);
        }
        Ok((Signature {
            arg_types,
            ret_type: func.ret_type.instantiate(&func.type_params, &type_vars)?,
        }, type_vars))
    }

    fn infer_expr(
        &mut self,
        expr: &mut Expr,
        env: &HMEnv,
        expected: Option<&Type>,
    ) -> Result<Type, TypeError> {
        let actual_type = match expr {
            Expr::Variable { name, .. } => {
                if let Some(t) = env.vars.get(name) {
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
            Expr::Expr {
                kind,
                args,
                ..
            } => {
                let arg_types = args
                    .iter_mut()
                    .map(|arg| self.infer_expr(arg, env, None))
                    .collect::<Result<Vec<_>, _>>()?;
                self.sort_out_seq_at(kind, args, &arg_types)?;
                let sig = self.signature(kind)?;  // also sets type instantiations for functions
                if sig.arg_types.len() != arg_types.len() {
                    return Err(TypeError {
                        message: format!(
                            "Expression expected {} arguments, got {}",
                            sig.arg_types.len(),
                            arg_types.len()
                        ),
                    });
                }
                for (actual, expected) in arg_types.iter().zip(&sig.arg_types) {
                    self.unify(actual, expected)?;
                }
                sig.ret_type
            }
            Expr::Let { name, mutable, typ, value, body, .. } => {
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
                self.infer_expr(body, &new_env, expected)?
            }
            Expr::Lambda { args, body, .. } => {
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
        };

        let typ_mut = expr.type_mut();
        assert!(typ_mut.is_none());
        typ_mut.replace(actual_type.clone());
        if let Some(expected_type) = expected {
            // println!("For expression {}, unifying actual type {} with expected type {}", expr, actual_type, expected_type);
            self.unify(&actual_type, expected_type)?;
        }
        Ok(actual_type)
    }

    fn sort_out_seq_at(&self, kind: &mut ExprKind, args: &[Expr], arg_types: &[Type]) -> Result<(), TypeError> {
        if matches!(kind, ExprKind::UnknownSequenceAt)
        {
            assert!(arg_types.len() == 2);
            assert!(args.len() == 2);
            let seq_type = self.expand_type(&arg_types[0], true).unwrap();
            if seq_type.is_round_seq() {
                let index = args[1].as_literal_u64()? as usize;
                *kind = ExprKind::TupleAt {
                    len: seq_type.get_round_seq_length().unwrap() as usize,
                    index,
                };
            } else if seq_type.is_square_seq() {
                *kind = ExprKind::Function {
                    name: "seq_at".to_owned(),
                    type_instantiations: vec![seq_type.get_uniform_square_elem_type().unwrap().clone()],
                    mutable_args: vec![false,false]
                };
            } else {
                return Err(TypeError {
                    message: format!("Type {} is not a known sequence type", seq_type),
                });
            }
        }
        Ok(())
    }

    fn signature(&mut self, kind: &mut ExprKind) -> Result<Signature, TypeError> {
        match kind {
            ExprKind::Function {
                name,
                type_instantiations,
                ..
            } => {
                if let Some(func_def) = self.functions.get(name).cloned() {
                    let (sig, instantiations) = self.generalize_function(&func_def)?;
                    *type_instantiations = instantiations;
                    Ok(sig)
                } else {
                    Err(TypeError {
                        message: format!("Unknown function: {}", name),
                    })
                }
            },
            ExprKind::Literal { literal } => {
                Ok(Signature {
                    arg_types: vec![],
                    ret_type: literal.typ(),
                })
            },
            ExprKind::SquareSequence { len } => {
                let tvar = self.fresh_type_var_wrapped();
                Ok(Signature {
                    arg_types: vec![tvar.clone(); *len],
                    ret_type: tvar.vec(),
                })
            }
            ExprKind::RoundSequence { len } => {
                let tvars = self.fresh_type_vars_wrapped(*len);
                Ok(Signature {
                    arg_types: tvars.clone(),
                    ret_type: Type::tuple(&tvars),
                })
            }
            ExprKind::TupleAt { len, index } => {
                assert!(index < len);
                let tvars = self.fresh_type_vars_wrapped(*len);
                Ok(Signature {
                    arg_types: vec![Type::tuple(&tvars)],
                    ret_type: tvars[*index].clone(),
                })
            }
            ExprKind::UnknownSequenceAt => unreachable!(),
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

    fn expand_expr(&self, expr: &mut Expr, allow_unbound: bool) -> Result<(), TypeError> {
        let new_type = self.expand_type(&expr.typ(), allow_unbound)?;
        *expr.type_mut() = Some(new_type);
        match expr {
            Expr::Expr { kind, args, .. } => {
                if let ExprKind::Function { type_instantiations, .. } = kind {
                    for t in type_instantiations.iter_mut() {
                        *t = self.expand_type(t, allow_unbound)?;
                    }
                }
                for arg in args.iter_mut() {
                    self.expand_expr(arg, allow_unbound)?;
                }
                Ok(())
            }
            Expr::Lambda { args, body, .. } => {
                for arg in args.iter_mut() {
                    arg.arg_type = self.expand_type(&arg.arg_type, allow_unbound)?;
                }
                self.expand_expr(body, allow_unbound)
            }
            Expr::Let { typ, value, body, .. } => {
                if let Some(t) = typ {
                    *t = self.expand_type(t, allow_unbound)?;
                }
                self.expand_expr(value, allow_unbound)?;
                self.expand_expr(body, allow_unbound)
            }
            Expr::Variable { .. } => Ok(())
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
