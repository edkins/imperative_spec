use std::collections::HashMap;

use crate::{check::{builtins::all_builtins, ztype_ast::TFuncDef, ztype_inference::TypeError}, syntax::ast::{AssignOp, Expr, FuncDef, SourceFile, Stmt, Type, TypeArg}};

#[derive(Clone)]
struct DeclaredFuncType {
    arg_types: Vec<Type>,
    ret_type: Type,
    type_params: Vec<String>,
}

#[derive(Clone)]
struct TypeVars {
    debug_func_name: String,
    counter: usize,
    expansions: HashMap<String, Type>,
    vars: HashMap<String, Type>,
    functions: HashMap<String, DeclaredFuncType>,
}

#[derive(Clone, Default)]
struct TypeParamLookup(HashMap<String, Type>);

impl TypeParamLookup {
    fn translate_type_arg(&self, arg: &TypeArg) -> Result<TypeArg, TypeError> {
        match arg {
            TypeArg::Type(typ) => {
                Ok(TypeArg::Type(self.translate_type(typ)?))
            }
            TypeArg::Bound(b) => Ok(TypeArg::Bound(*b))
        }
    }

    fn translate_type(&self, typ: &Type) -> Result<Type, TypeError> {
        if let Some(t) = self.0.get(&typ.name) {
            if !t.type_args.is_empty() {
                return Err(TypeError{message: format!("Type parameter {} cannot have type arguments", typ.name)});
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

impl TypeVars {
    fn fresh_type_var(&mut self) -> String {
        let var_name = format!("'{}", self.counter);
        self.counter += 1;
        var_name
    }

    fn unify(&mut self, t0: &Type, t1: &Type) -> Result<(), TypeError> {
        if t0 == t1 {
            return Ok(());
        }
        if t0.is_type_var() {
            if t1.occurs_check(&t0.name) {
                return Err(TypeError{message: format!("Occurs check failed for type variable {}", t0.name)});
            }
            self.expansions.insert(t0.name.clone(), t1.clone());
            return Ok(());
        }
        if t1.is_type_var() {
            if t0.occurs_check(&t1.name) {
                return Err(TypeError{message: format!("Occurs check failed for type variable {}", t1.name)});
            }
            self.expansions.insert(t1.name.clone(), t0.clone());
            return Ok(());
        }
        if t0.name != t1.name || t0.type_args.len() != t1.type_args.len() {
            return Err(TypeError{message: format!("Cannot unify types {} and {}", t0.name, t1.name)});
        }
        for (arg0, arg1) in t0.type_args.iter().zip(&t1.type_args) {
            match (arg0, arg1) {
                (TypeArg::Type(ta0), TypeArg::Type(ta1)) => {
                    self.unify(ta0, ta1)?;
                }
                (TypeArg::Bound(b0), TypeArg::Bound(b1)) => {
                    if b0 != b1 {
                        return Err(TypeError{message: format!("Cannot unify bound type arguments {} and {}", b0, b1)});
                    }
                }
                _ => {
                    return Err(TypeError{message: format!("Cannot unify type arguments {} and {}", arg0, arg1)});
                }
            }
        }
        Ok(())
    }

    fn generalize_function(&mut self, func: &DeclaredFuncType) -> Result<FunctionGeneralizationResult, TypeError> {
        // Generate type variables for each type param
        let mut type_param_lookup = TypeParamLookup::default();
        for param in &func.type_params {
            let var_name = self.fresh_type_var();
            type_param_lookup.0.insert(param.clone(), Type::basic(&var_name));
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

    fn infer_expr(&mut self, expr: &mut Expr, expected: Option<&Type>) -> Result<Type, TypeError> {
        let actual_type = match expr {
            Expr::Literal(literal) => {literal.typ()}
            Expr::Variable { name, typ } => {
                assert!(typ.is_none());
                if let Some(t) = self.vars.get(name) {
                    *typ = Some(t.clone());
                    t.clone()
                } else {
                    return Err(TypeError{message: format!("Unknown variable: {} in function {}", name, self.debug_func_name)});
                }
            }
            Expr::Semicolon(stmt, expr) => {
                self.infer_stmt(stmt)?;
                self.infer_expr(expr, expected)?
            }
            Expr::FunctionCall { name, args, type_instantiations } => {
                assert!(type_instantiations.is_empty());
                if let Some(func_type) = self.functions.get(name).cloned() {
                    if func_type.arg_types.len() != args.len() {
                        return Err(TypeError{message: format!("Function {} expects {} arguments, got {}", name, func_type.arg_types.len(), args.len())});
                    }
                    let gen_result = self.generalize_function(&func_type)?;
                    for (arg, expected_type) in args.iter_mut().zip(gen_result.arg_types.iter()) {
                        self.infer_expr(arg, Some(expected_type))?;
                    }
                    gen_result.ret_type
                } else {
                    return Err(TypeError{message: format!("Unknown function: {}", name)});
                }
            }
            Expr::RoundSequence { elems } => {
                let mut type_args = vec![];
                for elem in elems.iter_mut() {
                    type_args.push(TypeArg::Type(self.infer_expr(elem, None)?));
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
                    self.infer_expr(elem, Some(&Type::basic(&tvar)))?;
                }
                Type {
                    name: "Vec".to_owned(),
                    type_args: vec![TypeArg::Type(Type::basic(&tvar))],
                }
            }
        };

        if let Some(expected_type) = expected {
            self.unify(&actual_type, expected_type)?;
        }
        Ok(actual_type)
    }

    fn infer_stmt(&mut self, stmt: &mut Stmt) -> Result<(), TypeError> {
        match stmt {
            Stmt::Expr(expr) => {
                self.infer_expr(expr, None)?;
                Ok(())
            }
            Stmt::Let { name, typ, value, .. } => {
                let styp = typ.as_ref().map(|t| t.skeleton(&[])).transpose()?;
                let inferred = self.infer_expr(value, styp.as_ref())?;
                self.vars.insert(name.clone(), inferred);
                Ok(())
            }
            Stmt::Assign { name, op, value } => {
                *stmt = Stmt::Expr(
                    Expr::FunctionCall {
                        name: op.function_name().to_owned(),
                        args: vec![
                            Expr::Variable { name: name.clone(), typ: None },
                            value.clone(),
                        ],
                        type_instantiations: vec![],
                    }
                );
                self.infer_stmt(stmt)
            }
        }
    }
}

impl AssignOp {
    fn function_name(&self) -> &'static str {
        match self {
            AssignOp::Assign => "assign",
            AssignOp::AddAssign => "add_assign",
            AssignOp::SubAssign => "sub_assign",
            AssignOp::MulAssign => "mul_assign",
        }
    }
}

impl Type {
    /// Strip out type constraints and just return the type that z3/hindley-milner can work with
    /// u32 -> int
    /// Vec<u32> -> Vec<int>
    /// (u32,u64,bool) -> (int,int,bool)
    /// etc.
    fn skeleton(&self, type_params: &[String]) -> Result<Type, TypeError> {
        match (self.name.as_str(), self.type_args.len()) {
            ("u8" | "u16" | "u32" | "u64" | "i8" | "i16" | "i32" | "i64" | "nat", 0) => Ok(Type::basic("int")),
            ("bool" | "int" | "str" | "void", 0) => Ok(self.clone()),
            ("Array", 2) => {
                Ok(Type {
                    name: "Vec".to_owned(),
                    type_args: vec![self.type_args[0].skeleton(type_params)?],
                })
            }
            ("Vec",1) | ("Tuple", _) | ("Lambda", _) => {
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
                    Err(TypeError{message: format!("Unknown type: {}", self.name)})
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

impl TFuncDef {
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
    let mut type_vars = TypeVars {
        debug_func_name: "".to_owned(),
        counter: 0,
        expansions: HashMap::new(),
        vars: HashMap::new(),
        functions: HashMap::new(),
    };

    // Register builtin functions
    for builtin in all_builtins().values() {
        let declared_type = builtin.skeleton()?;
        type_vars.functions.insert(builtin.name.clone(), declared_type);
    }

    // First, register all function declarations
    for func in &source_file.functions {
        let declared_type = func.skeleton()?;
        type_vars.functions.insert(func.name.clone(), declared_type);
    }

    // Now infer types for each function body
    for func in &mut source_file.functions.clone() {
        let mut local_type_vars = type_vars.clone();
        local_type_vars.debug_func_name = func.name.clone();
        let funcdef = type_vars.functions.get(&func.name).unwrap().clone();
        assert!(funcdef.arg_types.len() == func.args.len());
        for (param, arg) in funcdef.arg_types.iter().zip(&func.args) {
            local_type_vars.vars.insert(arg.name.clone(), param.clone());
        }
        local_type_vars.infer_expr(&mut func.body, Some(&funcdef.ret_type))?;
        if verbosity >= 2 {
            println!("Inferred types for function {}:", func.name);
            for (var, typ) in &local_type_vars.vars {
                println!("  {} : {}", var, typ);
            }
        }
    }

    Ok(())
}