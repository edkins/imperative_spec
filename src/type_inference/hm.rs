use std::collections::HashMap;

use crate::{check::ztype_inference::TypeError, syntax::ast::{Expr, Stmt, Type, TypeArg}};

#[derive(Clone)]
struct DeclaredFuncType {
    arg_types: Vec<Type>,
    ret_type: Type,
    type_params: Vec<String>,
}

struct TypeVars {
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

impl TypeVars {
    fn fresh_type_var(&mut self) -> String {
        let var_name = format!("'{}", self.counter);
        self.counter += 1;
        var_name
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
                    return Err(TypeError{message: format!("Unknown variable: {}", name)});
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
            // Here we would check that expr's inferred type matches expected_type
        }
        Ok(actual_type)
    }

    fn infer_stmt(&mut self, stmt: &mut Stmt) -> Result<(), TypeError> {
        match stmt {
            Stmt::Expr(expr) => {
                self.infer_expr(expr, None)?;
                Ok(())
            }
            Stmt::Let { name, mutable, typ, value } => {
                let styp = typ.as_ref().map(|t| t.skeleton()).transpose()?;
                let inferred = self.infer_expr(value, styp.as_ref())?;
                self.vars.insert(name.clone(), inferred);
                Ok(())
            }
            Stmt::Assign { name, op: _, value } => {
                let inferred = self.infer_expr(value, None)?;
                if let Some(var_type) = self.vars.get(name) {
                    // Here we would check that value's type matches var_type
                    Ok(())
                } else {
                    Err(TypeError{message: format!("Unknown variable: {}", name)})
                }
            }
        }
    }
}

impl Type {
    /// Strip out type constraints and just return the type that z3/hindley-milner can work with
    /// u32 -> int
    /// Vec<u32> -> Vec<int>
    /// (u32,u64,bool) -> (int,int,bool)
    /// etc.
    fn skeleton(&self) -> Result<Type, TypeError> {
        match self.name.as_str() {
            "u8" | "u16" | "u32" | "u64" | "i8" | "i16" | "i32" | "i64" | "nat" => Ok(Type::basic("int")),
            "bool" | "int" | "str" | "void" => Ok(self.clone()),
            "Vec" | "Array" | "Tuple" => {
                let skel_args = self
                    .type_args
                    .iter()
                    .map(|arg| arg.skeleton())
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Type {
                    name: self.name.clone(),
                    type_args: skel_args,
                })
            }
            _ => Err(TypeError{message: format!("Unknown type: {}", self.name)}),
        }
    }
}

impl TypeArg {
    fn skeleton(&self) -> Result<TypeArg, TypeError> {
        match self {
            TypeArg::Type(typ) => Ok(TypeArg::Type(typ.skeleton()?)),
            TypeArg::Bound(b) => Ok(TypeArg::Bound(*b)),
        }
    }
}
