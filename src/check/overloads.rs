use std::collections::HashMap;

use crate::{
    check::{
        ztype_inference::TypeError,
    },
    syntax::ast::{Arg, Type},
};

// #[derive(Clone)]
// pub struct ParameterizedArg {
//     pub name: String,
//     pub typ: ParameterizedType,
// }

// #[derive(Clone)]
// pub struct TFunc {
//     pub args: Vec<Arg>,
//     pub return_type: Type,
//     pub type_param_list: Vec<String>,
// }

#[derive(Clone)]
pub struct Optimization {
    pub debug_name: String,
    pub arg_types: Vec<Type>,
    pub return_type: Type,
    pub preconditions: Vec<TExpr>,
}

// #[derive(Clone)]
// pub struct TOverloadedFunc {
//     pub headline: TFunc,
//     pub optimizations: Vec<Optimization>,
//     pub preconditions: Vec<TExpr>,
// }

impl std::fmt::Display for Optimization {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: ({}) -> {}",
            self.debug_name,
            self.arg_types
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.return_type
        )
    }
}

impl Optimization {
    pub fn assumptions_when_applying(
        &self,
        args: &[Type],
        exprs: &[TExpr],
    ) -> Result<Vec<TExpr>, TypeError> {
        assert!(args.len() == exprs.len());
        let mut preconditions = self.preconditions.clone();
        for ((arg_type, expr), param_type) in args.iter().zip(exprs).zip(&self.arg_types) {
            if !arg_type.compatible_with(param_type) {
                return Err(TypeError {
                    message: format!(
                        "Cannot apply optimization {} due to incompatible argument types",
                        self.debug_name
                    ),
                });
            }
            preconditions.extend_from_slice(&param_type.type_assertions(expr.clone(), &[])?);
        }
        Ok(preconditions)
    }

    pub fn instantiate(&self, mapping: &HashMap<String, Type>) -> Result<Optimization, TypeError> {
        Ok(Optimization {
            debug_name: self.debug_name.clone(),
            arg_types: self
                .arg_types
                .iter()
                .map(|t| t.instantiate(mapping))
                .collect::<Result<Vec<Type>, TypeError>>()?,
            return_type: self.return_type.instantiate(mapping)?,
            preconditions: self
                .preconditions
                .iter()
                .map(|e| e.instantiate(mapping))
                .collect::<Result<Vec<TExpr>, TypeError>>()?,
        })
    }
}

// impl std::fmt::Display for TFunc {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         write!(
//             f,
//             "fn({}) -> {}",
//             self.headline
//                 .args
//                 .iter()
//                 .map(|arg| arg.arg_type.to_string())
//                 .collect::<Vec<String>>()
//                 .join(", "),
//             self.headline.return_type
//         )
//     }
// }

impl TFuncDef {
    pub fn simple(name: &str, arg_types: &[Type], return_type: &Type) -> Self {
        TFuncDef::psimple(name, arg_types, return_type, &[])
    }

    pub fn psimple(
        name: &str,
        arg_types: &[Type],
        return_type: &Type,
        type_param_list: &[&str],
    ) -> Self {
        TFuncDef {
            attributes: vec![],
            name: name.to_owned(),
            return_name: "__ret__".to_owned(),
            return_type: return_type.clone(),
            args: arg_types
                .iter()
                .enumerate()
                .map(|(i, t)| Arg {
                    name: format!("arg{}", i),
                    mutable: false,
                    arg_type: t.clone(),
                })
                .collect::<Vec<Arg>>(),
            optimizations: vec![],
            preconditions: vec![],
            postconditions: vec![],
            body: None,
            type_params: type_param_list.iter().map(|s| s.to_string()).collect(),
        }
    }

    pub fn instantiate_from_types(&self, arg_types: &[Type]) -> Result<TFuncDef, TypeError> {
        if self.args.len() != arg_types.len() {
            return Err(TypeError {
                message: format!(
                    "Wrong number of arguments: expected {}, got {}",
                    self.args.len(),
                    arg_types.len()
                ),
            });
        }
        let mut compatible = true;
        let mut mapping = HashMap::new();
        for (arg_type, arg) in arg_types.iter().zip(&self.args) {
            arg.arg_type
                .unify(arg_type, &mut mapping, &self.type_params).map_err(|e|e.with_context(&format!("... for function {}", self.name)))?;
        }
        for param in &self.type_params {
            if !mapping.contains_key(param) {
                return Err(TypeError {
                    message: format!("Type parameter {} not mapped during unification", param),
                });
            }
        }
        for (arg_type, arg) in arg_types.iter().zip(&self.args) {
            if !arg_type.compatible_with(&arg.arg_type.instantiate(&mapping)?) {
                compatible = false;
                break;
            }
        }
        if compatible {
            return self.instantiate(&mapping);
        }
        Err(TypeError {
            message: format!(
                "instantiate_from_types: No matching function overload found for {} given argument types {}",
                self.name,
                arg_types
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        })
    }

    pub fn instantiate(&self, mapping: &HashMap<String, Type>) -> Result<TFuncDef, TypeError> {
        Ok(TFuncDef {
            args: self
                .args
                .iter()
                .map(|t| t.instantiate(mapping))
                .collect::<Result<Vec<Arg>, TypeError>>()?,
            return_type: self.return_type.instantiate(mapping)?,
            type_params: vec![],
            optimizations: self
                .optimizations
                .iter()
                .map(|opt| opt.instantiate(mapping))
                .collect::<Result<Vec<Optimization>, TypeError>>()?,
            preconditions: self
                .preconditions
                .iter()
                .map(|e| e.instantiate(mapping))
                .collect::<Result<Vec<TExpr>, TypeError>>()?,
            attributes: self.attributes.clone(),
            name: self.name.clone(),
            return_name: self.return_name.clone(),
            postconditions: self
                .postconditions
                .iter()
                .map(|e| e.instantiate(mapping))
                .collect::<Result<Vec<TExpr>, TypeError>>()?,
            body: self
                .body
                .as_ref()
                .map(|b| b.instantiate(mapping))
                .transpose()?,
        })
    }
}
