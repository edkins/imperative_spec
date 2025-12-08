use std::collections::HashMap;

use crate::{
    check::{ztype_ast::TExpr, ztype_inference::TypeError},
    syntax::ast::{Arg, Type},
};

// #[derive(Clone)]
// pub struct ParameterizedArg {
//     pub name: String,
//     pub typ: ParameterizedType,
// }

#[derive(Clone)]
pub struct TFunc {
    pub args: Vec<Arg>,
    pub return_type: Type,
    pub type_param_list: Vec<String>,
}

// #[derive(Clone)]
// pub struct TConcreteFunc {
//     pub arg_types: Vec<Type>,
//     pub return_type: Type,
// }

#[derive(Clone)]
pub struct Optimization {
    pub debug_name: String,
    pub arg_types: Vec<Type>,
    pub return_type: Type,
    pub preconditions: Vec<TExpr>,
}

// #[derive(Clone)]
// pub struct ConcreteOptimization {
//     pub debug_name: String,
//     pub func: TConcreteFunc,
// }

#[derive(Clone)]
pub struct TOverloadedFunc {
    pub headline: TFunc,
    pub optimizations: Vec<Optimization>,
    pub preconditions: Vec<TExpr>,
}

// #[derive(Clone)]
// pub struct TConcreteOverloadedFunc {
//     pub headline: TConcreteFunc,
//     pub optimizations: Vec<ConcreteOptimization>,
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
        type_param_list: &[String],
    ) -> Result<Vec<TExpr>, TypeError> {
        assert!(args.len() == exprs.len());
        let mut type_preconditions = vec![];
        for ((arg_type, expr), param_type) in args.iter().zip(exprs).zip(&self.arg_types) {
            if !arg_type.compatible_with(param_type) {
                return Err(TypeError {
                    message: format!(
                        "Cannot apply optimization {} due to incompatible argument types",
                        self.debug_name
                    ),
                });
            }
            type_preconditions
                .extend_from_slice(&param_type.type_assertions(expr.clone(), type_param_list)?);
        }
        Ok(type_preconditions)
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

impl TFunc {
    pub fn psimple(arg_types: &[Type], return_type: &Type, type_param_list: &[&str]) -> Self {
        let args = arg_types
            .iter()
            .enumerate()
            .map(|(i, t)| Arg {
                name: format!("arg{}", i),
                arg_type: t.clone(),
            })
            .collect::<Vec<Arg>>();
        TFunc {
            args,
            return_type: return_type.clone(),
            type_param_list: type_param_list.iter().map(|s| s.to_string()).collect(),
        }
    }
}

impl std::fmt::Display for TOverloadedFunc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "fn({}) -> {}",
            self.headline
                .args
                .iter()
                .map(|arg| arg.arg_type.to_string())
                .collect::<Vec<String>>()
                .join(", "),
            self.headline.return_type
        )
    }
}

impl TOverloadedFunc {
    pub fn simple(arg_types: &[Type], return_type: &Type) -> Self {
        TOverloadedFunc::psimple(arg_types, return_type, &[])
    }

    pub fn psimple(arg_types: &[Type], return_type: &Type, type_param_list: &[&str]) -> Self {
        TOverloadedFunc {
            headline: TFunc::psimple(arg_types, return_type, type_param_list),
            optimizations: vec![],
            preconditions: vec![],
        }
    }

    pub fn instantiate_from_types(&self, arg_types: &[Type]) -> Result<TOverloadedFunc, TypeError> {
        let headline = &self.headline;
        if headline.args.len() != arg_types.len() {
            return Err(TypeError {
                message: format!(
                    "Wrong number of arguments: expected {}, got {}",
                    headline.args.len(),
                    arg_types.len()
                ),
            });
        }
        let mut compatible = true;
        let mut mapping = HashMap::new();
        for (arg_type, arg) in arg_types.iter().zip(&headline.args) {
            arg.arg_type
                .unify(arg_type, &mut mapping, &headline.type_param_list)?;
        }
        for param in &headline.type_param_list {
            if !mapping.contains_key(param) {
                return Err(TypeError {
                    message: format!("Type parameter {} not mapped during unification", param),
                });
            }
        }
        for (arg_type, arg) in arg_types.iter().zip(&headline.args) {
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
                "No matching function overload found for given argument types {}",
                arg_types
                    .iter()
                    .map(|t| t.to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        })
    }

    pub fn instantiate(
        &self,
        mapping: &HashMap<String, Type>,
    ) -> Result<TOverloadedFunc, TypeError> {
        Ok(TOverloadedFunc {
            headline: TFunc {
                args: self
                    .headline
                    .args
                    .iter()
                    .map(|t| t.instantiate(mapping))
                    .collect::<Result<Vec<Arg>, TypeError>>()?,
                return_type: self.headline.return_type.instantiate(mapping)?,
                type_param_list: vec![],
            },
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
        })
    }

    pub fn extract_single(&self) -> Result<TFunc, TypeError> {
        if !self.headline.type_param_list.is_empty() {
            return Err(TypeError {
                message: "Cannot extract single function from parameterized overloaded function"
                    .to_owned(),
            });
        }
        Ok(TFunc {
            args: self.headline.args.clone(),
            return_type: self.headline.return_type.clone(),
            type_param_list: vec![],
        })
    }

    // pub fn lookup_return_type(&self, arg_types: &[Type]) -> Result<Type, TypeError> {
    //     let headline = &self.headline;
    //     if headline.arg_types.len() != arg_types.len() {
    //         return Err(TypeError {
    //             message: format!(
    //                 "Wrong number of arguments: expected {}, got {}",
    //                 headline.arg_types.len(),
    //                 arg_types.len()
    //             ),
    //         });
    //     }
    //     let mut compatible = true;
    //     let mut mapping = HashMap::new();
    //     for (arg_type, param_type) in arg_types.iter().zip(&headline.arg_types) {
    //         param_type.unify(arg_type, &mut mapping)?;
    //     }
    //     for (arg_type, param_type) in arg_types.iter().zip(&headline.arg_types) {
    //         if !arg_type.compatible_with(&param_type.instantiate(&mapping)?) {
    //             compatible = false;
    //             break;
    //         }
    //     }
    //     if compatible {
    //         return headline.return_type.instantiate(&mapping);
    //     }
    //     Err(TypeError {
    //         message: format!(
    //             "No matching function overload found for given argument types {}",
    //             arg_types
    //                 .iter()
    //                 .map(|t| t.to_string())
    //                 .collect::<Vec<String>>()
    //                 .join(", ")
    //         ),
    //     })
    // }
}

impl TOverloadedFunc {
    pub fn lookup_type_preconditions(&self, args: &[TExpr]) -> Result<Vec<TExpr>, TypeError> {
        let headline = &self.headline;
        if headline.args.len() != args.len() {
            return Err(TypeError {
                message: format!(
                    "Wrong number of arguments: expected {}, got {}",
                    headline.args.len(),
                    args.len()
                ),
            });
        }
        let mut compatible = true;
        let mut type_preconditions = vec![];
        for (arg, param) in args.iter().zip(&headline.args) {
            if !arg.typ().compatible_with(&param.arg_type) {
                compatible = false;
                break;
            }
            type_preconditions.extend_from_slice(
                &param
                    .arg_type
                    .type_assertions(arg.clone(), &headline.type_param_list)?,
            );
        }
        if compatible {
            return Ok(type_preconditions);
        }
        Err(TypeError {
            message: format!(
                "No matching function overload found for given argument types {}",
                args.iter()
                    .map(|t| t.typ().to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        })
    }
}
