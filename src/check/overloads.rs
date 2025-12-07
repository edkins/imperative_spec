use std::collections::HashMap;

use crate::{
    check::{parameterized::ParameterizedType, ztype_ast::TExpr, ztype_inference::TypeError},
    syntax::ast::Type,
};

#[derive(Clone)]
pub struct TFunc {
    pub arg_types: Vec<ParameterizedType>,
    pub return_type: ParameterizedType,
}

#[derive(Clone)]
pub struct TConcreteFunc {
    pub arg_types: Vec<Type>,
    pub return_type: Type,
}

#[derive(Clone)]
pub struct Optimization {
    pub debug_name: String,
    pub func: TFunc,
}

#[derive(Clone)]
pub struct TOverloadedFunc {
    pub headline: TFunc,
    pub optimizations: Vec<Optimization>,
}

impl TOverloadedFunc {
    pub fn simple(arg_types: &[Type], return_type: &Type) -> Self {
        let arg_types = arg_types
            .iter()
            .map(ParameterizedType::from_type)
            .collect::<Vec<ParameterizedType>>();
        let return_type = ParameterizedType::from_type(return_type);
        TOverloadedFunc {
            headline: TFunc {
                arg_types,
                return_type,
            },
            optimizations: vec![],
        }
    }

    pub fn psimple(arg_types: &[ParameterizedType], return_type: &ParameterizedType) -> Self {
        TOverloadedFunc {
            headline: TFunc {
                arg_types: arg_types.to_vec(),
                return_type: return_type.clone(),
            },
            optimizations: vec![],
        }
    }
}

impl TOverloadedFunc {
    pub fn extract_single(&self) -> Result<TConcreteFunc, TypeError> {
        Ok(TConcreteFunc {
            arg_types: self.headline
                .arg_types
                .iter()
                .map(|t| t.to_type())
                .collect::<Result<Vec<Type>, TypeError>>()?,
            return_type: self.headline.return_type.to_type()?,
        })
    }

    pub fn lookup_return_type(&self, arg_types: &[Type]) -> Result<Type, TypeError> {
        let headline = &self.headline;
        if headline.arg_types.len() != arg_types.len() {
            return Err(TypeError {
                message: format!(
                    "Wrong number of arguments: expected {}, got {}",
                    headline.arg_types.len(),
                    arg_types.len()
                ),
            });
        }
        let mut compatible = true;
        let mut mapping = HashMap::new();
        for (arg_type, param_type) in arg_types.iter().zip(&headline.arg_types) {
            param_type.unify(arg_type, &mut mapping)?;
        }
        for (arg_type, param_type) in arg_types.iter().zip(&headline.arg_types) {
            if !arg_type.compatible_with(&param_type.instantiate(&mapping)?) {
                compatible = false;
                break;
            }
        }
        if compatible {
            return headline.return_type.instantiate(&mapping);
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

    pub fn lookup_type_preconditions(&self, args: &[TExpr]) -> Result<Vec<TExpr>, TypeError> {
        let headline = &self.headline;
        if headline.arg_types.len() != args.len() {
            return Err(TypeError {
                message: format!(
                    "Wrong number of arguments: expected {}, got {}",
                    headline.arg_types.len(),
                    args.len()
                ),
            });
        }
        let mut compatible = true;
        let mut mapping = HashMap::new();
        for (arg, param_type) in args.iter().zip(&headline.arg_types) {
            param_type.unify(&arg.typ(), &mut mapping)?;
        }
        let mut type_preconditions = vec![];
        for (arg, param_type) in args.iter().zip(&headline.arg_types) {
            let instantiated = param_type.instantiate(&mapping)?;
            if !arg.typ().compatible_with(&instantiated) {
                compatible = false;
                break;
            }
            type_preconditions.extend_from_slice(&instantiated.type_assertions(arg.clone())?);
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
