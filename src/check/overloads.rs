use std::collections::HashMap;

use crate::{
    check::{
        parameterized::{ParameterizedType, ParameterizedTypeArg},
        ztype_ast::TExpr,
        ztype_inference::TypeError,
    },
    syntax::ast::{Bound, Type, TypeArg},
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
pub struct TOptimizedFunc {
    pub headline: TFunc,
    pub optimizations: Vec<TFunc>,
}

#[derive(Clone)]
pub struct TOverloadedFunc(pub Vec<TOptimizedFunc>);

// impl TFunc {
//     fn new(args_types: &[ParameterizedType], return_type: &ParameterizedType) -> Self {
//         TFunc {
//             arg_types: args_types.to_vec(),
//             return_type: return_type.clone(),
//         }
//     }
// }

impl TOverloadedFunc {
    pub fn simple(arg_types: &[Type], return_type: &Type) -> Self {
        let arg_types = arg_types
            .iter()
            .map(|t| ParameterizedType::from_type(t))
            .collect::<Vec<ParameterizedType>>();
        let return_type = ParameterizedType::from_type(return_type);
        TOverloadedFunc(vec![TOptimizedFunc {
            headline: TFunc {
                arg_types,
                return_type,
            },
            optimizations: vec![],
        }])
    }

    pub fn psimple(arg_types: &[ParameterizedType], return_type: &ParameterizedType) -> Self {
        TOverloadedFunc(vec![TOptimizedFunc {
            headline: TFunc {
                arg_types: arg_types.to_vec(),
                return_type: return_type.clone(),
            },
            optimizations: vec![],
        }])
    }
}

impl TOverloadedFunc {
    pub fn extract_single(&self) -> Result<TConcreteFunc, TypeError> {
        Ok(TConcreteFunc {
            arg_types: self.0[0]
                .headline
                .arg_types
                .iter()
                .map(|t| t.to_type())
                .collect::<Result<Vec<Type>, TypeError>>()?,
            return_type: self.0[0].headline.return_type.to_type()?,
        })
    }

    pub fn lookup_return_type(&self, arg_types: &[Type]) -> Result<Type, TypeError> {
        for optimized_func in &self.0 {
            let headline = &optimized_func.headline;
            if headline.arg_types.len() != arg_types.len() {
                continue;
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
                return Ok(headline.return_type.instantiate(&mapping)?);
            }
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
        for optimized_func in &self.0 {
            let headline = &optimized_func.headline;
            if headline.arg_types.len() != args.len() {
                continue;
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

    // fn mk_function_call(&self, name: &str, args: &[TExpr]) -> Result<TExpr, TypeError> {
    //     match self {
    //         TOverloadedFunc::Single{headline, ..} => {
    //             if headline.arg_types.len() != args.len() {
    //                 return Err(TypeError {
    //                     message: format!(
    //                         "Function {} expects {} arguments, got {}",
    //                         name,
    //                         headline.arg_types.len(),
    //                         args.len()
    //                     ),
    //                 });
    //             }
    //             let mut compatible = true;
    //             for (arg_type, param_type) in args.iter().zip(&headline.arg_types) {
    //                 if !arg_type.typ().compatible_with(param_type) {
    //                     compatible = false;
    //                     break;
    //                 }
    //             }
    //             if compatible {
    //                 let coerced_args = args
    //                     .iter()
    //                     .zip(&headline.arg_types)
    //                     .map(|(arg, param_type)| arg.coerce(param_type))
    //                     .collect::<Result<Vec<TExpr>, TypeError>>()?;
    //                 return Ok(TExpr::FunctionCall {
    //                     name: name.to_owned(),
    //                     args: coerced_args,
    //                     return_type: headline.return_type.clone(),
    //                 });
    //             }
    //             Err(TypeError {
    //                 message: format!(
    //                     "No matching function overload found for {} with given argument types {}",
    //                     name,
    //                     display_texprs(args)
    //                 ),
    //             })
    //         }
    //         TOverloadedFunc::Equality => {
    //             if args.len() != 2 {
    //                 return Err(TypeError {
    //                     message: "Equality function requires exactly 2 arguments".to_owned(),
    //                 });
    //             }
    //             let eqt = args[0].typ().find_equality_type(&args[1].typ())?;
    //             let arg0 = args[0].coerce(&eqt)?;
    //             let arg1 = args[1].coerce(&eqt)?;
    //             Ok(TExpr::FunctionCall {
    //                 name: name.to_owned(),
    //                 args: vec![arg0, arg1],
    //                 return_type: Type::basic("bool"),
    //             })
    //         }
    //     }
    // }
}
