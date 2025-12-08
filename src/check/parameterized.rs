use std::collections::HashMap;

use crate::{
    check::{
        ztype_ast::{TExpr, TStmt},
        ztype_inference::TypeError,
    },
    syntax::ast::{Arg, Type, TypeArg},
};

// #[derive(Clone)]
// pub enum ParameterizedType {
//     Param(String),
//     Named(String, Vec<ParameterizedTypeArg>),
// }

// #[derive(Clone)]
// pub enum ParameterizedTypeArg {
//     Type(ParameterizedType),
//     Bound(Bound),
// }

// impl std::fmt::Display for ParameterizedType {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             ParameterizedType::Param(name) => write!(f, "{}", name),
//             ParameterizedType::Named(name, params) => {
//                 if params.is_empty() {
//                     write!(f, "{}", name)
//                 } else {
//                     let params_str = params
//                         .iter()
//                         .map(|p| format!("{}", p))
//                         .collect::<Vec<String>>()
//                         .join(", ");
//                     write!(f, "{}<{}>", name, params_str)
//                 }
//             }
//         }
//     }
// }

// impl std::fmt::Display for ParameterizedTypeArg {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             ParameterizedTypeArg::Type(t) => write!(f, "{}", t),
//             ParameterizedTypeArg::Bound(b) => write!(f, "{}", b),
//         }
//     }
// }

// impl ParameterizedTypeArg {
//     pub fn to_type(&self) -> Result<TypeArg, TypeError> {
//         match self {
//             ParameterizedTypeArg::Bound(b) => Ok(TypeArg::Bound(*b)),
//             ParameterizedTypeArg::Type(t) => Ok(TypeArg::Type(t.to_type()?)),
//         }
//     }

//     pub fn from_type(type_arg: &TypeArg) -> Self {
//         match type_arg {
//             TypeArg::Bound(b) => ParameterizedTypeArg::Bound(*b),
//             TypeArg::Type(t) => ParameterizedTypeArg::Type(ParameterizedType::from_type(t)),
//         }
//     }

//     pub fn most_general(&self) -> Result<Self, TypeError> {
//         match self {
//             ParameterizedTypeArg::Bound(b) => Ok(ParameterizedTypeArg::Bound(*b)),
//             ParameterizedTypeArg::Type(t) => {
//                 let general_type = t.most_general()?;
//                 Ok(ParameterizedTypeArg::Type(general_type))
//             }
//         }
//     }
// }

impl TypeArg {
    pub fn unify(
        &self,
        concrete: &TypeArg,
        mapping: &mut HashMap<String, Type>,
        param_list: &[String],
    ) -> Result<(), TypeError> {
        match (self, concrete) {
            (TypeArg::Bound(b1), TypeArg::Bound(b2)) => {
                if b1 != b2 {
                    return Err(TypeError {
                        message: format!("Bound mismatch: {} vs {}", b1, b2),
                    });
                }
                Ok(())
            }
            (TypeArg::Type(t_param), TypeArg::Type(t_concrete)) => {
                t_param.unify(t_concrete, mapping, param_list)
            }
            _ => Err(TypeError {
                message: "Cannot unify bound with type".to_owned(),
            }),
        }
    }

    // pub fn has_params(&self, param_list: &[String]) -> bool {
    //     match self {
    //         TypeArg::Bound(_) => false,
    //         TypeArg::Type(t) => t.has_params(param_list),
    //     }
    // }

    pub fn instantiate(&self, mapping: &HashMap<String, Type>) -> Result<TypeArg, TypeError> {
        match self {
            TypeArg::Bound(b) => Ok(TypeArg::Bound(*b)),
            TypeArg::Type(t) => {
                let concrete_type = t.instantiate(mapping)?;
                Ok(TypeArg::Type(concrete_type))
            }
        }
    }
}

// impl ParameterizedType {
//     pub fn basic(name: &str) -> Self {
//         ParameterizedType::Named(name.to_owned(), vec![])
//     }

//     pub fn lambda_type(arg_types: &[ParameterizedType], return_type: &ParameterizedType) -> Self {
//         let mut args = arg_types
//             .iter()
//             .map(|t| ParameterizedTypeArg::Type(t.clone()))
//             .collect::<Vec<ParameterizedTypeArg>>();
//         let ret = ParameterizedTypeArg::Type(return_type.clone());
//         args.push(ret);
//         ParameterizedType::Named("Lambda".to_owned(), args)
//     }

//     pub fn to_type(&self) -> Result<Type, TypeError> {
//         match self {
//             ParameterizedType::Param(name) => Err(TypeError {
//                 message: format!("Unresolved type parameter: {}", name),
//             }),
//             ParameterizedType::Named(name, params) => {
//                 let type_args = params
//                     .iter()
//                     .map(|p| p.to_type())
//                     .collect::<Result<Vec<TypeArg>, TypeError>>()?;
//                 Ok(Type {
//                     name: name.clone(),
//                     type_args,
//                 })
//             }
//         }
//     }

//     pub fn from_type(typ: &Type) -> Self {
//         let params = typ
//             .type_args
//             .iter()
//             .map(ParameterizedTypeArg::from_type)
//             .collect::<Vec<ParameterizedTypeArg>>();
//         ParameterizedType::Named(typ.name.clone(), params)
//     }

//     pub fn most_general(&self) -> Result<Self, TypeError> {
//         if !self.has_params() {
//             return Ok(Self::from_type(&self.to_type()?.most_general_type()));
//         }
//         match self {
//             ParameterizedType::Param(name) => Ok(ParameterizedType::Param(name.clone())),
//             ParameterizedType::Named(name, params) => {
//                 if name == "Array" {
//                     // Special case: Array<T,n> becomes Seq<T>
//                     if params.len() != 2 {
//                         return Err(TypeError {
//                             message: format!(
//                                 "Array type must have 2 parameters, found {}",
//                                 params.len()
//                             ),
//                         });
//                     }
//                     let general_params = vec![params[0].most_general()?];
//                     Ok(ParameterizedType::Named("Seq".to_owned(), general_params))
//                 } else if name == "Vec" {
//                     // Special case: Vec<T> becomes Seq<T>
//                     if params.len() != 1 {
//                         return Err(TypeError {
//                             message: format!(
//                                 "Vec type must have 1 parameter, found {}",
//                                 params.len()
//                             ),
//                         });
//                     }
//                     let general_params = vec![params[0].most_general()?];
//                     Ok(ParameterizedType::Named("Seq".to_owned(), general_params))
//                 } else {
//                     let general_params = params.iter().map(|p| p.most_general()).collect::<Result<
//                         Vec<ParameterizedTypeArg>,
//                         TypeError,
//                     >>(
//                     )?;
//                     Ok(ParameterizedType::Named(name.clone(), general_params))
//                 }
//             }
//         }
//     }
// }

impl Type {
    pub fn unify(
        &self,
        concrete: &Type,
        mapping: &mut HashMap<String, Type>,
        param_list: &[String],
    ) -> Result<(), TypeError> {
        self.most_general_type(param_list)?.unify_inner(
            &concrete.most_general_type(param_list)?,
            mapping,
            param_list,
        )
    }

    fn unify_inner(
        &self,
        concrete: &Type,
        mapping: &mut HashMap<String, Type>,
        param_list: &[String],
    ) -> Result<(), TypeError> {
        if param_list.contains(&self.name) {
            if let Some(mapped_type) = mapping.get(&self.name) {
                if !mapped_type.compatible_with(concrete) {
                    // TODO: if they're compatible but not equal, we might want to merge them instead
                    // e.g. u64 and int
                    return Err(TypeError {
                        message: format!(
                            "Type parameter {} already mapped to {}, cannot map to {}",
                            self.name, mapped_type, concrete
                        ),
                    });
                }
            } else {
                mapping.insert(self.name.clone(), concrete.clone());
            }
            return Ok(());
        } else if concrete.name != self.name {
            return Err(TypeError {
                message: format!(
                    "Type name mismatch: expected {}, found {} (type parameters: {:?})",
                    self.name, concrete.name, param_list
                ),
            });
        }
        if self.type_args.len() != concrete.type_args.len() {
            return Err(TypeError {
                message: format!(
                    "Type argument length mismatch for {}: expected {}, found {}",
                    self.name,
                    self.type_args.len(),
                    concrete.type_args.len()
                ),
            });
        }
        for (param, concrete_arg) in self.type_args.iter().zip(&concrete.type_args) {
            param.unify(concrete_arg, mapping, param_list)?;
        }
        Ok(())
    }

    // pub fn has_params(&self, param_list: &[String]) -> bool {
    //     self.type_args.iter().any(|p| p.has_params(param_list))
    // }

    pub fn instantiate(&self, mapping: &HashMap<String, Type>) -> Result<Type, TypeError> {
        if mapping.contains_key(&self.name) {
            if self.type_args.is_empty() {
                Ok(mapping.get(&self.name).unwrap().clone())
            } else {
                Err(TypeError {
                    message: format!("Type parameter {} cannot have type arguments", self.name),
                })
            }
        } else {
            let type_args = self
                .type_args
                .iter()
                .map(|p| p.instantiate(mapping))
                .collect::<Result<Vec<TypeArg>, TypeError>>()?;
            Ok(Type {
                name: self.name.clone(),
                type_args,
            })
        }
    }
}

impl TStmt {
    pub fn instantiate(&self, mapping: &HashMap<String, Type>) -> Result<TStmt, TypeError> {
        match self {
            TStmt::Expr(texpr) => {
                let concrete_expr = texpr.instantiate(mapping)?;
                Ok(TStmt::Expr(concrete_expr))
            }
            TStmt::Let {
                name,
                typ,
                mutable,
                type_declared,
                value,
            } => {
                let concrete_type = typ.instantiate(mapping)?;
                let concrete_value = value.instantiate(mapping)?;
                Ok(TStmt::Let {
                    name: name.clone(),
                    typ: concrete_type,
                    mutable: *mutable,
                    type_declared: *type_declared,
                    value: concrete_value,
                })
            }
            TStmt::Assign { name, typ, value } => {
                let concrete_type = typ.instantiate(mapping)?;
                let concrete_value = value.instantiate(mapping)?;
                Ok(TStmt::Assign {
                    name: name.clone(),
                    typ: concrete_type,
                    value: concrete_value,
                })
            }
        }
    }
}

impl TExpr {
    pub fn instantiate(&self, mapping: &HashMap<String, Type>) -> Result<TExpr, TypeError> {
        match self {
            TExpr::Literal(lit) => Ok(TExpr::Literal(lit.clone())),
            TExpr::Variable { name, typ } => Ok(TExpr::Variable {
                name: name.clone(),
                typ: typ.instantiate(mapping)?,
            }),
            TExpr::FunctionCall {
                name,
                args,
                return_type,
                optimizations,
            } => {
                let concrete_args = args
                    .iter()
                    .map(|arg| arg.instantiate(mapping))
                    .collect::<Result<Vec<TExpr>, TypeError>>()?;
                let concrete_return_type = return_type.instantiate(mapping)?;
                Ok(TExpr::FunctionCall {
                    name: name.clone(),
                    args: concrete_args,
                    return_type: concrete_return_type,
                    optimizations: optimizations.clone(),
                })
            }
            TExpr::Semicolon(tstmt, texpr) => {
                let concrete_stmt = tstmt.instantiate(mapping)?;
                let concrete_expr = texpr.instantiate(mapping)?;
                Ok(TExpr::Semicolon(
                    Box::new(concrete_stmt),
                    Box::new(concrete_expr),
                ))
            }
            TExpr::Sequence {
                elements,
                elem_type,
            } => {
                let concrete_elements = elements
                    .iter()
                    .map(|elem| elem.instantiate(mapping))
                    .collect::<Result<Vec<TExpr>, TypeError>>()?;
                let concrete_elem_type = elem_type.instantiate(mapping)?;
                Ok(TExpr::Sequence {
                    elements: concrete_elements,
                    elem_type: concrete_elem_type,
                })
            }
            TExpr::EmptySequence => Ok(TExpr::EmptySequence),
            TExpr::Lambda { args, body } => {
                let concrete_args = args
                    .iter()
                    .map(|arg| arg.instantiate(mapping))
                    .collect::<Result<Vec<Arg>, TypeError>>()?;
                let concrete_body = body.instantiate(mapping)?;
                Ok(TExpr::Lambda {
                    args: concrete_args,
                    body: Box::new(concrete_body),
                })
            }
        }
    }
}

impl Arg {
    pub fn instantiate(&self, mapping: &HashMap<String, Type>) -> Result<Arg, TypeError> {
        Ok(Arg {
            name: self.name.clone(),
            arg_type: self.arg_type.instantiate(mapping)?,
        })
    }
}
