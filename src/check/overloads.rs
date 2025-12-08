use std::collections::{HashMap, HashSet};

use crate::{
    check::{
        ztype_ast::{TExpr, TFuncDef, TStmt},
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

    pub fn psimple(name: &str, arg_types: &[Type], return_type: &Type, type_param_list: &[&str]) -> Self {
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
                    arg_type: t.clone(),
                })
                .collect::<Vec<Arg>>(),
            optimizations: vec![],
            preconditions: vec![],
            postconditions: vec![],
            side_effects: HashSet::new(),
            sees: vec![],
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
                .unify(arg_type, &mut mapping, &self.type_params)?;
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
    ) -> Result<TFuncDef, TypeError> {
        Ok(TFuncDef {
            args: self.args
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
            postconditions: self.postconditions
                .iter()
                .map(|e| e.instantiate(mapping))
                .collect::<Result<Vec<TExpr>, TypeError>>()?,
            side_effects: self.side_effects.clone(),
            sees: self.sees.clone(),
            body: self.body.as_ref().map(|b| b.instantiate(mapping)).transpose()?,
        })
    }

    // pub fn extract_single(&self) -> Result<TFunc, TypeError> {
    //     if !self.headline.type_param_list.is_empty() {
    //         return Err(TypeError {
    //             message: "Cannot extract single function from parameterized overloaded function"
    //                 .to_owned(),
    //         });
    //     }
    //     Ok(TFunc {
    //         args: self.headline.args.clone(),
    //         return_type: self.headline.return_type.clone(),
    //         type_param_list: vec![],
    //     })
    // }

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

impl TFuncDef {
    pub fn lookup_preconditions(&self, args: &[TExpr]) -> Result<Vec<TExpr>, TypeError> {
        if self.args.len() != args.len() {
            return Err(TypeError {
                message: format!(
                    "Wrong number of arguments: expected {}, got {}",
                    self.args.len(),
                    args.len()
                ),
            });
        }
        let mut compatible = true;

        let mut preconditions = vec![];

        for (arg, param) in args.iter().zip(&self.args) {
            if !arg.typ().compatible_with(&param.arg_type) {
                compatible = false;
                break;
            }
            preconditions.extend_from_slice(
                &param
                    .arg_type
                    .type_assertions(arg.clone(), &self.type_params)?,
            );
        }

        if !self.preconditions.is_empty() {
            let arg_mapping = self
                .args
                .iter()
                .map(|arg| arg.name.clone())
                .zip(args.iter().cloned())
                .collect::<HashMap<_, _>>();
            for cond in &self.preconditions {
                preconditions.push(cond.subst(&arg_mapping)?);
            }
        }

        if compatible {
            return Ok(preconditions);
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

impl TStmt {
    pub fn subst(&self, mapping: &HashMap<String, TExpr>) -> Result<TStmt, TypeError> {
        match self {
            TStmt::Expr(expr) => {
                let new_expr = expr.subst(mapping)?;
                Ok(TStmt::Expr(new_expr))
            }
            TStmt::Let {
                name,
                typ,
                mutable,
                type_declared,
                value,
            } => {
                let new_value = value.subst(mapping)?;
                Ok(TStmt::Let {
                    name: name.clone(),
                    typ: typ.clone(),
                    mutable: *mutable,
                    type_declared: *type_declared,
                    value: new_value,
                })
            }
            TStmt::Assign { name, value, typ } => {
                let new_value = value.subst(mapping)?;
                Ok(TStmt::Assign {
                    name: name.clone(),
                    typ: typ.clone(),
                    value: new_value,
                })
            }
        }
    }
}

impl TExpr {
    pub fn subst(&self, mapping: &HashMap<String, TExpr>) -> Result<TExpr, TypeError> {
        match self {
            TExpr::Literal(literal) => Ok(TExpr::Literal(literal.clone())),
            TExpr::Variable { name, .. } => {
                if let Some(replacement) = mapping.get(name) {
                    Ok(replacement.clone())
                } else {
                    Err(TypeError {
                        message: format!("No substitution found for variable {}", name),
                    })
                }
            }
            TExpr::FunctionCall {
                name,
                args,
                return_type,
                optimizations,
            } => {
                let new_args = args
                    .iter()
                    .map(|arg| arg.subst(mapping))
                    .collect::<Result<Vec<TExpr>, TypeError>>()?;
                Ok(TExpr::FunctionCall {
                    name: name.clone(),
                    args: new_args,
                    return_type: return_type.clone(),
                    optimizations: optimizations.clone(),
                })
            }
            TExpr::Semicolon(stmt, expr) => {
                let new_stmt = stmt.subst(mapping)?;
                let new_expr = expr.subst(mapping)?;
                Ok(TExpr::Semicolon(Box::new(new_stmt), Box::new(new_expr)))
            }
            TExpr::Sequence {
                elements,
                elem_type,
            } => {
                let new_elements = elements
                    .iter()
                    .map(|elem| elem.subst(mapping))
                    .collect::<Result<Vec<TExpr>, TypeError>>()?;
                Ok(TExpr::Sequence {
                    elements: new_elements,
                    elem_type: elem_type.clone(),
                })
            }
            TExpr::EmptySequence => Ok(TExpr::EmptySequence),
            TExpr::Lambda { args, body } => {
                let new_body = body.subst(mapping)?;
                Ok(TExpr::Lambda {
                    args: args.clone(),
                    body: Box::new(new_body),
                })
            }
        }
    }
}
