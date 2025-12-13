use std::collections::HashMap;

use crate::{
    check::types::TypeError,
    syntax::ast::{CallArg, Expr, FuncDef, Stmt, Type},
};

impl FuncDef {
    pub fn lookup_preconditions(
        &self,
        args: &[Expr],
        type_instantiations: &[Type],
        outer_type_params: &[String],
    ) -> Result<Vec<Expr>, TypeError> {
        assert!(
            self.type_params.len() == type_instantiations.len(),
            "Function {} called with wrong number of type instantiations: expected {:?}, got {:?}",
            self.name,
            self.type_params,
            type_instantiations
        );
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
            let instantiated = param
                .arg_type
                .instantiate(&self.type_params, type_instantiations)?;
            if arg.typ() != instantiated.skeleton(outer_type_params)? {
                compatible = false;
                break;
            }
            preconditions.extend_from_slice(&instantiated.type_assertions(arg.clone(), outer_type_params)?);
        }

        if !self.preconditions.is_empty() {
            let arg_mapping = self
                .args
                .iter()
                .map(|arg| arg.name.clone())
                .zip(args.iter().cloned())
                .collect::<HashMap<_, _>>();
            for cond in &self.preconditions {
                preconditions.push(cond.type_subst(&self.type_params, type_instantiations)?.subst(&arg_mapping)?);
            }
        }

        if compatible {
            return Ok(preconditions);
        }
        Err(TypeError {
            message: format!(
                "lookup_preconditions: No matching function overload found for {} given argument types {}",
                self.name,
                args.iter()
                    .map(|t| t.typ().to_string())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
        })
    }

    pub fn postconditions_and_type_postconditions(
        &self,
        type_instantiations: &[Type],
        outer_type_params: &[String],
    ) -> Result<Vec<Expr>, TypeError> {
        // Regular postconditions
        let mut postconditions = self.postconditions
            .iter()
            .map(|t| t.type_subst(&self.type_params, type_instantiations))
            .collect::<Result<Vec<_>, TypeError>>()?;

        // Return type postcondition
        let ret_inst = self
            .return_type
            .instantiate(&self.type_params, type_instantiations)?;
        let return_var = Expr::Variable {
            name: self.return_name.clone(),
            typ: Some(ret_inst.skeleton(outer_type_params)?),
        };
        let type_postconditions = ret_inst.type_assertions(return_var, outer_type_params)?;
        postconditions.extend(type_postconditions);

        Ok(postconditions)
    }
}

impl Stmt {
    pub fn type_subst(
        &self,
        type_params: &[String],
        type_instantiations: &[Type],
    ) -> Result<Stmt, TypeError> {
        match self {
            Stmt::Expr(expr) => {
                let new_expr = expr.type_subst(type_params, type_instantiations)?;
                Ok(Stmt::Expr(new_expr))
            }
            Stmt::Let {
                name,
                typ,
                mutable,
                value,
            } => {
                let new_type = typ.as_ref().map(|t| t.instantiate(type_params, type_instantiations)).transpose()?;
                let new_value = value.type_subst(type_params, type_instantiations)?;
                Ok(Stmt::Let {
                    name: name.clone(),
                    typ: new_type,
                    mutable: *mutable,
                    value: new_value,
                })
            }
            Stmt::Assign { name, value, op } => {
                let new_value = value.type_subst(type_params, type_instantiations)?;
                Ok(Stmt::Assign {
                    name: name.clone(),
                    op: *op,
                    value: new_value,
                })
            }
        }
    }

    pub fn subst(
        &self,
        mapping: &HashMap<String, Expr>,
    ) -> Result<(Stmt, Option<String>), TypeError> {
        match self {
            Stmt::Expr(expr) => {
                let new_expr = expr.subst(mapping)?;
                Ok((Stmt::Expr(new_expr), None))
            }
            Stmt::Let {
                name,
                typ,
                mutable,
                value,
            } => {
                let new_value = value.subst(mapping)?;
                Ok((
                    Stmt::Let {
                        name: name.clone(),
                        typ: typ.clone(),
                        mutable: *mutable,
                        value: new_value,
                    },
                    Some(name.clone()),
                ))
            }
            Stmt::Assign { name, value, op } => {
                let new_value = value.subst(mapping)?;
                Ok((
                    Stmt::Assign {
                        name: name.clone(),
                        op: *op,
                        value: new_value,
                    },
                    None,
                ))
            }
        }
    }
}

impl CallArg {
    pub fn subst(&self, mapping: &HashMap<String, Expr>) -> Result<CallArg, TypeError> {
        match self {
            CallArg::Expr(e) => Ok(CallArg::Expr(e.subst(mapping)?)),
            CallArg::MutVar { name, typ } => {
                // TODO: this doesn't really make sense - we can't substitute a mutable thing with an immutable thing
                if let Some(replacement) = mapping.get(name) {
                    Ok(CallArg::Expr(replacement.clone()))
                } else {
                    Ok(CallArg::MutVar {
                        name: name.clone(),
                        typ: typ.clone(),
                    })
                }
            }
        }
    }

    pub fn type_subst(
        &self,
        type_params: &[String],
        type_instantiations: &[Type],
    ) -> Result<CallArg, TypeError> {
        match self {
            CallArg::Expr(e) => Ok(CallArg::Expr(e.type_subst(type_params, type_instantiations)?)),
            CallArg::MutVar { name, typ } => {
                let new_type = typ.as_ref().map(|t| t.instantiate(type_params, type_instantiations)).transpose()?;
                Ok(CallArg::MutVar {
                    name: name.clone(),
                    typ: new_type,
                })
            }
        }
    }
}

impl Expr {
    pub fn type_subst(
        &self,
        type_params: &[String],
        type_instantiations: &[Type],
    ) -> Result<Expr, TypeError> {
        match self {
            Expr::Literal(literal) => Ok(Expr::Literal(literal.clone())),
            Expr::Variable { name, typ } => {
                let new_type = if let Some(t) = typ {
                    Some(t.instantiate(type_params, type_instantiations)?)
                } else {
                    None
                };
                Ok(Expr::Variable {
                    name: name.clone(),
                    typ: new_type,
                })
            }
            Expr::FunctionCall {
                name,
                args,
                return_type,
                type_instantiations: call_type_instantiations,
            } => {
                let new_args = args
                    .iter()
                    .map(|arg| arg.type_subst(type_params, type_instantiations))
                    .collect::<Result<Vec<_>, TypeError>>()?;
                let new_return_type =
                    return_type.as_ref().map(|t| t.instantiate(type_params, type_instantiations)).transpose()?;
                let new_type_instantiations = call_type_instantiations
                    .iter()
                    .map(|t| t.instantiate(type_params, type_instantiations))
                    .collect::<Result<Vec<_>, TypeError>>()?;
                Ok(Expr::FunctionCall {
                    name: name.clone(),
                    args: new_args,
                    return_type: new_return_type,
                    type_instantiations: new_type_instantiations,
                })
            }
            _ => Ok(self.clone()), // Other cases can be implemented similarly
        }
    }

    pub fn subst(&self, mapping: &HashMap<String, Expr>) -> Result<Expr, TypeError> {
        match self {
            Expr::Literal(literal) => Ok(Expr::Literal(literal.clone())),
            Expr::Variable { name, .. } => {
                if let Some(replacement) = mapping.get(name) {
                    Ok(replacement.clone())
                } else {
                    Err(TypeError {
                        message: format!("No substitution found for variable {}", name),
                    })
                }
            }
            Expr::FunctionCall {
                name,
                args,
                return_type,
                type_instantiations,
            } => {
                let new_args = args
                    .iter()
                    .map(|arg| arg.subst(mapping))
                    .collect::<Result<Vec<_>, TypeError>>()?;
                Ok(Expr::FunctionCall {
                    name: name.clone(),
                    args: new_args,
                    return_type: return_type.clone(),
                    type_instantiations: type_instantiations.clone(),
                })
            }
            Expr::Semicolon(stmt, expr) => {
                let (new_stmt, new_var) = stmt.subst(mapping)?;
                if let Some(var_name) = new_var {
                    let mut new_mapping = mapping.clone();
                    new_mapping.insert(
                        var_name.clone(),
                        Expr::Variable {
                            name: var_name.clone(),
                            typ: None,
                        },
                    );
                    let new_expr = expr.subst(&new_mapping)?;
                    return Ok(Expr::Semicolon(Box::new(new_stmt), Box::new(new_expr)));
                } else {
                    let new_expr = expr.subst(mapping)?;
                    Ok(Expr::Semicolon(Box::new(new_stmt), Box::new(new_expr)))
                }
            }
            Expr::SquareSequence { elems, elem_type } => {
                let new_elements = elems
                    .iter()
                    .map(|elem| elem.subst(mapping))
                    .collect::<Result<Vec<Expr>, TypeError>>()?;
                Ok(Expr::SquareSequence {
                    elems: new_elements,
                    elem_type: elem_type.clone(),
                })
            }
            Expr::RoundSequence { elems } => {
                let new_elements = elems
                    .iter()
                    .map(|elem| elem.subst(mapping))
                    .collect::<Result<Vec<Expr>, TypeError>>()?;
                Ok(Expr::RoundSequence {
                    elems: new_elements,
                })
            }
            Expr::Lambda { args, body } => {
                let mut inner_mapping = mapping.clone();
                for arg in args {
                    inner_mapping.insert(arg.name.clone(), arg.arg_type.var(&arg.name));
                }
                let new_body = body.subst(&inner_mapping)?;
                Ok(Expr::Lambda {
                    args: args.clone(),
                    body: Box::new(new_body),
                })
            }
            Expr::SeqAt { seq, index } => {
                let new_seq = seq.subst(mapping)?;
                let new_index = index.subst(mapping)?;
                Ok(Expr::SeqAt {
                    seq: Box::new(new_seq),
                    index: Box::new(new_index),
                })
            } // Expr::Cast { expr, to_type } => {
              //     let new_expr = expr.subst(mapping)?;
              //     Ok(Expr::Cast {
              //         expr: Box::new(new_expr),
              //         to_type: to_type.clone(),
              //     })
              // }
        }
    }
}
