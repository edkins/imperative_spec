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
            if arg.typ() != instantiated.skeleton(&[])? {
                compatible = false;
                break;
            }
            preconditions.extend_from_slice(&instantiated.type_assertions(arg.clone(), &[])?);
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
    ) -> Result<Vec<Expr>, TypeError> {
        // Regular postconditions
        let mut postconditions = self.postconditions.clone();

        // Return type postcondition
        let ret_inst = self
            .return_type
            .instantiate(&self.type_params, type_instantiations)?;
        let return_var = Expr::Variable {
            name: self.return_name.clone(),
            typ: Some(ret_inst.skeleton(&[])?),
        };
        let type_postconditions = ret_inst.type_assertions(return_var, &[])?;
        postconditions.extend(type_postconditions);

        Ok(postconditions)
    }
}

impl Stmt {
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
}

impl Expr {
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
