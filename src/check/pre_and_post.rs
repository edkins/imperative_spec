use std::collections::HashMap;

use crate::{
    check::{builtins::lookup_builtin, ops::{Ops, big_and}, types::{TypeError, cartesian_product}},
    syntax::ast::{Expr, ExprKind, FuncDef, Type},
};

impl FuncDef {
    fn type_preconditions(&self, args: &[Expr], type_instantiations: &[Type], outer_type_params: &[String]) -> Result<Vec<Expr>, TypeError> {
        assert!(self.type_params.len() == type_instantiations.len());
        if self.args.len() != args.len() {
            return Err(TypeError {
                message: format!(
                    "Wrong number of arguments: expected {}, got {}",
                    self.args.len(),
                    args.len()
                ),
            });
        }
        let mut preconditions = vec![];
        for (arg, param) in args.iter().zip(&self.args) {
            let instantiated = param
                .arg_type
                .instantiate(&self.type_params, type_instantiations)?;
            if arg.typ() != instantiated.skeleton(outer_type_params)? {
                return Err(TypeError {
                    message: format!(
                        "Argument type mismatch: expected {}, got {}",
                        instantiated.skeleton(outer_type_params)?,
                        arg.typ()
                    ),
                });
            }
            // println!("Generating preconditions for arg {:?} of type {}", arg, instantiated);
            preconditions.extend_from_slice(&instantiated.type_assertions(arg.clone(), outer_type_params)?);
        }
        Ok(preconditions)
    }

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
        // let mut compatible = true;

        let mut preconditions = self.type_preconditions(args, type_instantiations, outer_type_params)?;

        // for (arg, param) in args.iter().zip(&self.args) {
        //     let instantiated = param
        //         .arg_type
        //         .instantiate(&self.type_params, type_instantiations)?;
        //     if arg.typ() != instantiated.skeleton(outer_type_params)? {
        //         compatible = false;
        //         break;
        //     }
        //     preconditions.extend_from_slice(&instantiated.type_assertions(arg.clone(), outer_type_params)?);
        // }

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

        return Ok(preconditions);
    }

    fn possible_narrowings(&self, type_instantiations: &[Type]) -> Result<Vec<Vec<Type>>, TypeError> {
        Ok(cartesian_product(&type_instantiations
            .iter()
            .map(|t| t.narrowings())
            .collect::<Result<Vec<_>, TypeError>>()?))
    }

    pub fn postconditions_and_type_postconditions(
        &self,
        args: &[Expr],
        result: &Expr,
        type_instantiations: &[Type],
        outer_type_params: &[String],
    ) -> Result<Vec<Expr>, TypeError> {
        // Regular postconditions
        let mut postconditions = vec![];
        if !self.postconditions.is_empty() {
            assert!(self.type_params.len() == type_instantiations.len());
            assert!(self.args.len() == args.len());
            let mut arg_mapping = self
                .args
                .iter()
                .map(|arg| arg.name.clone())
                .zip(args.iter().cloned())
                .collect::<HashMap<_, _>>();
            arg_mapping.insert(
                self.return_name.clone(),
                result.clone(),
            );
            for pc in &self.postconditions {
                postconditions.push(pc.type_subst(&self.type_params, type_instantiations)?.subst(&arg_mapping)?);
            }
        }

        // Flowthroughs
        for narrowing in self.possible_narrowings(type_instantiations)? {
            let narrowed_ret_inst = self
                .return_type
                .instantiate(&self.type_params, &narrowing)?;
            let flowthrough_postconditions =
                narrowed_ret_inst.type_assertions(result.clone(), outer_type_params)?;
            let mut flowthrough_preconditions = Expr::zero();
            for (i, pc) in flowthrough_postconditions.iter().enumerate() {
                if i == 0 {
                    // TODO: avoid preconditions if they're already covered?
                    // e.g. fn(u32) -> u32
                    // doesn't need flowthrough preconditions
                    flowthrough_preconditions =
                        big_and(&self.type_preconditions(&args, &narrowing, outer_type_params)?)?;
                }
                postconditions.push(flowthrough_preconditions.implies(&pc)?);
            }
        }

        Ok(postconditions)
    }
}

// impl Stmt {
//     pub fn type_subst(
//         &self,
//         type_params: &[String],
//         type_instantiations: &[Type],
//     ) -> Result<Stmt, TypeError> {
//         match self {
//             Stmt::Expr(expr) => {
//                 let new_expr = expr.type_subst(type_params, type_instantiations)?;
//                 Ok(Stmt::Expr(new_expr))
//             }
//             Stmt::Let {
//                 name,
//                 typ,
//                 mutable,
//                 value,
//             } => {
//                 let new_type = typ.as_ref().map(|t| t.instantiate(type_params, type_instantiations)).transpose()?;
//                 let new_value = value.type_subst(type_params, type_instantiations)?;
//                 Ok(Stmt::Let {
//                     name: name.clone(),
//                     typ: new_type,
//                     mutable: *mutable,
//                     value: new_value,
//                 })
//             }
//             Stmt::Assign { name, value, op } => {
//                 let new_value = value.type_subst(type_params, type_instantiations)?;
//                 Ok(Stmt::Assign {
//                     name: name.clone(),
//                     op: *op,
//                     value: new_value,
//                 })
//             }
//         }
//     }

//     pub fn subst(
//         &self,
//         mapping: &HashMap<String, Expr>,
//     ) -> Result<(Stmt, Option<String>), TypeError> {
//         match self {
//             Stmt::Expr(expr) => {
//                 let new_expr = expr.subst(mapping)?;
//                 Ok((Stmt::Expr(new_expr), None))
//             }
//             Stmt::Let {
//                 name,
//                 typ,
//                 mutable,
//                 value,
//             } => {
//                 let new_value = value.subst(mapping)?;
//                 Ok((
//                     Stmt::Let {
//                         name: name.clone(),
//                         typ: typ.clone(),
//                         mutable: *mutable,
//                         value: new_value,
//                     },
//                     Some(name.clone()),
//                 ))
//             }
//             Stmt::Assign { name, value, op } => {
//                 let new_value = value.subst(mapping)?;
//                 Ok((
//                     Stmt::Assign {
//                         name: name.clone(),
//                         op: *op,
//                         value: new_value,
//                     },
//                     None,
//                 ))
//             }
//         }
//     }
// }

// impl CallArg {
//     pub fn subst(&self, mapping: &HashMap<String, Expr>) -> Result<CallArg, TypeError> {
//         match self {
//             CallArg::Expr(e) => Ok(CallArg::Expr(e.subst(mapping)?)),
//             CallArg::MutVar { name, typ } => {
//                 // TODO: this doesn't really make sense - we can't substitute a mutable thing with an immutable thing
//                 if let Some(replacement) = mapping.get(name) {
//                     Ok(CallArg::Expr(replacement.clone()))
//                 } else {
//                     Ok(CallArg::MutVar {
//                         name: name.clone(),
//                         typ: typ.clone(),
//                     })
//                 }
//             }
//         }
//     }

//     pub fn type_subst(
//         &self,
//         type_params: &[String],
//         type_instantiations: &[Type],
//     ) -> Result<CallArg, TypeError> {
//         match self {
//             CallArg::Expr(e) => Ok(CallArg::Expr(e.type_subst(type_params, type_instantiations)?)),
//             CallArg::MutVar { name, typ } => {
//                 let new_type = typ.as_ref().map(|t| t.instantiate(type_params, type_instantiations)).transpose()?;
//                 Ok(CallArg::MutVar {
//                     name: name.clone(),
//                     typ: new_type,
//                 })
//             }
//         }
//     }
// }

impl Type {
    fn type_subst_in_place(
        &mut self,
        type_params: &[String],
        type_instantiations: &[Type],
    ) -> Result<(), TypeError> {
        *self = self.instantiate(type_params, type_instantiations)?;
        Ok(())
    }
}

impl Expr {
    pub fn type_subst(
        &self,
        type_params: &[String],
        type_instantiations: &[Type],
    ) -> Result<Expr, TypeError> {
        let mut e = self.clone();
        e.type_subst_in_place(type_params, type_instantiations)?;
        Ok(e)
    }

    fn type_subst_in_place(
        &mut self,
        type_params: &[String],
        type_instantiations: &[Type],
    ) -> Result<(), TypeError> {
        self.type_mut()
            .as_mut()
            .unwrap()
            .type_subst_in_place(type_params, type_instantiations)?;
        match self {
            Expr::Variable { .. } => {
                Ok(())
            }
            Expr::Expr { args, type_instantiations: call_type_instantiations, .. } => {
                for t in call_type_instantiations.iter_mut() {
                    t.type_subst_in_place(type_params, type_instantiations)?;
                }
                for arg in args.iter_mut() {
                    arg.type_subst_in_place(type_params, type_instantiations)?;
                }
                Ok(())
            }
            Expr::Let { typ, value, body, .. } => {
                if let Some(t) = typ {
                    t.type_subst_in_place(type_params, type_instantiations)?;
                }
                value.type_subst_in_place(type_params, type_instantiations)?;
                body.type_subst_in_place(type_params, type_instantiations)?;
                Ok(())
            }
            Expr::Lambda { args, body, .. } => {
                for arg in args.iter_mut() {
                    arg.arg_type.type_subst_in_place(type_params, type_instantiations)?;
                }
                body.type_subst_in_place(type_params, type_instantiations)?;
                Ok(())
            }
        }
    }

    pub fn subst(&self, mapping: &HashMap<String, Expr>) -> Result<Expr, TypeError> {
        match self {
            Expr::Variable { name, .. } => {
                if let Some(replacement) = mapping.get(name) {
                    Ok(replacement.clone())
                } else {
                    Err(TypeError {
                        message: format!("No substitution found for variable {}", name),
                    })
                }
            }
            Expr::Expr {
                kind,
                args,
                info,
                type_instantiations,
            } => {
                let new_args = args
                    .iter()
                    .map(|arg| arg.subst(mapping))
                    .collect::<Result<Vec<_>, TypeError>>()?;
                Ok(Expr::Expr {
                    kind: kind.clone(),
                    args: new_args,
                    info: info.clone(),
                    type_instantiations: type_instantiations.clone(),
                })
            }
            Expr::Lambda { args, body, info } => {
                let mut inner_mapping = mapping.clone();
                for arg in args {
                    inner_mapping.insert(arg.name.clone(), arg.arg_type.var(&arg.name));
                }
                let new_body = body.subst(&inner_mapping)?;
                Ok(Expr::Lambda {
                    args: args.clone(),
                    body: Box::new(new_body),
                    info: info.clone(),
                })
            }
            Expr::Let { name, mutable, typ, value, body, info } => {
                let new_value = value.subst(mapping)?;
                let mut inner_mapping = mapping.clone();
                inner_mapping.insert(name.clone(), new_value.clone());
                let new_body = body.subst(&inner_mapping)?;
                Ok(Expr::Let {
                    name: name.clone(),
                    mutable: *mutable,
                    typ: typ.clone(),
                    value: Box::new(new_value),
                    body: Box::new(new_body),
                    info: info.clone(),
                })
            }
        }
    }
}

pub struct PreAndPost {
    pub preconditions: Vec<Expr>,
    pub postconditions: Vec<Expr>,
}

impl FuncDef {
    fn find_by_name(funcs: &[FuncDef], name: &str) -> Result<FuncDef, TypeError> {
        if let Some(builtin) = lookup_builtin(name) {
            return Ok(builtin);
        }
        for func in funcs {
            if func.name == name {
                return Ok(func.clone());
            }
        }
        Err(TypeError {
            message: format!("Function {} not found", name),
        })
    }
}

impl ExprKind {
    pub fn pre_and_post(&self, type_instantiations: &[Type], do_preconditions: bool, args:&[Expr], result: &Expr, funcs: &[FuncDef], outer_type_params: &[String]) -> Result<PreAndPost, TypeError> {
        if !do_preconditions {
            return Ok(PreAndPost {
                preconditions: vec![],
                postconditions: vec![],
            });
        }
        match self {
            ExprKind::Function {
                name,
                ..
            } => {
                let func = FuncDef::find_by_name(funcs, name)?;
                let preconditions = func.lookup_preconditions(args, type_instantiations, outer_type_params)?;
                let postconditions = func.postconditions_and_type_postconditions(args, result, type_instantiations, outer_type_params)?;
                Ok(PreAndPost {
                    preconditions,
                    postconditions,
                })
            }
            ExprKind::Literal{..} | ExprKind::SquareSequence{..} | ExprKind::RoundSequence{..} | ExprKind::TupleAt{..} => Ok(PreAndPost {
                preconditions: vec![],
                postconditions: vec![],
            }),
            ExprKind::UnknownSequenceAt{..} => unreachable!()
        }
    }

    pub fn mutability(&self) -> Vec<bool> {
        match self {
            ExprKind::Function {
                mutable_args,
                ..
            } => mutable_args.clone(),
            ExprKind::Literal{..} => vec![],
            ExprKind::SquareSequence{len} => vec![false; *len],
            ExprKind::RoundSequence{len} => vec![false; *len],
            ExprKind::TupleAt{..} => vec![false,false],
            ExprKind::UnknownSequenceAt{..} => unreachable!(),
        }
    }
}
