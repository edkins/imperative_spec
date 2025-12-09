use std::collections::HashMap;

use crate::check::builtins::lookup_builtin;
use crate::check::ops::Ops;
use crate::check::ztype_ast::{TExpr, TFuncAttribute, TFuncDef, TSourceFile, TStmt};
use crate::syntax::ast::{Arg, AssignOp, Expr, FuncDef, SourceFile, Stmt, Type, TypeArg};

#[derive(Debug)]
pub struct TypeError {
    pub message: String,
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TypeError: {}", self.message)
    }
}
impl std::error::Error for TypeError {}

#[derive(Clone)]
struct TEnv {
    variables: HashMap<String, Type>,
    functions: HashMap<String, TFuncDef>,
}

impl Type {
    pub fn lambda(arg_types: &[Type], ret_type: &Type) -> Type {
        Type {
            name: "Lambda".to_owned(),
            type_args: arg_types
                .iter()
                .cloned()
                .map(TypeArg::Type)
                .chain(std::iter::once(TypeArg::Type(ret_type.clone())))
                .collect(),
        }
    }

    // pub fn call_lambda(&self, arg_types: &[Type]) -> Result<Type, TypeError> {
    //     if self.name != "Lambda" {
    //         return Err(TypeError {
    //             message: format!("Type {} is not a Lambda", self),
    //         });
    //     }
    //     if self.type_args.is_empty() {
    //         return Err(TypeError {
    //             message: format!("Lambda type {} has no type arguments", self),
    //         });
    //     }
    //     if self.type_args.len() != arg_types.len() + 1 {
    //         return Err(TypeError {
    //             message: format!(
    //                 "Lambda type {} expects {} arguments, got {}",
    //                 self,
    //                 self.type_args.len() - 1,
    //                 arg_types.len()
    //             ),
    //         });
    //     }
    //     for (i, arg_type) in arg_types.iter().enumerate() {
    //         match &self.type_args[i] {
    //             TypeArg::Type(t) => {
    //                 if !arg_type.is_subtype_of(t) {
    //                     return Err(TypeError {
    //                         message: format!(
    //                             "Lambda argument type mismatch: expected {}, got {}",
    //                             t, arg_type
    //                         ),
    //                     });
    //                 }
    //             }
    //             _ => {
    //                 return Err(TypeError {
    //                     message: format!("Lambda argument type {} is not a Type", self),
    //                 });
    //             }
    //         }
    //     }
    //     match &self.type_args[self.type_args.len() - 1] {
    //         TypeArg::Type(t) => Ok(t.clone()),
    //         _ => Err(TypeError {
    //             message: format!("Lambda return type of {} is not a Type", self),
    //         }),
    //     }
    // }

    // pub fn two_bounds_args(&self) -> Result<(Bound, Bound), TypeError> {
    //     if self.type_args.len() != 2 {
    //         return Err(TypeError {
    //             message: format!("Type {} should have exactly two type arguments", self),
    //         });
    //     }
    //     let lower = match &self.type_args[0] {
    //         TypeArg::Bound(b) => *b,
    //         _ => {
    //             return Err(TypeError {
    //                 message: format!("First type argument of {} is not a Bound", self),
    //             });
    //         }
    //     };
    //     let upper = match &self.type_args[1] {
    //         TypeArg::Bound(b) => *b,
    //         _ => {
    //             return Err(TypeError {
    //                 message: format!("Second type argument of {} is not a Bound", self),
    //             });
    //         }
    //     };
    //     Ok((lower, upper))
    // }
}

impl Expr {
    fn type_check(&self, env: &mut TEnv, hint: Option<&Type>) -> Result<TExpr, TypeError> {
        match self {
            Expr::Literal(lit) => Ok(TExpr::Literal(lit.clone())),
            Expr::Variable(x) => {
                if let Some(typ) = env.variables.get(x) {
                    Ok(TExpr::Variable {
                        name: x.clone(),
                        typ: typ.clone(),
                    })
                } else {
                    Err(TypeError {
                        message: format!("Undefined variable: {}", x),
                    })
                }
            }
            Expr::FunctionCall { name, args } => {
                let funcdef = env.get_function(name)?;
                if args.len() != funcdef.args.len() {
                    return Err(TypeError {
                        message: format!(
                            "Function {} expects {} arguments, got {}",
                            name,
                            funcdef.args.len(),
                            args.len()
                        ),
                    });
                }
                let targs = args
                    .iter()
                    .zip(&funcdef.args)
                    .map(|(a0, a1)| a0.type_check(env, Some(&a1.arg_type)))
                    .collect::<Result<Vec<TExpr>, TypeError>>()?;
                funcdef.make_func_call(&targs)
            }
            Expr::Semicolon(stmt, expr) => {
                let tstmt = stmt.type_check(env)?;
                let texpr = expr.type_check(env, hint)?;
                Ok(TExpr::Semicolon(Box::new(tstmt.clone()), Box::new(texpr)))
            }
            Expr::Sequence { square, elems } => {
                if hint.is_none() {
                    return Err(TypeError {
                        message: "Type hint required for sequence expressions".to_owned(),
                    });
                }
                let hint = hint.unwrap();
                if *square != hint.is_square_seq() {
                    return Err(TypeError {
                        message: format!(
                            "Sequence square type mismatch: expected square={}, got square={}",
                            hint.is_square_seq(),
                            square
                        ),
                    });
                }
                let elements = elems
                    .iter()
                    .enumerate()
                    .map(|(i, e)| e.type_check(env, hint.get_either_elem_type(i as u64)))
                    .collect::<Result<Vec<TExpr>, TypeError>>()?;
                Ok(TExpr::Sequence {
                    elements,
                    sequence_type: hint.clone(),
                })
            }
        }
    }
}

impl AssignOp {
    fn mk_expr(&self, left: &TExpr, right: &TExpr) -> Result<TExpr, TypeError> {
        match self {
            AssignOp::Assign => Ok(right.clone()),
            AssignOp::PlusAssign => {
                if left.typ().is_int() && right.typ().is_int() {
                    left.add(right)
                } else {
                    Err(TypeError {
                        message: format!(
                            "PlusAssign requires integer types got {} and {}",
                            left.typ(),
                            right.typ()
                        ),
                    })
                }
            }
            AssignOp::MinusAssign => {
                if left.typ().is_int() && right.typ().is_int() {
                    left.sub(right)
                } else {
                    Err(TypeError {
                        message: format!(
                            "MinusAssign requires integer types got {} and {}",
                            left.typ(),
                            right.typ()
                        ),
                    })
                }
            }
        }
    }
}

impl Stmt {
    fn type_check(&self, env: &mut TEnv) -> Result<TStmt, TypeError> {
        match self {
            Stmt::Expr(e) => {
                let te = e.type_check(env, None)?;
                Ok(TStmt::Expr(te))
            }
            Stmt::Let { name, typ, value } => {
                let tvalue = value.type_check(env, typ.as_ref())?;
                let vtype = if let Some(typ) = typ {
                    if !tvalue.typ().compatible_with(typ) {
                        return Err(TypeError {
                            message: format!(
                                "Type of value {} does not match declared type {} for variable {}",
                                tvalue.typ(),
                                typ,
                                name
                            ),
                        });
                    }
                    typ.clone()
                } else {
                    tvalue.typ()
                };
                env.variables.insert(name.clone(), vtype.clone());
                Ok(TStmt::Let {
                    name: name.clone(),
                    typ: vtype,
                    mutable: false,
                    type_declared: typ.is_some(),
                    value: tvalue,
                })
            }
            Stmt::LetMut { name, typ, value } => {
                let tvalue = value.type_check(env, Some(typ))?;
                if !tvalue.typ().compatible_with(typ) {
                    return Err(TypeError {
                        message: format!(
                            "Type of value {} does not match declared type {} for variable {}",
                            tvalue.typ(),
                            typ,
                            name
                        ),
                    });
                }
                env.variables.insert(name.clone(), typ.clone());
                Ok(TStmt::Let {
                    name: name.clone(),
                    typ: typ.clone(),
                    mutable: true,
                    type_declared: true,
                    value: tvalue,
                })
            }
            Stmt::Assign { name, op, value } => {
                let var_type = env
                    .variables
                    .get(name)
                    .ok_or(TypeError {
                        message: format!("Undefined variable: {}", name),
                    })?
                    .clone();
                let tvalue = value.type_check(env, Some(&var_type))?;
                let old_left = TExpr::Variable {
                    name: name.clone(),
                    typ: var_type.clone(),
                };
                let result = op.mk_expr(&old_left, &tvalue)?;
                if !result.typ().compatible_with(&var_type) {
                    return Err(TypeError {
                        message: format!(
                            "Resulting type of assignment does not match variable type for {}",
                            name
                        ),
                    });
                }
                Ok(TStmt::Assign {
                    name: name.clone(),
                    typ: var_type.clone(),
                    value: result,
                })
            }
        }
    }
}

impl TFuncAttribute {
    fn from_expr(expr: &Expr) -> Result<TFuncAttribute, TypeError> {
        match expr {
            Expr::FunctionCall { name, args } if name == "check_decisions" => {
                let args = args
                    .iter()
                    .map(|arg| match arg {
                        Expr::Variable(x) => Ok(x.clone()),
                        _ => Err(TypeError {
                            message: "check_decisions arguments must be u64 literals".to_owned(),
                        }),
                    })
                    .collect::<Result<Vec<String>, TypeError>>()?;
                Ok(TFuncAttribute::CheckDecisions(args))
            }
            _ => Err(TypeError {
                message: format!("Unknown function attribute: {}", expr),
            }),
        }
    }
}

impl TEnv {
    fn get_function(&self, name: &str) -> Result<TFuncDef, TypeError> {
        if let Some(b) = lookup_builtin(name) {
            return Ok(b);
        }
        self.functions.get(name).cloned().ok_or(TypeError {
            message: format!("Function {} not found in environment", name),
        })
    }
}

impl FuncDef {
    fn decl(&self) -> Result<TFuncDef, TypeError> {
        let mut arg_types = vec![];
        for a in &self.args {
            arg_types.push(a.arg_type.clone());
        }
        let return_type = self.return_type.clone();
        Ok(TFuncDef::simple(&self.name, &arg_types, &return_type))
    }

    fn type_check(&self, env: &mut TEnv) -> Result<TFuncDef, TypeError> {
        let mut local_env = env.clone();
        let decl = &env.get_function(&self.name)?;
        assert!(decl.args.len() == self.args.len());
        for (a, a2) in self.args.iter().zip(&decl.args) {
            if local_env.variables.contains_key(&a.name) {
                return Err(TypeError {
                    message: format!("Duplicate argument name: {}", a.name),
                });
            }
            local_env
                .variables
                .insert(a.name.clone(), a2.arg_type.clone());
        }
        let args_env = local_env.clone();
        let tbody = self
            .body
            .type_check(&mut local_env, Some(&decl.return_type))?;
        if !tbody.typ().compatible_with(&decl.return_type) {
            return Err(TypeError {
                message: format!(
                    "Function {} body type {} does not match declared return type {}",
                    self.name,
                    tbody.typ(),
                    decl.return_type
                ),
            });
        }
        let mut preconditions = vec![];
        let mut postconditions = vec![];
        preconditions.extend(
            self.preconditions
                .iter()
                .map(|p| p.type_check(&mut args_env.clone(), Some(&Type::basic("bool"))))
                .collect::<Result<Vec<TExpr>, TypeError>>()?,
        );
        let mut post_args_env = args_env.clone();
        if self.return_name.is_some() {
            post_args_env
                .variables
                .insert(self.return_name.clone().unwrap(), decl.return_type.clone());
        }
        postconditions.extend(
            self.postconditions
                .iter()
                .map(|p| p.type_check(&mut post_args_env, Some(&Type::basic("bool"))))
                .collect::<Result<Vec<TExpr>, TypeError>>()?,
        );

        let args = self
            .args
            .iter()
            .zip(&decl.args)
            .map(|(a, a2)| Arg {
                name: a.name.clone(),
                arg_type: a2.arg_type.clone(),
            })
            .collect::<Vec<_>>();

        let mut attributes = self
            .attributes
            .iter()
            .map(TFuncAttribute::from_expr)
            .collect::<Result<Vec<TFuncAttribute>, TypeError>>()?;
        for see in &self.sees {
            attributes.push(TFuncAttribute::Sees(see.clone()));
        }

        Ok(TFuncDef {
            attributes,
            name: self.name.clone(),
            args,
            return_type: decl.return_type.clone(),
            return_name: self
                .return_name
                .clone()
                .unwrap_or_else(|| "__ret__".to_owned()),
            preconditions,
            postconditions,
            body: Some(tbody),
            optimizations: vec![],
            type_params: vec![],
        })
    }
}

impl SourceFile {
    pub fn type_check(&self) -> Result<TSourceFile, TypeError> {
        let mut env = TEnv {
            variables: HashMap::new(),
            functions: HashMap::new(),
        };

        for func in &self.functions {
            let overload = func.decl()?;
            if env.functions.contains_key(&func.name) {
                return Err(TypeError {
                    message: format!("Duplicate function name: {}", func.name),
                });
            }
            env.functions.insert(func.name.clone(), overload);
        }
        let tfuncs = self
            .functions
            .iter()
            .map(|f| f.type_check(&mut env))
            .collect::<Result<Vec<TFuncDef>, TypeError>>()?;
        Ok(TSourceFile { functions: tfuncs })
    }
}
