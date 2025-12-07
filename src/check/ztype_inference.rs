use std::collections::HashMap;
use std::slice::from_ref;

use crate::check::builtins::builtins;
use crate::check::overloads::TOverloadedFunc;
use crate::check::ztype_ast::{TExpr, TFuncDef, TSourceFile, TStmt};
use crate::syntax::ast::{
    Arg, AssignOp, Bound, Expr, FuncDef, Literal, SourceFile, Stmt, Type, TypeArg,
};

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

// #[derive(Clone)]
// struct TFunc {
//     arg_types: Vec<Type>,
//     return_type: Type,
//     return_name: String,
//     arg_preconditions: Vec<TExpr>,
//     return_postconditions: Vec<TExpr>,
// }

#[derive(Clone)]
struct TEnv {
    variables: HashMap<String, Type>,
    functions: HashMap<String, TOverloadedFunc>,
}

const MAX_UNROLL: u64 = 64;

impl Bound {
    pub fn as_u64(&self) -> Result<u64, TypeError> {
        match self {
            Bound::I64(i) => {
                if *i < 0 {
                    return Err(TypeError {
                        message: format!("Bound {} is negative, cannot convert to u64", self),
                    });
                }
                Ok(*i as u64)
            }
            Bound::U64(u) => Ok(*u),
            _ => Err(TypeError {
                message: format!("Bound {} is not a u64", self),
            }),
        }
    }
}

// impl Type {
//     pub fn is_int(&self) -> bool {
//         self.name.as_str() == "int" && self.type_args.is_empty()
//     }

//     pub fn canonicalize(&self, name: &str) -> Result<(Type, Vec<TExpr>), TypeError> {
//         self.canonicalize_expr(|typ| TExpr::Variable {
//             name: name.to_owned(),
//             typ,
//         })
//     }

//     pub fn canonicalize_dummy(&self) -> Result<Type, TypeError> {
//         let (canon, _) = self.canonicalize_expr(|_| TExpr::Literal(Literal::Unit))?;
//         Ok(canon)
//     }

//     pub fn canonicalize_const(&self, expr: &TExpr) -> Result<Vec<TExpr>, TypeError> {
//         let (_, conditions) = self.canonicalize_expr(|_| expr.clone())?;
//         Ok(conditions)
//     }

//     pub fn canonicalize_expr(
//         &self,
//         expr_factory: impl Fn(Type) -> TExpr,
//     ) -> Result<(Type, Vec<TExpr>), TypeError> {
//         match self.name.as_str() {
//             "i8" | "i16" | "i32" | "i64" | "u8" | "u16" | "u32" | "u64" | "int" | "nat" => {
//                 self.no_type_args()?;
//                 let (lower, upper) = lookup_in_bounds(self.name.as_str());
//                 Ok((
//                     Type::basic("int"),
//                     bounds_to_expr(lower, upper, expr_factory),
//                 ))
//             }
//             "str" | "bool" | "void" => {
//                 self.no_type_args()?;
//                 Ok((self.clone(), vec![]))
//             }
//             "Vec" => {
//                 let elem_type = self.one_type_arg()?;
//                 let (type_lambda, elem_canon) = TEnv::type_lambda(&elem_type)?;
//                 let vec_type = Type {
//                     name: "Seq".to_owned(),
//                     type_args: vec![TypeArg::Type(elem_canon.clone())],
//                 };
//                 let conds = if let Some(type_lambda) = type_lambda {
//                     let array_expr = expr_factory(vec_type.clone());
//                     vec![array_expr.seq_all(&type_lambda)?]
//                 } else {
//                     vec![]
//                 };
//                 Ok((vec_type, conds))
//             }
//             "Array" => {
//                 let (elem_type, size) = self.one_type_one_u64_args()?;
//                 if size > MAX_UNROLL {
//                     return Err(TypeError {
//                         message: format!(
//                             "Array size {} exceeds maximum unroll limit {}",
//                             size, MAX_UNROLL
//                         ),
//                     });
//                 }
//                 let elem_canon = elem_type.canonicalize_dummy()?;
//                 let array_type = Type {
//                     name: "Seq".to_owned(),
//                     type_args: vec![TypeArg::Type(elem_canon)],
//                 };
//                 let array_expr = expr_factory(array_type.clone());
//                 let mut conditions = vec![
//                     array_expr
//                         .seq_len()?
//                         .eq(&TExpr::Literal(Literal::U64(size)))?,
//                 ];
//                 for i in 0..size {
//                     let index_expr = TExpr::Literal(Literal::U64(i));
//                     let elem_expr = array_expr.seq_at(&index_expr)?;
//                     let condition = elem_type.canonicalize_const(&elem_expr)?;
//                     conditions.extend_from_slice(&condition);
//                 }
//                 Ok((array_type, conditions))
//             }
//             _ => Err(TypeError {
//                 message: format!("Cannot canonicalize user-defined type {}", self),
//             }),
//         }
//     }
//  }

impl Type {

    pub fn find_equality_type(&self, other: &Type) -> Result<Type, TypeError> {
        self.find_common_type(other)
    }

    pub fn find_common_type(&self, other: &Type) -> Result<Type, TypeError> {
        if self == other {
            return Ok(self.clone());
        }
        // if self.is_int() && other.is_int() {
        //     let (self_min, self_max) = self.int_bounds();
        //     let (other_min, other_max) = other.int_bounds();
        //     let lower = self_min.min(other_min);
        //     let upper = self_max.max(other_max);
        //     return Ok(Type::basic("int"));
        // }
        Err(TypeError {
            message: format!("No common equality type found for {} and {}", self, other),
        })
    }

    pub fn one_type_one_u64_args(&self) -> Result<(Type, u64), TypeError> {
        if self.type_args.len() != 2 {
            return Err(TypeError {
                message: format!("Type {} should have exactly two type arguments", self),
            });
        }
        let t = match &self.type_args[0] {
            TypeArg::Type(t) => t.clone(),
            _ => {
                return Err(TypeError {
                    message: format!("First type argument of {} is not a Type", self),
                });
            }
        };
        let b = match &self.type_args[1] {
            TypeArg::Bound(b) => *b,
            _ => {
                return Err(TypeError {
                    message: format!("Second type argument of {} is not a Bound", self),
                });
            }
        };
        Ok((t, b.as_u64()?))
    }

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

    pub fn call_lambda(&self, arg_types: &[Type]) -> Result<Type, TypeError> {
        if self.name != "Lambda" {
            return Err(TypeError {
                message: format!("Type {} is not a Lambda", self),
            });
        }
        if self.type_args.is_empty() {
            return Err(TypeError {
                message: format!("Lambda type {} has no type arguments", self),
            });
        }
        if self.type_args.len() != arg_types.len() + 1 {
            return Err(TypeError {
                message: format!(
                    "Lambda type {} expects {} arguments, got {}",
                    self,
                    self.type_args.len() - 1,
                    arg_types.len()
                ),
            });
        }
        for (i, arg_type) in arg_types.iter().enumerate() {
            match &self.type_args[i] {
                TypeArg::Type(t) => {
                    if !arg_type.is_subtype_of(t) {
                        return Err(TypeError {
                            message: format!(
                                "Lambda argument type mismatch: expected {}, got {}",
                                t, arg_type
                            ),
                        });
                    }
                }
                _ => {
                    return Err(TypeError {
                        message: format!("Lambda argument type {} is not a Type", self),
                    });
                }
            }
        }
        match &self.type_args[self.type_args.len() - 1] {
            TypeArg::Type(t) => Ok(t.clone()),
            _ => Err(TypeError {
                message: format!("Lambda return type of {} is not a Type", self),
            }),
        }
    }

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

pub fn big_and(exprs: &[TExpr]) -> Result<TExpr, TypeError> {
    if exprs.is_empty() {
        return Ok(TExpr::Literal(Literal::Bool(true)));
    }
    let mut result = exprs[0].clone();
    for e in &exprs[1..] {
        result = result.and(e)?;
    }
    Ok(result)
}

impl TExpr {
    /// Won't necessarily return something with the "exact" correct type
    /// but will coerce empty sequences to a typed sequence.
    pub fn coerce(&self, target_type: &Type) -> Result<TExpr, TypeError> {
        if !self.typ().compatible_with(target_type) {
            return Err(TypeError {
                message: format!("Cannot coerce type {} to {}", self.typ(), target_type),
            });
        }
        if matches!(self, TExpr::EmptySequence) && target_type.name == "Seq" {
            let elem_type = target_type.one_type_arg()?;
            return Ok(TExpr::Sequence {
                elements: vec![],
                elem_type,
            });
        }
        Ok(self.clone())
    }

    pub fn as_assertion(&self) -> TStmt {
        assert!(self.typ().is_bool());
        TStmt::Expr(TExpr::FunctionCall {
            name: "assert".to_owned(),
            args: vec![self.clone()],
            return_type: Type::basic("void"),
        })
    }

    pub fn eq(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        let eqt = self.typ().find_equality_type(&other.typ())?;
        let left = self.coerce(&eqt)?;
        let right = other.coerce(&eqt)?;
        Ok(TExpr::FunctionCall {
            name: "==".to_owned(),
            args: vec![left, right],
            return_type: Type::basic("bool"),
        })
    }

    pub fn and(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        if !self.typ().is_bool() || !other.typ().is_bool() {
            return Err(TypeError {
                message: format!(
                    "Cannot perform logical and on non-bool types {} and {}",
                    self.typ(),
                    other.typ()
                ),
            });
        }
        Ok(TExpr::FunctionCall {
            name: "&&".to_owned(),
            args: vec![self.clone(), other.clone()],
            return_type: Type::basic("bool"),
        })
    }

    pub fn seq_at(&self, index: &TExpr) -> Result<TExpr, TypeError> {
        if self.typ().is_empty_seq() {
            return Err(TypeError {
                message: "Cannot index into an empty sequence".to_owned(),
            });
        }
        if let Some(elem_type) = self.typ().get_named_seq() {
            Ok(TExpr::FunctionCall {
                name: "seq_at".to_owned(),
                args: vec![self.clone(), index.clone()],
                return_type: elem_type.clone(),
            })
        } else {
            return Err(TypeError {
                message: format!("seq_at called on non-sequence type {}", self.typ()),
            });
        }
    }

    pub fn seq_len(&self) -> Result<TExpr, TypeError> {
        if self.typ().is_empty_seq() {
            return Ok(TExpr::Literal(Literal::U64(0)));
        }
        if !self.typ().is_named_seq() {
            return Err(TypeError {
                message: format!("seq_len called on non-sequence type {}", self.typ()),
            });
        }
        Ok(TExpr::FunctionCall {
            name: "seq_len".to_owned(),
            args: vec![self.clone()],
            return_type: Type::basic("int"),
        })
    }

    pub fn seq_map(&self, f: &TExpr) -> Result<TExpr, TypeError> {
        if self.typ().is_empty_seq() {
            // TODO: add type information gleaned from f?
            return Ok(self.clone());
        }
        if let Some(elem_type) = self.typ().get_named_seq() {
            let ret_type = f.typ().call_lambda(from_ref(elem_type))?;
            Ok(TExpr::FunctionCall {
                name: "seq_map".to_owned(),
                args: vec![self.clone(), f.clone()],
                return_type: Type {
                    name: "Seq".to_owned(),
                    type_args: vec![TypeArg::Type(ret_type)],
                },
            })
        } else {
            return Err(TypeError {
                message: format!("seq_map called on non-sequence type {}", self.typ()),
            });
        }
    }

    pub fn seq_foldl(&self, f: &TExpr, initial: &TExpr) -> Result<TExpr, TypeError> {
        if self.typ().is_empty_seq() {
            return Ok(initial.clone());
        }
        if let Some(elem_type) = self.typ().get_named_seq() {
            let return_type = f.typ().call_lambda(&[initial.typ(), elem_type.clone()])?;
            if !initial.typ().is_subtype_of(&return_type) {
                return Err(TypeError {
                    message: format!(
                        "Initial value type {} is not compatible with fold function return type {}",
                        initial.typ(),
                        return_type
                    ),
                });
            }
            if !f
                .typ()
                .call_lambda(&[return_type.clone(), elem_type.clone()])?
                .is_subtype_of(&return_type)
            {
                return Err(TypeError {
                    message: format!(
                        "Fold function return type {} is not compatible with fold function argument type {}",
                        return_type, elem_type
                    ),
                });
            }
            Ok(TExpr::FunctionCall {
                name: "seq_foldl".to_owned(),
                args: vec![self.clone(), f.clone(), initial.clone()],
                return_type,
            })
        } else {
            return Err(TypeError {
                message: format!("seq_foldl called on non-sequence type {}", self.typ()),
            });
        }
    }

    pub fn seq_all(&self, predicate: &TExpr) -> Result<TExpr, TypeError> {
        if self.typ().is_empty_seq() {
            return Ok(TExpr::Literal(Literal::Bool(true)));
        }
        if let Some(elem_type) = self.typ().get_named_seq() {
            if !predicate
                .typ()
                .call_lambda(from_ref(&elem_type))?
                .is_subtype_of(&Type::basic("bool"))
            {
                return Err(TypeError {
                    message: format!(
                        "Predicate function does not return bool for element type {}",
                        elem_type
                    ),
                });
            }
            self.seq_map(predicate)?
                .seq_foldl(&TEnv::and_lambda(), &TExpr::Literal(Literal::Bool(true)))
        } else {
            return Err(TypeError {
                message: format!("seq_all called on non-sequence type {}", self.typ()),
            });
        }
    }
}

impl Expr {
    fn type_check(&self, env: &mut TEnv) -> Result<TExpr, TypeError> {
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
                let overloaded = env
                    .functions
                    .get(name)
                    .ok_or(TypeError {
                        message: format!("Undefined function: {}", name),
                    })?
                    .clone();
                let targs = args
                    .iter()
                    .map(|a| a.type_check(env))
                    .collect::<Result<Vec<TExpr>, TypeError>>()?;
                let ret_type = overloaded.lookup_return_type(
                    &targs.iter().map(|a| a.typ()).collect::<Vec<Type>>(),
                )?;
                return Ok(TExpr::FunctionCall {
                        name: name.to_owned(),
                        args: targs,
                        return_type: ret_type,
                    });
            }
            Expr::Semicolon(stmt, expr) => {
                let tstmt = stmt.type_check(env)?;
                let texpr = expr.type_check(env)?;
                Ok(TExpr::Semicolon(Box::new(tstmt.clone()), Box::new(texpr)))
            }
            Expr::Sequence(elems) => {
                if elems.is_empty() {
                    Ok(TExpr::EmptySequence)
                } else {
                    let telems = elems
                        .iter()
                        .map(|e| e.type_check(env))
                        .collect::<Result<Vec<TExpr>, TypeError>>()?;
                    let first_type = telems[0].typ();
                    for te in &telems[1..] {
                        if te.typ() != first_type {
                            return Err(TypeError {
                                message: "All elements of the sequence must have the same type"
                                    .to_owned(),
                            });
                        }
                    }
                    Ok(TExpr::Sequence {
                        elements: telems,
                        elem_type: first_type,
                    })
                }
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
                    Ok(TExpr::FunctionCall {
                        name: "+".to_owned(),
                        args: vec![left.clone(), right.clone()],
                        return_type: Type::basic("int"),
                    })
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
                    Ok(TExpr::FunctionCall {
                        name: "-".to_owned(),
                        args: vec![left.clone(), right.clone()],
                        return_type: Type::basic("int"),
                    })
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
                let te = e.type_check(env)?;
                Ok(TStmt::Expr(te))
            }
            Stmt::Let { name, value } => {
                let tvalue = value.type_check(env)?;
                let vtype = tvalue.typ();
                env.variables.insert(name.clone(), vtype.clone());
                Ok(TStmt::Let {
                    name: name.clone(),
                    typ: vtype,
                    mutable: false,
                    type_declared: false,
                    value: tvalue,
                })
            }
            Stmt::LetMut { name, typ, value } => {
                let tvalue = value.type_check(env)?;
                if !tvalue.typ().compatible_with(&typ) {
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
                let tvalue = value.type_check(env)?;
                let var_type = env.variables.get(name).ok_or(TypeError {
                    message: format!("Undefined variable: {}", name),
                })?;
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

impl FuncDef {
    fn decl(&self) -> Result<TOverloadedFunc, TypeError> {
        let mut arg_types = vec![];
        for a in &self.args {
            arg_types.push(a.arg_type.clone());
        }
        let return_type = self.return_type.clone();
        Ok(TOverloadedFunc::simple(&arg_types, &return_type))
    }

    fn type_check(&self, env: &mut TEnv) -> Result<TFuncDef, TypeError> {
        let mut local_env = env.clone();
        let decl = &env
            .functions
            .get(&self.name)
            .ok_or(TypeError {
                message: format!(
                    "Function {} not found in environment during type checking",
                    self.name
                ),
            })?
            .extract_single()?;
        assert!(decl.arg_types.len() == self.args.len());
        for (a, t) in self.args.iter().zip(&decl.arg_types) {
            if local_env.variables.contains_key(&a.name) {
                return Err(TypeError {
                    message: format!("Duplicate argument name: {}", a.name),
                });
            }
            local_env.variables.insert(a.name.clone(), t.clone());
        }
        let args_env = local_env.clone();
        let tbody = self.body.type_check(&mut local_env)?;
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
        let sees = self.sees.clone();
        preconditions.extend(
            self.preconditions
                .iter()
                .map(|p| p.type_check(&mut args_env.clone()))
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
                .map(|p| p.type_check(&mut post_args_env))
                .collect::<Result<Vec<TExpr>, TypeError>>()?,
        );

        let args = self
            .args
            .iter()
            .zip(&decl.arg_types)
            .map(|(a, t)| Arg {
                name: a.name.clone(),
                arg_type: t.clone(),
            })
            .collect::<Vec<_>>();
        Ok(TFuncDef {
            name: self.name.clone(),
            args,
            return_type: decl.return_type.clone(),
            return_name: self.return_name.clone().unwrap_or_else(||"__ret__".to_owned()),
            preconditions,
            postconditions,
            sees,
            body: tbody,
        })
    }
}

impl TEnv {
    fn and_lambda() -> TExpr {
        let var0 = "__item0__".to_owned();
        let var1 = "__item1__".to_owned();
        let v0 = TExpr::Variable {
            name: var0.clone(),
            typ: Type::basic("bool"),
        };
        let v1 = TExpr::Variable {
            name: var1.clone(),
            typ: Type::basic("bool"),
        };
        let body = v0.and(&v1).unwrap();

        TExpr::Lambda {
            args: vec![
                Arg {
                    name: var0.clone(),
                    arg_type: Type::basic("bool"),
                },
                Arg {
                    name: var1.clone(),
                    arg_type: Type::basic("bool"),
                },
            ],
            body: Box::new(body),
        }
    }
}

impl SourceFile {
    pub fn type_check(&self) -> Result<TSourceFile, TypeError> {
        let mut env = TEnv {
            variables: HashMap::new(),
            functions: builtins(),
        };

        // env.functions.insert("seq_at".to_owned(), TOverloadedFunc::Finite(vec![]));
        // env.functions.insert("seq_len".to_owned(), TOverloadedFunc::Finite(vec![]));

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
