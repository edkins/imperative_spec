use crate::{
    check::{ztype_ast::TExpr, ztype_inference::TypeError},
    syntax::ast::{Arg, Literal, Type, TypeArg},
};
use std::slice::from_ref;

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
    pub fn zero() -> TExpr {
        TExpr::Literal(Literal::U64(0))
    }

    pub fn eq(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        if !self.typ().compatible_with(&other.typ()) {
            return Err(TypeError {
                message: format!(
                    "Cannot compare equality of incompatible types {} and {}",
                    self.typ(),
                    other.typ()
                ),
            });
        }
        Ok(TExpr::FunctionCall {
            name: "==".to_owned(),
            args: vec![self.clone(), other.clone()],
            return_type: Type::basic("bool"),
            optimizations: vec![], // TODO: add optimizations for eq and ne?
        })
    }

    pub fn ne(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        if !self.typ().compatible_with(&other.typ()) {
            return Err(TypeError {
                message: format!(
                    "Cannot compare inequality of incompatible types {} and {}",
                    self.typ(),
                    other.typ()
                ),
            });
        }
        Ok(TExpr::FunctionCall {
            name: "!=".to_owned(),
            args: vec![self.clone(), other.clone()],
            return_type: Type::basic("bool"),
            optimizations: vec![],
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
            optimizations: vec![],
        })
    }

    #[allow(dead_code)]
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
                optimizations: vec![],
            })
        } else {
            Err(TypeError {
                message: format!("seq_at called on non-sequence type {}", self.typ()),
            })
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
            optimizations: vec![],
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
                optimizations: vec![],
            })
        } else {
            Err(TypeError {
                message: format!("seq_map called on non-sequence type {}", self.typ()),
            })
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
                optimizations: vec![],
            })
        } else {
            Err(TypeError {
                message: format!("seq_foldl called on non-sequence type {}", self.typ()),
            })
        }
    }

    pub fn seq_all(&self, predicate: &TExpr) -> Result<TExpr, TypeError> {
        if self.typ().is_empty_seq() {
            return Ok(TExpr::Literal(Literal::Bool(true)));
        }
        if let Some(elem_type) = self.typ().get_named_seq() {
            if !predicate
                .typ()
                .call_lambda(from_ref(elem_type))?
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
                .seq_foldl(&and_lambda(), &TExpr::Literal(Literal::Bool(true)))
        } else {
            Err(TypeError {
                message: format!("seq_all called on non-sequence type {}", self.typ()),
            })
        }
    }

    pub fn add(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        if !self.typ().is_int() || !other.typ().is_int() {
            return Err(TypeError {
                message: format!(
                    "Cannot perform addition on non-int types {} and {}",
                    self.typ(),
                    other.typ()
                ),
            });
        }
        Ok(TExpr::FunctionCall {
            name: "+".to_owned(),
            args: vec![self.clone(), other.clone()],
            return_type: Type::basic("int"),
            optimizations: vec![],
        })
    }

    pub fn sub(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        if !self.typ().is_int() || !other.typ().is_int() {
            return Err(TypeError {
                message: format!(
                    "Cannot perform subtraction on non-int types {} and {}",
                    self.typ(),
                    other.typ()
                ),
            });
        }
        Ok(TExpr::FunctionCall {
            name: "-".to_owned(),
            args: vec![self.clone(), other.clone()],
            return_type: Type::basic("int"),
            optimizations: vec![],
        })
    }

    pub fn ge(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        if !self.typ().is_int() || !other.typ().is_int() {
            return Err(TypeError {
                message: format!(
                    "Cannot perform greater-equal comparison on non-int types {} and {}",
                    self.typ(),
                    other.typ()
                ),
            });
        }
        Ok(TExpr::FunctionCall {
            name: ">=".to_owned(),
            args: vec![self.clone(), other.clone()],
            return_type: Type::basic("bool"),
            optimizations: vec![],
        })
    }

    pub fn le(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        if !self.typ().is_int() || !other.typ().is_int() {
            return Err(TypeError {
                message: format!(
                    "Cannot perform less-equal comparison on non-int types {} and {}",
                    self.typ(),
                    other.typ()
                ),
            });
        }
        Ok(TExpr::FunctionCall {
            name: "<=".to_owned(),
            args: vec![self.clone(), other.clone()],
            return_type: Type::basic("bool"),
            optimizations: vec![],
        })
    }
}

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
