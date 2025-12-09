use crate::{
    check::{
        builtins::known_builtin,
        ztype_ast::{TExpr, TFuncDef},
        ztype_inference::TypeError,
    },
    syntax::ast::{Arg, Literal, Type},
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

impl TFuncDef {
    pub fn make_func_call(&self, args: &[TExpr]) -> Result<TExpr, TypeError> {
        let concrete =
            self.instantiate_from_types(&args.iter().map(|a| a.typ()).collect::<Vec<Type>>())?;
        Ok(TExpr::FunctionCall {
            name: self.name.to_owned(),
            args: args.to_owned(),
            return_type: concrete.return_type.clone(),
            optimizations: concrete.optimizations.clone(),
        })
    }
}

/// Make this a trait (it's only implemented by one thing) to avoid accidentally
/// calling it from builtins.rs
pub trait Ops: Sized {
    fn eq(&self, other: &Self) -> Result<Self, TypeError>;
    #[allow(dead_code)]
    fn ne(&self, other: &Self) -> Result<Self, TypeError>;
    fn and(&self, other: &Self) -> Result<Self, TypeError>;
    fn seq_len(&self) -> Result<Self, TypeError>;
    fn seq_map(&self, f: &Self) -> Result<Self, TypeError>;
    fn seq_foldl(&self, f: &Self, initial: &Self) -> Result<Self, TypeError>;
    fn seq_all(&self, predicate: &Self) -> Result<Self, TypeError>;
    // fn seq_at(&self, index: &Self) -> Result<Self, TypeError>;
    fn add(&self, other: &Self) -> Result<Self, TypeError>;
    fn sub(&self, other: &Self) -> Result<Self, TypeError>;
    fn ge(&self, other: &Self) -> Result<Self, TypeError>;
    fn le(&self, other: &Self) -> Result<Self, TypeError>;
}

impl TExpr {
    pub fn zero() -> TExpr {
        TExpr::Literal(Literal::U64(0))
    }

    pub fn tuple_at(&self, index: u64) -> Result<TExpr, TypeError> {
        if self.typ().is_round_seq() {
            if index <= self.typ().get_round_seq_length().unwrap() {
                Ok(TExpr::TupleAt { tuple: Box::new(self.clone()), index })
            } else {
                Err(TypeError {
                    message: format!(
                        "Index {} out of bounds for tuple of length {}",
                        index,
                        self.typ().get_round_seq_length().unwrap()
                    ),
                })
            }
        } else {
            Err(TypeError {
                message: format!(
                    "Cannot access index {} of non-tuple type {}",
                    index, self.typ()
                ),
            })
        }
    }

    pub fn cast(&self, to_type: Type) -> TExpr {
        TExpr::Cast {
            expr: Box::new(self.clone()),
            to_type,
        }
    }
}

impl Ops for TExpr {
    fn eq(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        known_builtin("==").make_func_call(&[self.clone(), other.clone()])
    }

    fn ne(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        known_builtin("!=").make_func_call(&[self.clone(), other.clone()])
    }

    fn and(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        // TODO: short-circuiting
        known_builtin("&&").make_func_call(&[self.clone(), other.clone()])
    }

    fn seq_len(&self) -> Result<TExpr, TypeError> {
        known_builtin("seq_len").make_func_call(from_ref(self))
    }

    fn seq_map(&self, f: &TExpr) -> Result<TExpr, TypeError> {
        known_builtin("seq_map").make_func_call(&[self.clone(), f.clone()])
    }

    fn seq_foldl(&self, f: &TExpr, initial: &TExpr) -> Result<TExpr, TypeError> {
        known_builtin("seq_foldl").make_func_call(&[self.clone(), f.clone(), initial.clone()])
    }

    fn seq_all(&self, predicate: &TExpr) -> Result<TExpr, TypeError> {
        self.seq_map(predicate)?
            .seq_foldl(&and_lambda(), &TExpr::Literal(Literal::Bool(true)))
    }

    // fn seq_at(&self, index: &TExpr) -> Result<TExpr, TypeError> {
    //     known_builtin("seq_at").make_func_call(&[self.clone(), index.clone()])
    // }

    fn add(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        known_builtin("+").make_func_call(&[self.clone(), other.clone()])
    }

    fn sub(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        known_builtin("-").make_func_call(&[self.clone(), other.clone()])
    }

    fn ge(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        known_builtin(">=").make_func_call(&[self.clone(), other.clone()])
    }

    fn le(&self, other: &TExpr) -> Result<TExpr, TypeError> {
        known_builtin("<=").make_func_call(&[self.clone(), other.clone()])
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
