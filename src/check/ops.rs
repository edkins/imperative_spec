use crate::{
    check::{builtins::known_builtin, types::TypeError},
    syntax::ast::{Arg, Expr, ExprInfo, ExprKind, FuncDef, Literal, Type},
};
use std::slice::from_ref;

pub fn big_and(exprs: &[Expr]) -> Result<Expr, TypeError> {
    if exprs.is_empty() {
        return Ok(Literal::Bool(true).typed_expr());
    }
    let mut result = exprs[0].clone();
    for e in &exprs[1..] {
        result = result.and(e)?;
    }
    Ok(result)
}

impl FuncDef {
    pub fn pmake_func_call(
        &self,
        args: &[Expr],
        type_instantiations: &[Type],
    ) -> Result<Expr, TypeError> {
        assert!(self.type_params.len() == type_instantiations.len());
        Ok(Expr::Expr {
            kind: ExprKind::Function {
                name: self.name.to_owned(),
                type_instantiations: type_instantiations.to_owned(),
                mutable_args: self
                    .args
                    .iter()
                    .map(|arg| arg.mutable)
                    .collect(),
            },
            args: args.to_owned(),
            info: ExprInfo {
                typ: Some(self.return_type
                    .instantiate(&self.type_params, type_instantiations)?),
                pos: None,
                id: "".to_owned(),
                preconditions_checked: false,
            },
        })
    }

    pub fn make_func_call(&self, args: &[Expr]) -> Result<Expr, TypeError> {
        self.pmake_func_call(args, &[])
    }
}

/// Make this a trait (it's only implemented by one thing) to avoid accidentally
/// calling it from builtins.rs
pub trait Ops: Sized {
    fn eq(&self, other: &Self) -> Result<Self, TypeError>;
    #[allow(dead_code)]
    fn ne(&self, other: &Self) -> Result<Self, TypeError>;
    fn and(&self, other: &Self) -> Result<Self, TypeError>;
    fn implies(&self, other: &Self) -> Result<Self, TypeError>;
    fn seq_len(&self) -> Result<Self, TypeError>;
    fn seq_map(&self, f: &Self) -> Result<Self, TypeError>;
    fn seq_foldl(&self, f: &Self, initial: &Self) -> Result<Self, TypeError>;
    fn seq_all(&self, predicate: &Self) -> Result<Self, TypeError>;
    // fn seq_at(&self, index: &Self) -> Result<Self, TypeError>;
    fn add(&self, other: &Self) -> Result<Self, TypeError>;
    fn sub(&self, other: &Self) -> Result<Self, TypeError>;
    fn mul(&self, other: &Self) -> Result<Self, TypeError>;
    fn ge(&self, other: &Self) -> Result<Self, TypeError>;
    fn le(&self, other: &Self) -> Result<Self, TypeError>;
}

impl Expr {
    pub fn zero() -> Expr {
        Literal::U64(0).typed_expr()
    }

    pub fn tuple_at(&self, index: usize) -> Result<Expr, TypeError> {
        if self.typ().is_round_seq() {
            if index as u64 <= self.typ().get_round_seq_length().unwrap() {
                Ok(Expr::Expr {
                    kind: ExprKind::TupleAt {len: self.typ().get_round_seq_length().unwrap() as usize, index},
                    args: vec![self.clone()],
                    info: ExprInfo {
                        typ: Some(self.typ().get_round_elem_type(index as u64).unwrap().clone()),
                        pos: None,
                        id: "".to_owned(),
                        preconditions_checked: false,
                    },
                })
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
                    index,
                    self.typ()
                ),
            })
        }
    }

    // pub fn cast(&self, to_type: Type) -> TExpr {
    //     TExpr::Cast {
    //         expr: Box::new(self.clone()),
    //         to_type,
    //     }
    // }
}

impl Ops for Expr {
    fn eq(&self, other: &Expr) -> Result<Expr, TypeError> {
        known_builtin("==").pmake_func_call(&[self.clone(), other.clone()], &[self.typ()])
    }

    fn ne(&self, other: &Expr) -> Result<Expr, TypeError> {
        known_builtin("!=").pmake_func_call(&[self.clone(), other.clone()], &[self.typ()])
    }

    fn and(&self, other: &Expr) -> Result<Expr, TypeError> {
        // TODO: short-circuiting
        known_builtin("&&").make_func_call(&[self.clone(), other.clone()])
    }

    fn implies(&self, other: &Expr) -> Result<Expr, TypeError> {
        known_builtin("==>").make_func_call(&[self.clone(), other.clone()])
    }

    fn seq_len(&self) -> Result<Expr, TypeError> {
        known_builtin("len")
            .pmake_func_call(from_ref(self), &[self.typ().uniform_square_elem_type()?])
    }

    fn seq_map(&self, f: &Expr) -> Result<Expr, TypeError> {
        let ftype = f.typ();
        assert!(ftype.name == "Lambda");
        assert!(ftype.type_args.len() == 2);
        assert!(ftype.type_args[0].as_type()? == self.typ().uniform_square_elem_type()?);
        known_builtin("seq_map").pmake_func_call(
            &[self.clone(), f.clone()],
            &[ftype.type_args[0].as_type()?, ftype.type_args[1].as_type()?],
        )
    }

    fn seq_foldl(&self, f: &Expr, initial: &Expr) -> Result<Expr, TypeError> {
        let ftype = f.typ();
        assert!(ftype.name == "Lambda");
        assert!(ftype.type_args.len() == 3);
        assert!(ftype.type_args[0].as_type()? == initial.typ());
        assert!(ftype.type_args[1].as_type()? == self.typ().uniform_square_elem_type()?);
        assert!(ftype.type_args[2].as_type()? == ftype.type_args[0].as_type()?);
        known_builtin("seq_foldl").pmake_func_call(
            &[self.clone(), f.clone(), initial.clone()],
            &[ftype.type_args[0].as_type()?, ftype.type_args[1].as_type()?],
        )
    }

    fn seq_all(&self, predicate: &Expr) -> Result<Expr, TypeError> {
        let result = self
            .seq_map(predicate)?
            .seq_foldl(&and_lambda(), &Literal::Bool(true).typed_expr());
        result
    }

    // fn seq_at(&self, index: &Expr) -> Result<Expr, TypeError> {
    //     known_builtin("seq_at").make_func_call(&[self.clone(), index.clone()])
    // }

    fn add(&self, other: &Expr) -> Result<Expr, TypeError> {
        known_builtin("+").make_func_call(&[self.clone(), other.clone()])
    }

    fn sub(&self, other: &Expr) -> Result<Expr, TypeError> {
        known_builtin("-").make_func_call(&[self.clone(), other.clone()])
    }

    fn mul(&self, other: &Expr) -> Result<Expr, TypeError> {
        known_builtin("*").make_func_call(&[self.clone(), other.clone()])
    }

    fn ge(&self, other: &Expr) -> Result<Expr, TypeError> {
        known_builtin(">=").make_func_call(&[self.clone(), other.clone()])
    }

    fn le(&self, other: &Expr) -> Result<Expr, TypeError> {
        known_builtin("<=").make_func_call(&[self.clone(), other.clone()])
    }
}

fn and_lambda() -> Expr {
    let var0 = "__item0__".to_owned();
    let var1 = "__item1__".to_owned();
    let v0 = Type::basic("bool").var(&var0);
    let v1 = Type::basic("bool").var(&var1);
    let body = v0.and(&v1).unwrap();

    Expr::Lambda {
        args: vec![
            Arg {
                name: var0.clone(),
                mutable: false,
                arg_type: Type::basic("bool"),
            },
            Arg {
                name: var1.clone(),
                mutable: false,
                arg_type: Type::basic("bool"),
            },
        ],
        body: Box::new(body),
        info: ExprInfo {
            typ: Some(
                Type::lambda(&[Type::basic("bool"),Type::basic("bool")], &Type::basic("bool"))
            ),
            pos: None,
            id: "".to_owned(),
            preconditions_checked: false,
        },
    }
}
