use crate::syntax::ast::{AssignOp, CodePos, Expr, ExprInfo, ExprKind, Literal, Type};

impl Literal {
    pub fn as_expr(self) -> Expr {
        Expr::Expr {
            kind: ExprKind::Literal { literal: self },
            args: vec![],
            type_instantiations: vec![],
            info: ExprInfo::default(),
        }
    }
}

pub fn untyped_var(name: String) -> Expr {
    Expr::Variable {
        name,
        info: ExprInfo::default(),
    }
}

pub fn immut_function_call(func_name: &str, args: Vec<Expr>) -> Expr {
    let falses = vec![false; args.len()];
    function_call(func_name, args, falses)
}

pub fn function_call(func_name: &str, args: Vec<Expr>, mutable_args: Vec<bool>) -> Expr {
    assert!(args.len() == mutable_args.len());
    Expr::Expr {
        kind: ExprKind::Function {
            name: func_name.to_owned(),
            mutable_args,
        },
        args,
        type_instantiations: vec![],
        info: ExprInfo::default(),
    }
}

pub fn tuple(elems: Vec<Expr>) -> Expr {
    Expr::Expr {
        kind: ExprKind::RoundSequence { len: elems.len() },
        args: elems,
        type_instantiations: vec![],
        info: ExprInfo::default(),
    }
}

pub fn vector(elems: Vec<Expr>) -> Expr {
    Expr::Expr {
        kind: ExprKind::SquareSequence { len: elems.len() },
        args: elems,
        type_instantiations: vec![],
        info: ExprInfo::default(),
    }
}

pub fn let_expr(
    name: String,
    mutable: bool,
    typ: Option<Type>,
    value: Expr,
    body: Expr,
) -> Expr {
    Expr::Let {
        name,
        mutable,
        typ,
        value: Box::new(value),
        body: Box::new(body),
        info: ExprInfo::default(),
    }
}

impl AssignOp {
    pub fn function_name(&self) -> &'static str {
        match self {
            AssignOp::Assign => "=",
            AssignOp::AddAssign => "+=",
            AssignOp::SubAssign => "-=",
            AssignOp::MulAssign => "*=",
        }
    }
}

pub fn assign(var: Expr, op: AssignOp, value: Expr) -> Expr {
    function_call(
        op.function_name(),
        vec![var, value],
        vec![true, false],
    )
}

impl Expr {
    pub fn get_info(&self) -> &ExprInfo {
        match self {
            Expr::Expr { info, .. } => info,
            Expr::Variable { info, .. } => info,
            Expr::Lambda { info, .. } => info,
            Expr::Let { info, .. } => info,
        }
    }

    pub fn get_info_mut(&mut self) -> &mut ExprInfo {
        match self {
            Expr::Expr { info, .. } => info,
            Expr::Variable { info, .. } => info,
            Expr::Lambda { info, .. } => info,
            Expr::Let { info, .. } => info,
        }
    }

    pub fn between(mut self, remainder0: &str, remainder1: &str) -> Self {
        let info = self.get_info_mut();
        let pos = CodePos::betweem(remainder0, remainder1);
        info.pos = Some(pos);
        self
    }

    pub fn semicolon(self, other: Expr) -> Expr {
        immut_function_call(";", vec![self, other])
    }

    // pub fn dot_at(self, index: usize) -> Expr {
    //     Expr::Expr {
    //         kind: ExprKind::TupleAt { index },
    //         args: vec![self],
    //         info: ExprInfo::default(),
    //     }
    // }

    pub fn square_bracket_at(self, index: Expr) -> Expr {
        Expr::Expr {
            kind: ExprKind::UnknownSequenceAt,
            args: vec![self, index],
            type_instantiations: vec![],
            info: ExprInfo::default(),
        }
    }
}