use crate::{check::{ztype_ast::TExpr, ztype_inference::{TypeError, big_and}}, syntax::ast::{Arg, Bound, Literal, Type, TypeArg}};

impl Type {
    // pub fn type_assertions_on_name(&self, more_general_type: &Type, name: &str) -> Vec<TExpr> {
    //     assert!(self.is_subtype_of(more_general_type));
    //     let expr = TExpr::Variable {
    //         name: name.to_owned(),
    //         typ: more_general_type.clone(),
    //     };
    //     self.type_assertions(expr)
    // }

    pub fn type_assertions(&self, expr: TExpr) -> Vec<TExpr> {
        match self.name.as_str() {
            "int" | "nat" | "z8" | "z16" | "z32" | "z64" | "i8" | "i16" | "i32" | "i64" | "u8"
            | "u16" | "u32" | "u64" => {
                let (lower, upper) = lookup_int_bounds(&self.name);
                bounds_to_expr(lower, upper, expr)
            }
            _ => vec![],
        }
    }

    pub fn is_bool(&self) -> bool {
        self.name.as_str() == "bool" && self.type_args.is_empty()
    }

    pub fn is_str(&self) -> bool {
        self.name.as_str() == "str" && self.type_args.is_empty()
    }

    pub fn is_void(&self) -> bool {
        self.name.as_str() == "void" && self.type_args.is_empty()
    }

    pub fn is_empty_seq(&self) -> bool {
        self.name.as_str() == "EmptySeq" && self.type_args.is_empty()
    }

    pub fn is_named_seq(&self) -> bool {
        self.name.as_str() == "Seq" && self.type_args.len() == 1
    }

    pub fn is_int(&self) -> bool {
        self.type_args.is_empty() && matches!(
            self.name.as_str(),
            "int" | "nat" | "z8" | "z16" | "z32" | "z64" | "i8" | "i16" | "i32" | "i64" | "u8"
                | "u16"
                | "u32"
                | "u64"
        )
    }

    pub fn discards_information(&self) -> bool {
        matches!(self.name.as_str(), "z8" | "z16" | "z32" | "z64")
    }

    pub fn is_subtype_of(&self, other: &Type) -> bool {
        if self == other {
            return true;
        }
        if self.is_empty_seq() && other.is_named_seq() {
            return true;
        }
        if self.is_int() && other.is_int() && !self.discards_information() && !other.discards_information() {
            let (self_min, self_max) = lookup_int_bounds(&self.name);
            let (other_min, other_max) = lookup_int_bounds(&other.name);
            if self_min >= other_min && self_max <= other_max {
                return true;
            }
        }
        false
    }

    pub fn no_type_args(&self) -> Result<(), TypeError> {
        if !self.type_args.is_empty() {
            return Err(TypeError {
                message: format!("Type {} should not have type arguments", self),
            });
        }
        Ok(())
    }

    pub fn one_type_arg(&self) -> Result<Type, TypeError> {
        if self.type_args.len() != 1 {
            return Err(TypeError {
                message: format!("Type {} should have exactly one type argument", self),
            });
        }
        match &self.type_args[0] {
            TypeArg::Type(t) => Ok(t.clone()),
            _ => Err(TypeError {
                message: format!("Type argument of {} is not a Type", self),
            }),
        }
    }

    pub fn compatible_with(&self, other: &Type) -> bool {
        if self == other {
            return true;
        }
        if self.is_int() && other.is_int() {
            return true;
        }
        if self.is_empty_seq() && other.is_named_seq() {
            return true;
        }
        if self.is_named_seq() && other.is_empty_seq() {
            return true;
        }
        if self.is_named_seq() && other.is_named_seq() {
            let self_arg = self.one_type_arg().unwrap();
            let other_arg = other.one_type_arg().unwrap();
            return self_arg.compatible_with(&other_arg);
        }
        false
    }

    fn type_lambda(&self, more_general_type: &Type) -> Option<TExpr> {
        assert!(self.is_subtype_of(more_general_type));
        let var = TExpr::Variable {
            name: "__item__".to_owned(),
            typ: more_general_type.clone(),
        };
        let conds = self.type_assertions(var);
        if conds.is_empty() {
            return None;
        }
        Some(TExpr::Lambda {
            args: vec![Arg {
                name: "__item__".to_owned(),
                arg_type: more_general_type.clone(),
            }],
            body: Box::new(big_and(&conds).unwrap()),
        })
    }
}


fn lookup_int_bounds(name: &str) -> (Bound, Bound) {
    match name {
        "i8" => (Bound::I64(-128), Bound::I64(127)),
        "i16" => (Bound::I64(-32768), Bound::I64(32767)),
        "i32" => (Bound::I64(-2147483648), Bound::I64(2147483647)),
        "i64" => (Bound::I64(i64::MIN), Bound::I64(i64::MAX)),
        "u8" => (Bound::U64(0), Bound::U64(255)),
        "u16" => (Bound::U64(0), Bound::U64(65535)),
        "u32" => (Bound::U64(0), Bound::U64(4294967295)),
        "u64" => (Bound::U64(0), Bound::U64(u64::MAX)),
        "z8" | "z16" | "z32" | "z64" | "int" => (Bound::MinusInfinity, Bound::PlusInfinity),
        "nat" => (Bound::U64(0), Bound::PlusInfinity),
        _ => panic!("Unknown type for bounds lookup: {}", name),
    }
}

fn bounds_to_expr(lower: Bound, upper: Bound, expr: TExpr) -> Vec<TExpr> {
    let mut result = vec![];
    match lower {
        Bound::MinusInfinity => {}
        Bound::I64(i) => result.push(TExpr::FunctionCall {
            name: ">=".to_owned(),
            args: vec![expr.clone(), TExpr::Literal(Literal::I64(i))],
            return_type: Type::basic("bool"),
        }),
        Bound::U64(u) => result.push(TExpr::FunctionCall {
            name: ">=".to_owned(),
            args: vec![expr.clone(), TExpr::Literal(Literal::U64(u))],
            return_type: Type::basic("bool"),
        }),
        Bound::PlusInfinity => unreachable!(),
    }
    match upper {
        Bound::PlusInfinity => {}
        Bound::I64(i) => result.push(TExpr::FunctionCall {
            name: "<=".to_owned(),
            args: vec![expr.clone(), TExpr::Literal(Literal::I64(i))],
            return_type: Type::basic("bool"),
        }),
        Bound::U64(u) => result.push(TExpr::FunctionCall {
            name: "<=".to_owned(),
            args: vec![expr.clone(), TExpr::Literal(Literal::U64(u))],
            return_type: Type::basic("bool"),
        }),
        Bound::MinusInfinity => unreachable!(),
    }
    result
}
