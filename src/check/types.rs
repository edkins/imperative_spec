use crate::{
    check::{ops::{Ops, big_and}, ztype_ast::TExpr, ztype_inference::TypeError},
    syntax::ast::{Arg, Bound, Literal, Type, TypeArg},
};

impl Bound {
    pub fn as_expr(&self) -> Result<TExpr, TypeError> {
        match self {
            Bound::I64(i) => Ok(TExpr::Literal(Literal::I64(*i))),
            Bound::U64(u) => Ok(TExpr::Literal(Literal::U64(*u))),
            Bound::MinusInfinity => Err(TypeError {
                message: "Cannot convert -infinity to expression".to_owned(),
            }),
            Bound::PlusInfinity => Err(TypeError {
                message: "Cannot convert +infinity to expression".to_owned(),
            }),
        }
    }
}

impl Type {
    // pub fn type_assertions_on_name(&self, more_general_type: &Type, name: &str) -> Vec<TExpr> {
    //     assert!(self.is_subtype_of(more_general_type));
    //     let expr = TExpr::Variable {
    //         name: name.to_owned(),
    //         typ: more_general_type.clone(),
    //     };
    //     self.type_assertions(expr)
    // }

    pub fn var(&self, name: &str) -> TExpr {
        TExpr::Variable {
            name: name.to_owned(),
            typ: self.clone(),
        }
    }

    pub fn most_general_type(&self, param_list: &[String]) -> Result<Type, TypeError> {
        if param_list.contains(&self.name) {
            if self.type_args.is_empty() {
                Ok(Type {
                    name: self.name.clone(),
                    type_args: vec![],
                })
            } else {
                Err(TypeError {
                    message: format!(
                        "Cannot generalize parameterized type {} with parameters",
                        self
                    ),
                })
            }
        } else if self.is_int() {
            Ok(Type::basic("int"))
        } else if let Some(elem) = self.get_named_seq() {
            let general_elem = elem.most_general_type(param_list)?;
            Ok(Type {
                name: "Seq".to_owned(),
                type_args: vec![TypeArg::Type(general_elem)],
            })
        } else {
            Ok(self.clone())
        }
    }

    pub fn condless(&self) -> bool {
        if matches!(
            self.name.as_str(),
            "int" | "z8" | "z16" | "z32" | "z64" | "str" | "bool" | "void" | "EmptySeq"
        ) && self.type_args.is_empty()
        {
            return true;
        }
        if let Some(elem) = self.get_named_seq() {
            return elem.condless();
        }
        if self.name == "Lambda" {
            for arg in &self.type_args {
                match arg {
                    TypeArg::Type(t) => {
                        if !t.condless() {
                            return false;
                        }
                    }
                    TypeArg::Bound(_) => {}
                }
            }
            return true;
        }
        false
    }

    pub fn type_assertions(
        &self,
        expr: TExpr,
        param_list: &[String],
    ) -> Result<Vec<TExpr>, TypeError> {
        match self.name.as_str() {
            "int" | "nat" | "z8" | "z16" | "z32" | "z64" | "i8" | "i16" | "i32" | "i64" | "u8"
            | "u16" | "u32" | "u64" => {
                let (lower, upper) = lookup_int_bounds(&self.name);
                Ok(bounds_to_expr(lower, upper, expr))
            }
            "Seq" | "Vec" => {
                if let &[TypeArg::Type(elem_type)] = &self.type_args.as_slice() {
                    if let Some(lambda) = elem_type
                        .type_lambda(&elem_type.most_general_type(param_list)?, param_list)?
                    {
                        Ok(vec![expr.seq_all(&lambda)?])
                    } else {
                        Ok(vec![])
                    }
                } else {
                    Err(TypeError {
                        message: format!(
                            "Type {} should have exactly one type argument",
                            self.name
                        ),
                    })
                }
            }
            "Array" => {
                if let &[TypeArg::Type(elem_type), TypeArg::Bound(array_size)] =
                    &self.type_args.as_slice()
                {
                    let size_expr = array_size.as_expr()?;
                    let mut conds = vec![expr.seq_len()?.eq(&size_expr)?];
                    if let Some(lambda) = elem_type
                        .type_lambda(&elem_type.most_general_type(param_list)?, param_list)?
                    {
                        conds.push(expr.seq_all(&lambda)?);
                    }
                    Ok(conds)
                } else {
                    Err(TypeError {
                        message: format!(
                            "Type {} should have exactly two type arguments",
                            self.name
                        ),
                    })
                }
            }
            "str" | "bool" | "void" => Ok(vec![]),
            "Lambda" => {
                if self.condless() {
                    Ok(vec![])
                } else {
                    Err(TypeError {
                        message: format!(
                            "Cannot generate type assertions for conditioned lambda type {}",
                            self
                        ),
                    })
                }
            }
            _ => Err(TypeError {
                message: format!("Unknown type for type assertions: {}", self),
            }),
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

    pub fn get_named_seq(&self) -> Option<&Type> {
        if self.is_named_seq() {
            match &self.type_args[0] {
                TypeArg::Type(t) => Some(t),
                _ => None,
            }
        } else {
            None
        }
    }

    pub fn is_named_seq(&self) -> bool {
        matches!(
            (self.name.as_str(), self.type_args.len()),
            ("Seq" | "Vec", 1) | ("Array", 2)
        )
    }

    pub fn is_int(&self) -> bool {
        self.type_args.is_empty()
            && matches!(
                self.name.as_str(),
                "int"
                    | "nat"
                    | "z8"
                    | "z16"
                    | "z32"
                    | "z64"
                    | "i8"
                    | "i16"
                    | "i32"
                    | "i64"
                    | "u8"
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
        if self.is_int()
            && other.is_int()
            && !self.discards_information()
            && !other.discards_information()
        {
            let (self_min, self_max) = lookup_int_bounds(&self.name);
            let (other_min, other_max) = lookup_int_bounds(&other.name);
            if self_min >= other_min && self_max <= other_max {
                return true;
            }
        }
        false
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
        if let Some(self_elem) = self.get_named_seq()
            && let Some(other_elem) = other.get_named_seq()
        {
            return self_elem.compatible_with(other_elem);
        }
        false
    }

    fn type_lambda(
        &self,
        more_general_type: &Type,
        param_list: &[String],
    ) -> Result<Option<TExpr>, TypeError> {
        assert!(
            self.is_subtype_of(more_general_type),
            "Type {} is not a subtype of {}",
            self,
            more_general_type
        );
        let var = TExpr::Variable {
            name: "__item__".to_owned(),
            typ: more_general_type.clone(),
        };
        let conds = self.type_assertions(var, param_list)?;
        if conds.is_empty() {
            return Ok(None);
        }
        Ok(Some(TExpr::Lambda {
            args: vec![Arg {
                name: "__item__".to_owned(),
                arg_type: more_general_type.clone(),
            }],
            body: Box::new(big_and(&conds).unwrap()),
        }))
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
        Bound::I64(i) => result.push(expr.ge(&TExpr::Literal(Literal::I64(i))).unwrap()),
        Bound::U64(u) => result.push(expr.ge(&TExpr::Literal(Literal::U64(u))).unwrap()),
        Bound::PlusInfinity => unreachable!(),
    }
    match upper {
        Bound::PlusInfinity => {}
        Bound::I64(i) => result.push(expr.le(&TExpr::Literal(Literal::I64(i))).unwrap()),
        Bound::U64(u) => result.push(expr.le(&TExpr::Literal(Literal::U64(u))).unwrap()),
        Bound::MinusInfinity => unreachable!(),
    }
    result
}
