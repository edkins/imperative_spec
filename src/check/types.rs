use crate::{
    check::{
        ops::{Ops, big_and},
        ztype_ast::TExpr,
        ztype_inference::TypeError,
    },
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

impl TypeArg {
    fn condless(&self) -> bool {
        match self {
            TypeArg::Type(t) => t.condless(),
            TypeArg::Bound(_) => true,
        }
    }

    fn as_type(&self) -> Result<Type, TypeError> {
        match self {
            TypeArg::Type(t) => Ok(t.clone()),
            TypeArg::Bound(_) => Err(TypeError {
                message: "Expected Type, found Bound".to_owned(),
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

    fn most_general_type_same_size(&self, param_list: &[String]) -> Result<Type, TypeError> {
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
        } else {
            match (self.name.as_str(), self.type_args.len()) {
                ("u8" | "i8" | "z8", 0) => Ok(Type::basic("z8")),
                ("u16" | "i16" | "z16", 0) => Ok(Type::basic("z16")),
                ("u32" | "i32" | "z32", 0) => Ok(Type::basic("z32")),
                ("u64" | "i64" | "z64", 0) => Ok(Type::basic("z64")),
                ("int" | "nat", 0) => Ok(Type::basic("int")),
                ("str", 0) => Ok(Type::basic("str")),
                ("bool", 0) => Ok(Type::basic("bool")),
                ("void", 0) => Ok(Type::basic("void")),
                ("Tuple", _) => {
                    let type_args = self.type_args.iter()
                    .map(|ta| ta.as_type().and_then(|t| t.most_general_type_same_size(param_list)))
                    .collect::<Result<Vec<Type>, TypeError>>()?;
                    Ok(Type {
                        name: "Tuple".to_owned(),
                        type_args: type_args.into_iter().map(TypeArg::Type).collect(),
                    })
                }
                ("Vec", 1) | ("Array", 2) => {
                    // ignore size for Array
                    let elem_type = self.type_args[0].as_type()?.most_general_type_same_size(param_list)?;
                    Ok(Type {
                        name: "Vec".to_owned(),
                        type_args: vec![TypeArg::Type(elem_type)],
                    })
                }
                ("Lambda", _) => {
                    // Don't mess with lambdas for now
                    Ok(self.clone())
                }
                _ => Err(TypeError {
                    message: format!(
                        "Cannot generalize unknown type {} to most general",
                        self
                    ),
                }),
            }
        }
    }

    pub fn most_general_type(&self, param_list: &[String]) -> Result<Type, TypeError> {
        if self.is_int() {
            Ok(Type::basic("int"))
        } else {
            // TODO: do we need to special-case tuples here?
            // Right now the most general form of (u32, u64) is (z32, z64) not (int, int)
            let t = self.most_general_type_same_size(param_list)?;
            Ok(t)
        }
    }

    pub fn condless(&self) -> bool {
        match (self.name.as_str(), self.type_args.len()) {
            ("int" | "z8" | "z16" | "z32" | "z64" | "str" | "bool" | "void", 0) => true,
            ("Tuple", _) => {
                assert!(self.type_args.len() > 0);
                self.type_args.iter().all(TypeArg::condless)
            }
            ("Array", 2) => self.type_args.iter().all(TypeArg::condless),
            ("Vec", 1) => self.type_args.iter().all(TypeArg::condless),
            ("Lambda", _) => {
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
                true
            }
            _ => false,
        }
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
            "Vec" | "Array" => {
                // TODO: check array lens also
                let new_type = self.most_general_type(param_list)?;
                let elem_type = self.get_uniform_square_elem_type().ok_or_else(|| TypeError{
                    message: format!(
                        "Type {} should have exactly one type argument",
                        self.name
                    ),
                })?;
                let new_elem_type = new_type.get_uniform_square_elem_type().ok_or_else(|| TypeError{
                    message: format!(
                        "Type {} should have exactly one type argument",
                        self.name
                    ),
                })?;
                if let Some(lambda) = elem_type.type_lambda(&new_elem_type, param_list)?
                {
                    Ok(vec![expr.cast(new_type).seq_all(&lambda)?])
                } else {
                    Ok(vec![])
                }
            }
            // "Array" => {
            //     if let &[TypeArg::Type(elem_type), TypeArg::Bound(array_size)] =
            //         &self.type_args.as_slice()
            //     {
            //         let size_expr = array_size.as_expr()?;
            //         let mut conds = vec![expr.seq_len()?.eq(&size_expr)?];
            //         if let Some(lambda) = elem_type
            //             .type_lambda(&elem_type.most_general_type(param_list)?, param_list)?
            //         {
            //             conds.push(expr.seq_all(&lambda)?);
            //         }
            //         Ok(conds)
            //     } else {
            //         Err(TypeError {
            //             message: format!(
            //                 "Type {} should have exactly two type arguments",
            //                 self.name
            //             ),
            //         })
            //     }
            // }
            "Tuple" => {
                let mut conds = vec![];
                let elem_types = self.get_round_elem_type_vector().ok_or(TypeError {
                    message: format!("Type {} should have only type arguments", self.name),
                })?;
                for (i, elem_type) in elem_types.iter().enumerate() {
                    let elem_expr = expr.tuple_at(i as u64)?;
                    conds.extend_from_slice(&elem_type.type_assertions(elem_expr, param_list)?);
                }
                Ok(conds)
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

    // pub fn is_empty_seq(&self) -> bool {
    //     self.name.as_str() == "EmptySeq" && self.type_args.is_empty()
    // }

    // pub fn get_named_seq(&self) -> Option<&Type> {
    //     if self.is_named_seq() {
    //         match &self.type_args[0] {
    //             TypeArg::Type(t) => Some(t),
    //             _ => None,
    //         }
    //     } else {
    //         None
    //     }
    // }

    pub fn is_square_seq(&self) -> bool {
        (self.name.as_str() == "Array" && self.type_args.len() == 2)
            || (self.name.as_str() == "Vec" && self.type_args.len() == 1)
    }

    pub fn is_round_seq(&self) -> bool {
        // don't include void here
        self.name == "Tuple"
    }

    pub fn get_uniform_square_elem_type(&self) -> Option<&Type> {
        if self.name == "Array" && self.type_args.len() == 2 {
            match &self.type_args[0] {
                TypeArg::Type(t) => Some(t),
                _ => None,
            }
        } else if self.name == "Vec" && self.type_args.len() == 1 {
            match &self.type_args[0] {
                TypeArg::Type(t) => Some(t),
                _ => None,
            }
        } else {
            None
        }
    }

    // pub fn get_square_elem_type(&self, i: u64) -> Option<&Type> {
    //     self.get_uniform_square_elem_type()
    // }

    pub fn get_round_elem_type(&self, i: u64) -> Option<&Type> {
        if self.name == "Tuple" {
            match self.type_args.get(i as usize) {
                Some(TypeArg::Type(t)) => Some(t),
                _ => None,
            }
        } else {
            None
        }
    }

    pub fn get_either_elem_type(&self, i: u64) -> Option<&Type> {
        if self.is_square_seq() {
            self.get_uniform_square_elem_type()
        } else {
            self.get_round_elem_type(i)
        }
    }

    pub fn get_round_elem_type_vector(&self) -> Option<Vec<&Type>> {
        if self.name == "Tuple" {
            let mut result = vec![];
            for ta in &self.type_args {
                match ta {
                    TypeArg::Type(t) => result.push(t),
                    _ => return None,
                }
            }
            Some(result)
        } else {
            None
        }
    }

    // pub fn get_square_seq_length(&self) -> Option<u64> {
    //     if self.name == "Array" && self.type_args.len() == 2 {
    //         match &self.type_args[1] {
    //             TypeArg::Bound(Bound::U64(u)) => Some(*u),
    //             _ => None,
    //         }
    //     } else {
    //         None
    //     }
    // }

    pub fn get_round_seq_length(&self) -> Option<u64> {
        if self.name == "Tuple" {
            Some(self.type_args.len() as u64)
        } else {
            None
        }
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

    // pub fn discards_information(&self) -> bool {
    //     matches!(self.name.as_str(), "z8" | "z16" | "z32" | "z64")
    // }

    // pub fn is_subtype_of(&self, other: &Type) -> bool {
    //     if self == other {
    //         return true;
    //     }
    //     if self.is_square_seq() && other.is_square_seq() {
    //         let self_len = self.get_square_seq_length();
    //         let other_len = other.get_square_seq_length();
    //         if self_len.is_some() && other_len.is_some() && self_len != other_len {
    //             return false;
    //         }
    //         if let Some(len) = self_len.or(other_len) {
    //             for i in 0..len {
    //                 let self_elem = self.get_square_elem_type(i).unwrap();
    //                 let other_elem = other.get_square_elem_type(i).unwrap();
    //                 if !self_elem.is_subtype_of(other_elem) {
    //                     return false;
    //                 }
    //             }
    //         } else {
    //             let self_elem = self.get_uniform_square_elem_type().unwrap();
    //             let other_elem = other.get_uniform_square_elem_type().unwrap();
    //             if !self_elem.is_subtype_of(other_elem) {
    //                 return false;
    //             }
    //         }
    //         return true;
    //     }
    //     if self.is_round_seq() && other.is_round_seq() {
    //         let self_len = self.get_round_seq_length();
    //         let other_len = other.get_round_seq_length();
    //         assert!(self_len.is_some() && other_len.is_some(), "Round sequences (tuples) must have known length right now");
    //         if self_len != other_len {
    //             return false;
    //         }
    //         let len = self_len.unwrap();
    //         for i in 0..len {
    //             let self_elem = self.get_round_elem_type(i).unwrap();
    //             let other_elem = other.get_round_elem_type(i).unwrap();
    //             if !self_elem.is_subtype_of(other_elem) {
    //                 return false;
    //             }
    //         }
    //         return true;
    //     }
    //     if self.is_int()
    //         && other.is_int()
    //         && !self.discards_information()
    //         && !other.discards_information()
    //     {
    //         let (self_min, self_max) = lookup_int_bounds(&self.name);
    //         let (other_min, other_max) = lookup_int_bounds(&other.name);
    //         if self_min >= other_min && self_max <= other_max {
    //             return true;
    //         }
    //     }
    //     false
    // }

    pub fn compatible_with(&self, other: &Type) -> bool {
        if self == other {
            return true;
        }
        if self.is_int() && other.is_int() {
            return true;
        }
        // if self.is_empty_seq() && other.is_named_seq() {
        //     return true;
        // }
        // if self.is_named_seq() && other.is_empty_seq() {
        //     return true;
        // }
        // if let Some(self_elem) = self.get_named_seq()
        //     && let Some(other_elem) = other.get_named_seq()
        // {
        //     return self_elem.compatible_with(other_elem);
        // }
        false
    }

    fn type_lambda(
        &self,
        more_general_type: &Type,
        param_list: &[String],
    ) -> Result<Option<TExpr>, TypeError> {
        assert!(
            self.compatible_with(more_general_type),
            "Type {} is not compatible with {}",
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
