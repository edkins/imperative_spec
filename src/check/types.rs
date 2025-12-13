use crate::{
    check::ops::{Ops, big_and},
    syntax::ast::{Arg, Bound, Expr, Literal, Type, TypeArg},
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

impl TypeError {
    pub fn with_context(self, context: &str) -> TypeError {
        TypeError {
            message: format!("{} {}", context, self.message),
        }
    }
}

// impl Bound {
//     pub fn as_expr(&self) -> Result<TExpr, TypeError> {
//         match self {
//             Bound::I64(i) => Ok(TExpr::Literal(Literal::I64(*i))),
//             Bound::U64(u) => Ok(TExpr::Literal(Literal::U64(*u))),
//             Bound::MinusInfinity => Err(TypeError {
//                 message: "Cannot convert -infinity to expression".to_owned(),
//             }),
//             Bound::PlusInfinity => Err(TypeError {
//                 message: "Cannot convert +infinity to expression".to_owned(),
//             }),
//         }
//     }
// }

impl Expr {
    pub fn typ(&self) -> Type {
        match self {
            Expr::Literal(lit) => lit.typ(),
            Expr::Variable { name, typ } => typ
                .clone()
                .expect(&format!("Variable expression {} must have type", name)),
            Expr::Semicolon(_, expr) => expr.typ(),
            Expr::FunctionCall { return_type, .. } => return_type
                .clone()
                .expect("Function call must have return type"),
            Expr::SquareSequence { elem_type, .. } => Type {
                name: "Vec".to_owned(),
                type_args: vec![TypeArg::Type(
                    elem_type
                        .clone()
                        .expect("Square sequence must have element type"),
                )],
            },
            Expr::RoundSequence { elems } => {
                let type_args = elems
                    .iter()
                    .map(|e| TypeArg::Type(e.typ()))
                    .collect::<Vec<TypeArg>>();
                Type {
                    name: "Tuple".to_owned(),
                    type_args,
                }
            }
            Expr::Lambda { args, body } => {
                let mut type_args = args
                    .iter()
                    .map(|arg| TypeArg::Type(arg.arg_type.clone()))
                    .collect::<Vec<TypeArg>>();
                type_args.push(TypeArg::Type(body.typ()));
                Type {
                    name: "Lambda".to_owned(),
                    type_args,
                }
            }
            Expr::SeqAt { seq, index } => {
                let seq_type = seq.typ();
                if seq_type.is_square_seq() {
                    seq_type
                        .get_uniform_square_elem_type()
                        .expect("SeqAt on non-sequence type")
                        .clone()
                } else {
                    let index = index
                        .as_literal_u64()
                        .expect("SeqAt index must be literal u64");
                    seq_type
                        .get_round_elem_type(index)
                        .expect("SeqAt on non-sequence type")
                        .clone()
                }
            }
        }
    }
}

impl TypeArg {
    // fn condless(&self) -> bool {
    //     match self {
    //         TypeArg::Type(t) => t.condless(),
    //         TypeArg::Bound(_) => true,
    //     }
    // }

    pub fn as_type(&self) -> Result<Type, TypeError> {
        match self {
            TypeArg::Type(t) => Ok(t.clone()),
            TypeArg::Bound(_) => Err(TypeError {
                message: "Expected Type, found Bound".to_owned(),
            }),
        }
    }

    pub fn instantiate(
        &self,
        type_params: &[String],
        instantiations: &[Type],
    ) -> Result<TypeArg, TypeError> {
        match self {
            TypeArg::Type(t) => Ok(TypeArg::Type(t.instantiate(type_params, instantiations)?)),
            TypeArg::Bound(b) => Ok(TypeArg::Bound(b.clone())),
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

    pub fn var(&self, name: &str) -> Expr {
        Expr::Variable {
            name: name.to_owned(),
            typ: Some(self.clone()),
        }
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

    pub fn instantiate(
        &self,
        type_params: &[String],
        instantiations: &[Type],
    ) -> Result<Type, TypeError> {
        assert!(type_params.len() == instantiations.len());
        if type_params.contains(&self.name) {
            if !self.type_args.is_empty() {
                return Err(TypeError {
                    message: format!(
                        "Cannot instantiate parameterized type {} with parameters",
                        self
                    ),
                });
            }
            let index = type_params
                .iter()
                .position(|p| p == &self.name)
                .expect("Type parameter must be in type_params");
            Ok(instantiations[index].clone())
        } else {
            Ok(Type {
                name: self.name.clone(),
                type_args: self
                    .type_args
                    .iter()
                    .map(|ta| ta.instantiate(type_params, instantiations))
                    .collect::<Result<Vec<TypeArg>, TypeError>>()?,
            })
        }
    }

    // fn most_general_type_same_size(&self, param_list: &[String]) -> Result<Type, TypeError> {
    //     if param_list.contains(&self.name) {
    //         if self.type_args.is_empty() {
    //             Ok(Type {
    //                 name: self.name.clone(),
    //                 type_args: vec![],
    //             })
    //         } else {
    //             Err(TypeError {
    //                 message: format!(
    //                     "Cannot generalize parameterized type {} with parameters",
    //                     self
    //                 ),
    //             })
    //         }
    //     } else {
    //         match (self.name.as_str(), self.type_args.len()) {
    //             ("u8" | "i8" | "z8", 0) => Ok(Type::basic("z8")),
    //             ("u16" | "i16" | "z16", 0) => Ok(Type::basic("z16")),
    //             ("u32" | "i32" | "z32", 0) => Ok(Type::basic("z32")),
    //             ("u64" | "i64" | "z64", 0) => Ok(Type::basic("z64")),
    //             ("int" | "nat", 0) => Ok(Type::basic("int")),
    //             ("str", 0) => Ok(Type::basic("str")),
    //             ("bool", 0) => Ok(Type::basic("bool")),
    //             ("void", 0) => Ok(Type::basic("void")),
    //             ("Tuple", _) => {
    //                 let type_args = self.type_args.iter()
    //                 .map(|ta| ta.as_type().and_then(|t| t.most_general_type_same_size(param_list)))
    //                 .collect::<Result<Vec<Type>, TypeError>>()?;
    //                 Ok(Type {
    //                     name: "Tuple".to_owned(),
    //                     type_args: type_args.into_iter().map(TypeArg::Type).collect(),
    //                 })
    //             }
    //             ("Vec", 1) | ("Array", 2) => {
    //                 // ignore size for Array
    //                 let elem_type = self.type_args[0].as_type()?.most_general_type_same_size(param_list)?;
    //                 Ok(Type {
    //                     name: "Vec".to_owned(),
    //                     type_args: vec![TypeArg::Type(elem_type)],
    //                 })
    //             }
    //             ("Lambda", _) => {
    //                 // Don't mess with lambdas for now
    //                 Ok(self.clone())
    //             }
    //             _ => Err(TypeError {
    //                 message: format!(
    //                     "Cannot generalize unknown type {} to most general",
    //                     self
    //                 ),
    //             }),
    //         }
    //     }
    // }

    // pub fn most_general_type(&self, param_list: &[String]) -> Result<Type, TypeError> {
    //     if self.is_int() {
    //         Ok(Type::basic("int"))
    //     } else {
    //         // TODO: do we need to special-case tuples here?
    //         // Right now the most general form of (u32, u64) is (z32, z64) not (int, int)
    //         let t = self.most_general_type_same_size(param_list)?;
    //         Ok(t)
    //     }
    // }

    // pub fn condless(&self) -> bool {
    //     match (self.name.as_str(), self.type_args.len()) {
    //         ("int" | "z8" | "z16" | "z32" | "z64" | "str" | "bool" | "void", 0) => true,
    //         ("Tuple", _) => {
    //             assert!(self.type_args.len() > 0);
    //             self.type_args.iter().all(TypeArg::condless)
    //         }
    //         ("Array", 2) => self.type_args.iter().all(TypeArg::condless),
    //         ("Vec", 1) => self.type_args.iter().all(TypeArg::condless),
    //         ("Lambda", _) => {
    //             for arg in &self.type_args {
    //                 match arg {
    //                     TypeArg::Type(t) => {
    //                         if !t.condless() {
    //                             return false;
    //                         }
    //                     }
    //                     TypeArg::Bound(_) => {}
    //                 }
    //             }
    //             true
    //         }
    //         _ => false,
    //     }
    // }

    pub fn type_assertions(
        &self,
        expr: Expr,
        param_list: &[String],
    ) -> Result<Vec<Expr>, TypeError> {
        assert!(
            expr.typ() == self.skeleton(param_list)?,
            "Type assertion expression type {} does not match expected type {}",
            expr.typ(),
            self.skeleton(param_list)?
        );
        assert!(param_list.is_empty());
        match self.name.as_str() {
            "int" | "nat" | "z8" | "z16" | "z32" | "z64" | "i8" | "i16" | "i32" | "i64" | "u8"
            | "u16" | "u32" | "u64" => {
                let (lower, upper) = lookup_int_bounds(&self.name);
                Ok(bounds_to_expr(lower, upper, expr))
            }
            "Vec" | "Array" => {
                let elem_type = self.uniform_square_elem_type()?;
                let mut conds = vec![];
                if let Some(len) = self.get_square_seq_length() {
                    conds.push(expr.seq_len()?.eq(&Expr::Literal(Literal::U64(len)))?);
                }
                if let Some(lambda) = elem_type.type_lambda(param_list)? {
                    conds.push(expr.seq_all(&lambda)?);
                }
                Ok(conds)
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
                if *self == self.skeleton(param_list)? {
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

    pub fn uniform_square_elem_type(&self) -> Result<Type, TypeError> {
        if let Some(t) = self.get_uniform_square_elem_type() {
            Ok(t.clone())
        } else {
            Err(TypeError {
                message: format!("Type {} is not a uniform square sequence", self),
            })
        }
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

    pub fn get_square_seq_length(&self) -> Option<u64> {
        if self.name == "Array" && self.type_args.len() == 2 {
            match &self.type_args[1] {
                TypeArg::Bound(Bound::U64(u)) => Some(*u),
                _ => None,
            }
        } else {
            None
        }
    }

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

    // pub fn compatible_with(&self, other: &Type) -> bool {
    //     if self == other {
    //         return true;
    //     }
    //     if self.is_int() && other.is_int() {
    //         return true;
    //     }
    //     // if self.is_empty_seq() && other.is_named_seq() {
    //     //     return true;
    //     // }
    //     // if self.is_named_seq() && other.is_empty_seq() {
    //     //     return true;
    //     // }
    //     // if let Some(self_elem) = self.get_named_seq()
    //     //     && let Some(other_elem) = other.get_named_seq()
    //     // {
    //     //     return self_elem.compatible_with(other_elem);
    //     // }
    //     false
    // }

    fn type_lambda(&self, param_list: &[String]) -> Result<Option<Expr>, TypeError> {
        let more_general_type = self.skeleton(param_list)?;
        let var = Expr::Variable {
            name: "__item__".to_owned(),
            typ: Some(more_general_type.clone()),
        };
        let conds = self.type_assertions(var, param_list)?;
        if conds.is_empty() {
            return Ok(None);
        }
        Ok(Some(Expr::Lambda {
            args: vec![Arg {
                name: "__item__".to_owned(),
                mutable: false,
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

fn bounds_to_expr(lower: Bound, upper: Bound, expr: Expr) -> Vec<Expr> {
    let mut result = vec![];
    match lower {
        Bound::MinusInfinity => {}
        Bound::I64(i) => result.push(expr.ge(&Expr::Literal(Literal::I64(i))).unwrap()),
        Bound::U64(u) => result.push(expr.ge(&Expr::Literal(Literal::U64(u))).unwrap()),
        Bound::PlusInfinity => unreachable!(),
    }
    match upper {
        Bound::PlusInfinity => {}
        Bound::I64(i) => result.push(expr.le(&Expr::Literal(Literal::I64(i))).unwrap()),
        Bound::U64(u) => result.push(expr.le(&Expr::Literal(Literal::U64(u))).unwrap()),
        Bound::MinusInfinity => unreachable!(),
    }
    result
}

impl Literal {
    pub fn typ(&self) -> Type {
        match self {
            Literal::Unit => Type::basic("void"),
            Literal::U64(_) => Type::basic("int"),
            Literal::I64(_) => Type::basic("int"),
            Literal::Str(_) => Type::basic("str"),
            Literal::Bool(_) => Type::basic("bool"),
        }
    }
}
