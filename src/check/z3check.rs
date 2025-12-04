use std::{
    collections::{HashMap, HashSet},
    error::Error,
    ffi::NulError,
    fmt::Display,
    str::FromStr,
};

use crate::{check::{ztype_ast::{TExpr, TFuncDef, TStmt}, ztype_inference::TypeError}, syntax::ast::*};
use z3::{self, SortDiffers, ast::Dynamic};

#[derive(Debug)]
pub struct CheckError {
    pub message: String,
}

impl Display for CheckError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "CheckError: {}", self.message)
    }
}
impl Error for CheckError {}

impl From<TypeError> for CheckError {
    fn from(err: TypeError) -> Self {
        CheckError {
            message: format!("TypeError: {}", err),
        }
    }
}

impl From<SortDiffers> for CheckError {
    fn from(err: SortDiffers) -> Self {
        CheckError {
            message: format!("SortDiffers: {}", err),
        }
    }
}

// #[derive(Clone)]
// enum Z3Value {
//     Void,
//     Bool(z3::ast::Bool),
//     Int(z3::ast::Int),
//     Str(z3::ast::String),
//     Vec(z3::ast::Seq, Type),
//     Array(z3::ast::Seq, Type),
//     UnknownSeq(Vec<Z3Value>),
// }

// impl std::fmt::Display for Z3Value {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         match self {
//             Z3Value::Void => write!(f, "()"),
//             Z3Value::Bool(b) => write!(f, "{}", b),
//             Z3Value::Int(i) => write!(f, "{}", i),
//             Z3Value::Str(s) => write!(f, "{}", s),
//             Z3Value::Vec(v, t) => write!(f, "{} : Vec<{}>", v, t),
//             Z3Value::Array(a, t) => write!(f, "{} : Array<{}>", a, t),
//             Z3Value::UnknownSeq(v) => {
//                 write!(f, "[")?;
//                 for (i, val) in v.iter().enumerate() {
//                     if i > 0 {
//                         write!(f, ", ")?;
//                     }
//                     write!(f, "{}", val)?;
//                 }
//                 write!(f, "]")
//             }
//         }
//     }
// }

#[derive(Clone)]
struct CheckedFunction {
    name: String,
    args: Vec<Arg>,
    return_type: Type,
    return_value: String,
    side_effects: HashSet<String>,
    preconditions: Vec<TExpr>,
    postconditions: Vec<TExpr>,
    body: Option<TExpr>,
}

#[derive(Clone)]
struct CheckedVar {
    name: String,
    version: usize,
    max_version: usize,
    mutable: bool,
    hidden: bool,
    var_type: Type,
}

#[derive(Clone)]
struct Env {
    vars: HashMap<String, CheckedVar>,
    assumptions: Vec<z3::ast::Bool>,
    side_effects: HashSet<String>,
    other_funcs: Vec<CheckedFunction>,
}

#[derive(Clone, Copy)]
enum AssertMode {
    Assert,
    Assume,
}

impl CheckedFunction {
    fn z3_func_decl(&self) -> Result<z3::FuncDecl, CheckError> {
        let args = self
            .args
            .iter()
            .map(|arg| arg.arg_type.to_z3_sort())
            .collect::<Result<Vec<_>, _>>()?;
        let arg_refs = args.iter().collect::<Vec<&z3::Sort>>();
        let ret_sort = self.return_type.to_z3_sort()?;
        Ok(z3::FuncDecl::new(self.name.clone(), &arg_refs, &ret_sort))
    }

    fn with_visibility(&self, sees: &[String]) -> CheckedFunction {
        let body = if sees.contains(&self.name) {
            self.body.clone()
        } else {
            None
        };
        CheckedFunction {
            name: self.name.clone(),
            args: self.args.clone(),
            return_type: self.return_type.clone(),
            return_value: self.return_value.clone(),
            side_effects: self.side_effects.clone(),
            preconditions: self.preconditions.clone(),
            postconditions: self.postconditions.clone(),
            body,
        }
    }
}

impl From<NulError> for CheckError {
    fn from(err: NulError) -> Self {
        CheckError {
            message: format!("NulError: {}", err),
        }
    }
}

impl CheckedVar {
    fn z3_name(&self) -> Result<String, CheckError> {
        if self.hidden {
            Err(CheckError {
                message: format!("Variable {} is out of scope", self.name),
            })
        } else if self.mutable || self.version > 0 {
            Ok(format!("{}:{}", self.name, self.version))
        } else {
            Ok(self.name.clone())
        }
    }

    fn z3_const(&self) -> Result<Dynamic, CheckError> {
        self.var_type.to_z3_const(&self.z3_name()?)
    }

    fn mutate(&mut self) {
        assert!(!self.hidden);
        self.max_version += 1;
        self.version = self.max_version;
    }

    fn replace(&mut self, mutable: bool, typ: &Type) {
        self.hidden = false;
        self.max_version += 1;
        self.version = self.max_version;
        self.mutable = mutable;
        self.var_type = typ.clone();
    }
}

// impl Z3Value {
    // fn guess_type(&self) -> Type {
    //     match self {
    //         Z3Value::Void => Type {
    //             name: "void".to_owned(),
    //             type_args: vec![],
    //         },
    //         Z3Value::Bool(_) => Type {
    //             name: "bool".to_owned(),
    //             type_args: vec![],
    //         },
    //         Z3Value::Int(_) => Type {
    //             name: "int".to_owned(),
    //             type_args: vec![],
    //         },
    //         Z3Value::Str(_) => Type {
    //             name: "str".to_owned(),
    //             type_args: vec![],
    //         },
    //         Z3Value::Array(_, e) => Type {
    //             name: "Array".to_owned(),
    //             type_args: vec![TypeArg::Type(e.clone())],
    //         },
    //         Z3Value::Vec(_, e) => Type {
    //             name: "Vec".to_owned(),
    //             type_args: vec![TypeArg::Type(e.clone())],
    //         },
    //         Z3Value::UnknownSeq(xs) => Type {
    //             name: "UnknownSeq".to_owned(),
    //             type_args: vec![TypeArg::Type(xs[0].guess_type())],
    //         }
    //     }
    // }

    // fn len(&self) -> Result<z3::ast::Int, CheckError> {
    //     match self {
    //         Z3Value::Vec(seq, _) => Ok(seq.length()),
    //         Z3Value::Array(seq, _) => Ok(seq.length()),
    //         Z3Value::UnknownSeq(xs) => Ok(z3::ast::Int::from_u64(xs.len() as u64)),
    //         _ => Err(CheckError {
    //             message: "Length can only be obtained for Vec or Array types".to_owned(),
    //         }),
    //     }
    // }

//     fn eq(&self, other: &Z3Value) -> Result<z3::ast::Bool, CheckError> {
//         match (self, other) {
//             (Z3Value::Bool(a), Z3Value::Bool(b)) => Ok(a.eq(b)),
//             (Z3Value::Int(a), Z3Value::Int(b)) => Ok(a.eq(b)),
//             (Z3Value::Str(a), Z3Value::Str(b)) => Ok(a.eq(b)),
//             (Z3Value::Vec(a, t), Z3Value::Vec(b, u)) if t==u => Ok(a.eq(b)),
//             (Z3Value::Array(a, t), Z3Value::Array(b, u)) if t==u => Ok(a.eq(b)),
//             (Z3Value::Vec(a, _t), Z3Value::UnknownSeq(xs)) => {
//                 let mut eqs = vec![a.length().eq(&z3::ast::Int::from_u64(xs.len() as u64))];
//                 for (i, x) in xs.iter().enumerate() {
//                     let idx = z3::ast::Int::from_u64(i as u64);
//                     let elem = a.nth(&idx);
//                     let x_dyn = x.to_z3_dynamic()?;
//                     eqs.push(elem.eq(&x_dyn));
//                 }
//                 Ok(z3::ast::Bool::and(&eqs))
//             }
//             _ => Err(CheckError {
//                 message: format!("Type mismatch or unsupported type in equality: {} vs {}", self, other),
//             }),
//         }
//     }

//     fn ne(&self, other: &Z3Value) -> Result<z3::ast::Bool, CheckError> {
//         self.eq(other).map(|eq_ast| eq_ast.not())
//     }

//     fn bool(&self) -> Result<&z3::ast::Bool, CheckError> {
//         match self {
//             Z3Value::Bool(b) => Ok(b),
//             _ => Err(CheckError {
//                 message: "Expected Bool type".to_owned(),
//             }),
//         }
//     }

//     fn int(&self) -> Result<&z3::ast::Int, CheckError> {
//         match self {
//             Z3Value::Int(i) => Ok(i),
//             _ => Err(CheckError {
//                 message: "Expected Int type".to_owned(),
//             }),
//         }
//     }

//     fn string(&self) -> Result<&z3::ast::String, CheckError> {
//         match self {
//             Z3Value::Str(s) => Ok(s),
//             _ => Err(CheckError {
//                 message: "Expected String type".to_owned(),
//             }),
//         }
//     }

//     fn void(&self) -> Result<(), CheckError> {
//         match self {
//             Z3Value::Void => Ok(()),
//             _ => Err(CheckError {
//                 message: "Expected Void type".to_owned(),
//             }),
//         }
//     }

//     fn to_z3_dynamic(&self) -> Result<Dynamic, CheckError> {
//         match self {
//             Z3Value::Bool(b) => Ok(b.clone().into()),
//             Z3Value::Int(i) => Ok(i.clone().into()),
//             Z3Value::Str(s) => Ok(s.clone().into()),
//             Z3Value::Vec(seq, _) => Ok(seq.clone().into()),
//             Z3Value::Array(seq, _) => Ok(seq.clone().into()),
//             Z3Value::Void => Err(CheckError {
//                 message: "Void type cannot be converted to Z3 dynamic".to_owned(),
//             }),
//             Z3Value::UnknownSeq(_) => Err(CheckError {
//                 message: "UnknownSeq type cannot be converted to Z3 dynamic".to_owned(),
//             }),
//         }
//     }
// }

impl Literal {
    fn z3_check(&self) -> Result<Dynamic, CheckError> {
        match self {
            Literal::I64(value) => Ok(z3::ast::Int::from_i64(*value).into()),
            Literal::U64(value) => Ok(z3::ast::Int::from_u64(*value).into()),
            Literal::Str(value) => Ok(z3::ast::String::from_str(value)?.into()),
            Literal::Bool(value) => Ok(z3::ast::Bool::from_bool(*value).into()),
        }
    }
}

impl Bound {
    fn to_z3_int(&self) -> Option<z3::ast::Int> {
        match self {
            Bound::MinusInfinity => None,
            Bound::PlusInfinity => None,
            Bound::I64(v) => Some(z3::ast::Int::from_i64(*v)),
            Bound::U64(v) => Some(z3::ast::Int::from_u64(*v)),
        }
    }
}

impl Type {
    // fn check_value(&self, value: &Dynamic, env: &mut Env) -> Result<(), CheckError> {
    //     self.check_or_assume_value(value, env, AssertMode::Assert)
    // }

    // fn check_or_assume_value(&self, value: &Dynamic, env: &mut Env, mode: AssertMode) -> Result<(), CheckError> {
    //     match self.name.as_str() {
    //         "u8" | "i8" | "u16" | "i16" | "u32" | "i32" | "u64" | "i64" | "nat" | "int" => {
    //             let v = int(value)?;
    //             let (lower, upper) = self.z3_int_bounds();
    //             if let Some(lower) = lower {
    //                 env.assert_or_assume(&v.ge(&lower), "Lower bound check failed", mode)?;
    //             }
    //             if let Some(upper) = upper {
    //                 env.assert_or_assume(&v.le(&upper), "Upper bound check failed", mode)?;
    //             }
    //             Ok(())
    //         }
    //         "bool" => {
    //             boolean(value)?;
    //             Ok(())
    //         }
    //         "str" => {
    //             string(value)?;
    //             Ok(())
    //         }
    //         "void" => {
    //             // nothing to check
    //             Ok(())
    //         }
    //         "EmptySeq" => {
    //             // match value.as_seq() {
    //             //     Some(seq) => {
    //             //         env.assert_or_assume(&seq.length().eq(&z3::ast::Int::from_u64(0)), "EmptySeq length check failed", mode)
    //             //     }
    //             //     None => Err(CheckError {
    //             //         message: format!("Expected EmptySeq type, got {}", value),
    //             //     }),
    //             // }
    //             unreachable!("We shouldn't see EmptySeq past type checking");
    //         }
    //         "Seq" => {
    //             let expected_elem_type = self.one_type_arg()?;
    //             if let Some(value) = value.as_seq() {
    //                 // TODO: check all elements expected_elem_type.check_value(&value.nth(&z3::ast::Int::from_u64(0)).into(), env)?;
    //                 Ok(())
    //             } else {
    //                 Err(CheckError {
    //                     message: format!("Expected Seq type, got {}", value),
    //                 })
    //             }
    //         }
    //         _ => Err(CheckError {
    //             message: format!("Unsupported type for check_or_assume_value: {}", self),
    //         }),
    //     }
    // }

    // fn coerce_z3_dynamic(&self, dyn_ast: &Dynamic) -> Result<Z3Value, CheckError> {
    //     match self.name.as_str() {
    //         "u8" | "i8" | "u16" | "i16" | "u32" | "i32" | "u64" | "i64" | "nat" | "int" => {
    //             Ok(Z3Value::Int(dyn_ast.as_int().ok_or_else(|| {
    //                 CheckError {
    //                     message: "Expected Int type".to_owned(),
    //                 }
    //             })?))
    //         }
    //         "bool" => Ok(Z3Value::Bool(dyn_ast.as_bool().ok_or_else(|| {
    //             CheckError {
    //                 message: "Expected Bool type".to_owned(),
    //             }
    //         })?)),
    //         "str" => Ok(Z3Value::Str(dyn_ast.as_string().ok_or_else(|| {
    //             CheckError {
    //                 message: "Expected String type".to_owned(),
    //             }
    //         })?)),
    //         "void" => Err(CheckError {
    //             message: "Void type cannot be converted from Z3 dynamic".to_owned(),
    //         }),
    //         _ => Err(CheckError {
    //             message: format!("Unsupported type for coerce_z3_dynamic: {}", self),
    //         }),
    //     }
    // }

    // fn check_z3_dynamic(&self, dyn_ast: &Dynamic, env: &mut Env) -> Result<Z3Value, CheckError> {
    //     let v = self.coerce_z3_dynamic(dyn_ast)?;
    //     self.check_value(&v, env)?;
    //     Ok(v)
    // }

    fn to_z3_sort(&self) -> Result<z3::Sort, CheckError> {
        match self.name.as_str() {
            "u8" | "i8" | "u16" | "i16" | "u32" | "i32" | "u64" | "i64" | "nat" | "int" => {
                Ok(z3::Sort::int())
            }
            "bool" => Ok(z3::Sort::bool()),
            "str" => Ok(z3::Sort::string()),
            "void" => Err(CheckError {
                message: "Void type cannot be converted from Z3 dynamic".to_owned(),
            }),
            _ => Err(CheckError {
                message: format!("Unsupported type for to_z3_sort: {}", self),
            }),
        }
    }

    fn to_z3_const(&self, name: &str) -> Result<Dynamic, CheckError> {
        match self.name.as_str() {
            "u8" | "i8" | "u16" | "i16" | "u32" | "i32" | "u64" | "i64" | "nat" | "int" =>
                Ok(z3::ast::Int::new_const(name).into()),
            "bool" => Ok(z3::ast::Bool::new_const(name).into()),
            "str" => Ok(z3::ast::String::new_const(name).into()),
            "void" => Ok(void_value()),
            "Vec" => {
                let elem_type = self.one_type_arg()?;
                let elem_sort = elem_type.to_z3_sort()?;
                Ok(z3::ast::Seq::new_const(name, &elem_sort).into())
            }
            // "Array" => {
            //     if let Some(TypeArg::Type(elem_type)) = self.type_args.get(0) {
            //         let elem_sort = elem_type.to_z3_sort()?;
            //         Ok(Z3Value::Array(z3::ast::Seq::new_const(name, &elem_sort), elem_type.clone()))
            //     } else {
            //         Err(CheckError {
            //             message: "Array type missing element type".to_owned(),
            //         })
            //     }
            // }
            _ => Err(CheckError {
                message: format!("Unsupported type for to_z3_const: {}", self),
            }),
        }
    }
}

impl AssignOp {
    fn relate(
        &self,
        old_left: Dynamic,
        new_left: Dynamic,
        right: Dynamic,
    ) -> Result<z3::ast::Bool, CheckError> {
        match self {
            AssignOp::Assign => Ok(new_left.safe_eq(&right)?),
            AssignOp::PlusAssign => {
                let left_int = int(&old_left)?;
                let right_int = int(&right)?;
                Ok(int(&new_left)?.safe_eq(left_int + right_int)?)
            }
            AssignOp::MinusAssign => {
                let left_int = int(&old_left)?;
                let right_int = int(&right)?;
                Ok(int(&new_left)?.safe_eq(left_int - right_int)?)
            }
        }
    }
}

impl Env {
    fn new(other_funcs: &[CheckedFunction], sees: &[String]) -> Self {
        let mut other_funcs_visible = Vec::new();
        for func in other_funcs {
            // Hide the body of functions not in 'sees'
            other_funcs_visible.push(func.with_visibility(sees));
        }
        Env {
            vars: HashMap::new(),
            assumptions: Vec::new(),
            side_effects: HashSet::new(),
            other_funcs: other_funcs_visible,
        }
    }

    fn get_var(&self, name: &str) -> Result<Dynamic, CheckError> {
        if let Some(info) = self.vars.get(name) {
            info.z3_const()
        } else {
            Err(CheckError {
                message: format!("Undefined variable: {}", name),
            })
        }
    }

    fn insert_var(
        &mut self,
        name: &str,
        mutable: bool,
        ty: &Type,
    ) -> Result<Dynamic, CheckError> {
        self.vars
            .entry(name.to_owned())
            .and_modify(|info| info.replace(mutable, ty))
            .or_insert_with(|| CheckedVar {
                name: name.to_owned(),
                version: 0,
                max_version: 0,
                hidden: false,
                mutable,
                var_type: ty.clone(),
            })
            .z3_const()
    }

    fn assume(&mut self, cond: z3::ast::Bool) {
        self.assumptions.push(cond);
    }

    fn assert(&mut self, cond: &z3::ast::Bool, message: &str) -> Result<(), CheckError> {
        let solver = z3::Solver::new();
        for assumption in &self.assumptions {
            solver.assert(assumption);
        }
        solver.assert(cond.not());
        if solver.check() != z3::SatResult::Unsat {
            Err(CheckError {
                message: format!("{}: {}", message, cond),
            })
        } else {
            self.assumptions.push(cond.clone());
            Ok(())
        }
    }

    fn assert_or_assume(
        &mut self,
        cond: &z3::ast::Bool,
        message: &str,
        mode: AssertMode,
    ) -> Result<(), CheckError> {
        match mode {
            AssertMode::Assert => self.assert(cond, message),
            AssertMode::Assume => {
                self.assume(cond.clone());
                Ok(())
            }
        }
    }

    fn prints(&mut self) {
        self.side_effects.insert("print".to_owned());
    }

    #[allow(dead_code)]
    fn mallocs(&mut self) {
        self.side_effects.insert("malloc".to_owned());
    }

    fn print_side_effects(&self) {
        let mut effects: Vec<_> = self.side_effects.iter().collect();
        effects.sort();
        for effect in &effects {
            print!(" {{{}}}", effect);
        }
        println!();
    }

    fn assign(&mut self, var: &str, value: Dynamic) -> Result<(), CheckError> {
        let info = self.vars.get_mut(var).ok_or(CheckError {
            message: format!("Undefined variable: {}", var),
        })?;
        if !info.mutable {
            return Err(CheckError {
                message: format!("Cannot assign to immutable variable: {}", var),
            });
        }
        info.mutate();
        let new_var = info.z3_const()?;
        self.assume(new_var.safe_eq(&value)?);
        // println!("Checking value of assigned variable {} to type {}", new_var, ty);
        // ty.check_value(&new_var.clone(), self)
        Ok(())
    }

    fn fold_in_scope(&mut self, other: &Env) {
        for (name, other_var) in &other.vars {
            self.vars
                .entry(name.clone())
                .and_modify(|var| {
                    assert!(other_var.version >= var.version);
                    var.version = other_var.version;
                })
                .or_insert_with(|| {
                    let mut other_clone = other_var.clone();
                    other_clone.hidden = true;
                    other_clone
                });
        }
        for effect in &other.side_effects {
            self.side_effects.insert(effect.clone());
        }

        for assumption in &other.assumptions {
            if !self.assumptions.contains(assumption) {
                self.assumptions.push(assumption.clone());
            }
        }
    }

    fn enter_call_scope(
        &self,
        func: &CheckedFunction,
        args: &[Dynamic],
    ) -> Result<Env, CheckError> {
        let mut new_env = self.clone();
        if func.args.len() != args.len() {
            return Err(CheckError {
                message: format!(
                    "Function {} expected {} arguments, got {}",
                    func.name,
                    func.args.len(),
                    args.len()
                ),
            });
        }

        // hide all outside variables
        for var in new_env.vars.values_mut() {
            var.hidden = true;
        }

        for (arg, value) in func.args.iter().zip(args.iter()) {
            let new_var = new_env.insert_var(&arg.name, false, &arg.arg_type)?;
            new_env.assume(new_var.safe_eq(value)?);
            // arg.arg_type.check_value(&new_var, &mut new_env)?;
        }
        Ok(new_env)
    }

    fn check_preconditions(&mut self, func: &CheckedFunction) -> Result<(), CheckError> {
        for precondition in &func.preconditions {
            let cond_z3_value = precondition.z3_check(self)?;
            self.assert(&boolean(&cond_z3_value)?, "Precondition failed")?;
        }
        Ok(())
    }
}

impl TStmt {
    fn z3_check(&self, env: &mut Env) -> Result<(), CheckError> {
        match self {
            TStmt::Expr(expr) => {
                expr.z3_check(env)?;
                Ok(())
            }
            TStmt::Let { name, typ, value, mutable } => {
                let z3_value = value.z3_check(env)?;
                let z3_var = env.insert_var(name, *mutable, &typ)?;
                // typ.check_value(&z3_var, env)?;
                env.assume(z3_var.safe_eq(&z3_value)?);
                Ok(())
            }
            TStmt::Assign { name, value } => {
                let z3_value = value.z3_check(env)?;
                env.assign(name, z3_value)
            }
        }
    }
}

// fn z3_mk_sequence(elems: &[Z3Value]) -> Result<Z3Value, CheckError> {
//     if elems.is_empty() {
//         return Err(CheckError {
//             message: "Cannot create sequence from empty elements".to_owned(),
//         });
//     }
//     let first_elem = &elems[0];
//     let elem_type = first_elem.guess_type();
//     let mut z3_elems:Vec<Dynamic> = Vec::new();
//     for elem in elems {
//         match elem {
//             Z3Value::Bool(b) => {
//                 if elem_type.name != "bool" {
//                     return Err(CheckError {
//                         message: "Type mismatch in sequence elements".to_owned(),
//                     });
//                 }
//                 z3_elems.push(b.clone().into());
//             }
//             Z3Value::Int(i) => {
//                 if elem_type.name != "int" {
//                     return Err(CheckError {
//                         message: "Type mismatch in sequence elements".to_owned(),
//                     });
//                 }
//                 z3_elems.push(i.clone().into());
//             }
//             Z3Value::Str(s) => {
//                 if elem_type.name != "str" {
//                     return Err(CheckError {
//                         message: "Type mismatch in sequence elements".to_owned(),
//                     });
//                 }
//                 z3_elems.push(s.clone().into());
//             }
//             _ => {
//                 return Err(CheckError {
//                     message: "Unsupported element type for sequence".to_owned(),
//                 });
//             }
//         }
//     }
//     let values = z3_elems
//         .iter()
//         .map(|e| z3::ast::Seq::unit(e))
//         .collect::<Vec<_>>();
//     let seq_ast = z3::ast::Seq::concat(&values);
//     Ok(Z3Value::Vec(seq_ast, elem_type))
// }

fn int(x: &Dynamic) -> Result<z3::ast::Int, CheckError> {
    x.as_int().ok_or_else(|| CheckError {
        message: "Expected Int type".to_owned(),
    })
}

fn boolean(x: &Dynamic) -> Result<z3::ast::Bool, CheckError> {
    x.as_bool().ok_or_else(|| CheckError {
        message: "Expected Bool type".to_owned(),
    })
}

fn string(x: &Dynamic) -> Result<z3::ast::String, CheckError> {
    x.as_string().ok_or_else(|| CheckError {
        message: "Expected String type".to_owned(),
    })
}

fn void_value() -> Dynamic {
    // There is no direct Void type in Z3, so we can use a dummy value
    z3::ast::Int::from_i64(0).into()
}

fn z3_function_call(name: &str, args: &[Dynamic], return_type: &Type, env: &mut Env) -> Result<Dynamic, CheckError> {
    // TODO: check return type is correct?
    match (name, args.len()) {
        ("==", 2) => {
            Ok(args[0].safe_eq(&args[1])?.into())
        }
        ("!=", 2) => {
            Ok(args[0].safe_eq(&args[1])?.not().into())
        }
        ("<", 2) => {
            Ok(int(&args[0])?.lt(&int(&args[1])?).into())
        }
        ("<=", 2) => {
            Ok(int(&args[0])?.le(&int(&args[1])?).into())
        }
        (">", 2) => {
            Ok(int(&args[0])?.gt(&int(&args[1])?).into())
        }
        (">=", 2) => {
            Ok(int(&args[0])?.ge(&int(&args[1])?).into())
        }
        ("+", 2) => Ok((int(&args[0])? + int(&args[1])?).into()),
        ("-", 2) => Ok((int(&args[0])? - int(&args[1])?).into()),
        ("assert", 1) => {
            let bool_arg = boolean(&args[0])?;
            env.assert(&bool_arg, "Assertion failed")?;
            Ok(void_value())
        }
        ("println", 1) => {
            string(&args[0])?;
            env.prints();
            Ok(void_value())
        }
        _ => {
            if let Some(user_func) = env.other_funcs.iter().find(|f| f.name == name) {
                let user_func = user_func.clone(); // clone it because we're doing other things to env and they conflict
                let func_decl = user_func.z3_func_decl()?;
                let mut call_env = env.enter_call_scope(&user_func, args)?;
                call_env.check_preconditions(&user_func)?;

                let z3_argrefs = args
                    .iter()
                    .map(|a| a as &dyn z3::ast::Ast)
                    .collect::<Vec<&dyn z3::ast::Ast>>();

                let retvar = call_env
                    .insert_var(&user_func.return_value, false, &user_func.return_type)?;

                // we can assume the postconditions (which includes type info e.g. bounds on the return value)
                for postcondition in &user_func.postconditions {
                    let cond_z3_value = postcondition.z3_check(&mut call_env)?;
                    call_env.assume(boolean(&cond_z3_value)?);
                }
                // don't forget the side effects
                for effect in &user_func.side_effects {
                    call_env.side_effects.insert(effect.clone());
                }

                // If body is visible, check it (which will add relevant assumptions)
                if let Some(body) = &user_func.body {
                    let body_z3_value = body.z3_check(&mut call_env)?;
                    env.assume(retvar.safe_eq(&body_z3_value)?);
                }

                // fold back into main env
                env.fold_in_scope(&call_env);

                // unify return value with function call
                let ast = func_decl.apply(&z3_argrefs);
                env.assume(retvar.safe_eq(&ast)?);

                Ok(ast)
            } else {
                Err(CheckError {
                    message: format!("Undefined function: {}", name),
                })
            }
        }
    }
}

impl TExpr {
    fn z3_check(&self, env: &mut Env) -> Result<Dynamic, CheckError> {
        match self {
            TExpr::Unit => Ok(void_value()),
            TExpr::Literal(literal) => literal.z3_check(),
            TExpr::Variable{name, ..} => env.get_var(name),
            TExpr::FunctionCall { name, args, return_type } => {
                let z3args = args
                    .iter()
                    .map(|arg| arg.z3_check(env))
                    .collect::<Result<Vec<_>, _>>()?;
                z3_function_call(name, &z3args, return_type, env)
            }
            TExpr::Semicolon(stmt, expr) => {
                stmt.z3_check(env)?;
                expr.z3_check(env)
            }
            TExpr::Sequence{elements, elem_type} => {
                let z3elems = elements
                    .iter()
                    .map(|elem| elem.z3_check(env))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(mk_z3_sequence(z3elems, elem_type)?)
            }
            TExpr::EmptySequence => {
                unreachable!("We shouldn't see EmptySequence past type checking");
            }
        }
    }
}

fn mk_z3_sequence(elems: Vec<Dynamic>, elem_type: &Type) -> Result<Dynamic, CheckError> {
    if elems.is_empty() {
        return Ok(z3::ast::Seq::empty(&elem_type.to_z3_sort()?).into());
    }
    // let elem_sort = elem_type.to_z3_sort()?;
    let mut z3_units:Vec<z3::ast::Seq> = Vec::new();
    for elem in elems {
        z3_units.push(z3::ast::Seq::unit(&elem));
    }
    let seq_ast = z3::ast::Seq::concat(&z3_units);
    Ok(seq_ast.into())
}

fn z3_check_funcdef(
    func: &TFuncDef,
    other_funcs: &[CheckedFunction],
) -> Result<CheckedFunction, CheckError> {
    let mut env = Env::new(other_funcs, &func.sees);
    for arg in &func.args {
        let _arg_var = env.insert_var(&arg.name, false, &arg.arg_type)?;
        // arg.arg_type.check_or_assume_value(&arg_var, &mut env, AssertMode::Assume)?;
    }
    for precondition in &func.preconditions {
        let cond_z3_value = precondition.z3_check(&mut env)?;
        env.assume(boolean(&cond_z3_value)?);
    }
    let body_z3_value = func.body.z3_check(&mut env)?;
    // func.return_type.check_value(&body_z3_value, &mut env)?;

    // now check all the postconditions
    let ret = &func.return_name;
    let ret_var = env.insert_var(ret, false, &func.return_type)?;
    env.assume(ret_var.safe_eq(&body_z3_value)?);
    for postcondition in &func.postconditions {
        let cond_z3_value = postcondition.z3_check(&mut env)?;
        env.assert(&boolean(&cond_z3_value)?, "Postcondition failed")?;
    }

    print!("Checked function: {}", func.name);
    env.print_side_effects();
    Ok(CheckedFunction {
        name: func.name.clone(),
        args: func.args.clone(),
        return_type: func.return_type.clone(),
        return_value: func.return_name.clone(),
        side_effects: env.side_effects,
        preconditions: func.preconditions.clone(),
        postconditions: func.postconditions.clone(),
        body: Some(func.body.clone()),
    })
}

pub fn z3_check(source_file: &SourceFile, verbose: bool) -> Result<(), CheckError> {
    let tsource_file = source_file.type_check()?;
    if verbose {
        println!("{}", tsource_file);
        println!("Type checking passed. Starting Z3 checking...");
    }

    let mut other_funcs = vec![];
    for func in &tsource_file.functions {
        let checked_func = z3_check_funcdef(func, &other_funcs)?;
        other_funcs.push(checked_func);
    }
    Ok(())
}
