use std::{
    collections::{HashMap, HashSet},
    error::Error,
    ffi::NulError,
    fmt::Display,
    str::FromStr,
};

use crate::syntax::ast::*;
use z3;

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

#[derive(Clone)]
enum Z3Value {
    Void,
    Bool(z3::ast::Bool),
    Int(z3::ast::Int),
    Str(z3::ast::String),
    Vec(z3::ast::Seq, Type),
    Array(z3::ast::Seq, Type),
    UnknownSeq(Vec<Z3Value>),
}

impl std::fmt::Display for Z3Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Z3Value::Void => write!(f, "()"),
            Z3Value::Bool(b) => write!(f, "{}", b),
            Z3Value::Int(i) => write!(f, "{}", i),
            Z3Value::Str(s) => write!(f, "{}", s),
            Z3Value::Vec(v, t) => write!(f, "{} : Vec<{}>", v, t),
            Z3Value::Array(a, t) => write!(f, "{} : Array<{}>", a, t),
            Z3Value::UnknownSeq(v) => {
                write!(f, "[")?;
                for (i, val) in v.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", val)?;
                }
                write!(f, "]")
            }
        }
    }
}

#[derive(Clone)]
struct CheckedFunction {
    name: String,
    args: Vec<Arg>,
    return_type: Type,
    return_value: String,
    side_effects: HashSet<String>,
    preconditions: Vec<Expr>,
    postconditions: Vec<Expr>,
    body: Option<Expr>,
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
                message: "Variable is out of scope".to_owned(),
            })
        } else if self.mutable || self.version > 0 {
            Ok(format!("{}:{}", self.name, self.version))
        } else {
            Ok(self.name.clone())
        }
    }

    fn z3_const(&self) -> Result<Z3Value, CheckError> {
        self.var_type.to_z3_const(&self.z3_name()?)
    }

    fn mutate(&mut self) {
        self.max_version += 1;
        self.version = self.max_version;
    }

    fn replace(&mut self, mutable: bool, typ: &Type) {
        self.max_version += 1;
        self.version = self.max_version;
        self.mutable = mutable;
        self.var_type = typ.clone();
    }
}

impl Z3Value {
    fn guess_type(&self) -> Type {
        match self {
            Z3Value::Void => Type {
                name: "void".to_owned(),
                type_args: vec![],
            },
            Z3Value::Bool(_) => Type {
                name: "bool".to_owned(),
                type_args: vec![],
            },
            Z3Value::Int(_) => Type {
                name: "int".to_owned(),
                type_args: vec![],
            },
            Z3Value::Str(_) => Type {
                name: "str".to_owned(),
                type_args: vec![],
            },
            Z3Value::Array(_, e) => Type {
                name: "Array".to_owned(),
                type_args: vec![TypeArg::Type(e.clone())],
            },
            Z3Value::Vec(_, e) => Type {
                name: "Vec".to_owned(),
                type_args: vec![TypeArg::Type(e.clone())],
            },
            Z3Value::UnknownSeq(xs) => Type {
                name: "UnknownSeq".to_owned(),
                type_args: vec![TypeArg::Type(xs[0].guess_type())],
            }
        }
    }

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

    fn eq(&self, other: &Z3Value) -> Result<z3::ast::Bool, CheckError> {
        match (self, other) {
            (Z3Value::Bool(a), Z3Value::Bool(b)) => Ok(a.eq(b)),
            (Z3Value::Int(a), Z3Value::Int(b)) => Ok(a.eq(b)),
            (Z3Value::Str(a), Z3Value::Str(b)) => Ok(a.eq(b)),
            (Z3Value::Vec(a, t), Z3Value::Vec(b, u)) if t==u => Ok(a.eq(b)),
            (Z3Value::Array(a, t), Z3Value::Array(b, u)) if t==u => Ok(a.eq(b)),
            (Z3Value::Vec(a, t), Z3Value::UnknownSeq(xs)) => {
                let mut eqs = vec![a.length().eq(&z3::ast::Int::from_u64(xs.len() as u64))];
                for (i, x) in xs.iter().enumerate() {
                    let idx = z3::ast::Int::from_u64(i as u64);
                    let elem = a.nth(&idx);
                    let x_dyn = x.to_z3_dynamic()?;
                    eqs.push(elem.eq(&x_dyn));
                }
                Ok(z3::ast::Bool::and(&eqs))
            }
            _ => Err(CheckError {
                message: format!("Type mismatch or unsupported type in equality: {} vs {}", self, other),
            }),
        }
    }

    fn ne(&self, other: &Z3Value) -> Result<z3::ast::Bool, CheckError> {
        self.eq(other).map(|eq_ast| eq_ast.not())
    }

    fn bool(&self) -> Result<&z3::ast::Bool, CheckError> {
        match self {
            Z3Value::Bool(b) => Ok(b),
            _ => Err(CheckError {
                message: "Expected Bool type".to_owned(),
            }),
        }
    }

    fn int(&self) -> Result<&z3::ast::Int, CheckError> {
        match self {
            Z3Value::Int(i) => Ok(i),
            _ => Err(CheckError {
                message: "Expected Int type".to_owned(),
            }),
        }
    }

    fn string(&self) -> Result<&z3::ast::String, CheckError> {
        match self {
            Z3Value::Str(s) => Ok(s),
            _ => Err(CheckError {
                message: "Expected String type".to_owned(),
            }),
        }
    }

    fn void(&self) -> Result<(), CheckError> {
        match self {
            Z3Value::Void => Ok(()),
            _ => Err(CheckError {
                message: "Expected Void type".to_owned(),
            }),
        }
    }

    fn to_z3_dynamic(&self) -> Result<z3::ast::Dynamic, CheckError> {
        match self {
            Z3Value::Bool(b) => Ok(b.clone().into()),
            Z3Value::Int(i) => Ok(i.clone().into()),
            Z3Value::Str(s) => Ok(s.clone().into()),
            Z3Value::Vec(seq, _) => Ok(seq.clone().into()),
            Z3Value::Array(seq, _) => Ok(seq.clone().into()),
            Z3Value::Void => Err(CheckError {
                message: "Void type cannot be converted to Z3 dynamic".to_owned(),
            }),
            Z3Value::UnknownSeq(_) => Err(CheckError {
                message: "UnknownSeq type cannot be converted to Z3 dynamic".to_owned(),
            }),
        }
    }
}

impl Literal {
    fn z3_check(&self) -> Result<Z3Value, CheckError> {
        match self {
            Literal::I64(value) => Ok(Z3Value::Int(z3::ast::Int::from_i64(*value))),
            Literal::U64(value) => Ok(Z3Value::Int(z3::ast::Int::from_u64(*value))),
            Literal::Str(value) => Ok(Z3Value::Str(z3::ast::String::from_str(value)?)),
        }
    }
}

impl Type {
    fn int_bounds(&self) -> (Option<z3::ast::Int>, Option<z3::ast::Int>) {
        match self.name.as_str() {
            "u8" => (
                Some(z3::ast::Int::from_u64(0)),
                Some(z3::ast::Int::from_u64(0xff)),
            ),
            "i8" => (
                Some(z3::ast::Int::from_i64(-0x80)),
                Some(z3::ast::Int::from_i64(0x7f)),
            ),
            "u16" => (
                Some(z3::ast::Int::from_u64(0)),
                Some(z3::ast::Int::from_u64(0xffff)),
            ),
            "i16" => (
                Some(z3::ast::Int::from_i64(-0x8000)),
                Some(z3::ast::Int::from_i64(0x7fff)),
            ),
            "u32" => (
                Some(z3::ast::Int::from_u64(0)),
                Some(z3::ast::Int::from_u64(0xffffffff)),
            ),
            "i32" => (
                Some(z3::ast::Int::from_i64(-0x80000000)),
                Some(z3::ast::Int::from_i64(0x7fffffff)),
            ),
            "u64" => (
                Some(z3::ast::Int::from_u64(0)),
                Some(z3::ast::Int::from_u64(0xffffffff_ffffffff)),
            ),
            "i64" => (
                Some(z3::ast::Int::from_i64(-0x80000000_00000000)),
                Some(z3::ast::Int::from_i64(0x7fffffff_ffffffff)),
            ),
            "nat" => (Some(z3::ast::Int::from_u64(0)), None),
            "int" => (None, None),
            _ => unreachable!("int_bounds called on non-integer type"),
        }
    }

    fn check_value(&self, value: &Z3Value, env: &mut Env) -> Result<(), CheckError> {
        self.check_or_assume_value(value, env, AssertMode::Assert)
    }

    fn check_or_assume_value(&self, value: &Z3Value, env: &mut Env, mode: AssertMode) -> Result<(), CheckError> {
        match self.name.as_str() {
            "u8" | "i8" | "u16" | "i16" | "u32" | "i32" | "u64" | "i64" | "nat" | "int" => {
                let v = value.int()?;
                let (lower, upper) = self.int_bounds();
                if let Some(lower) = lower {
                    env.assert_or_assume(&v.ge(&lower), "Lower bound check failed", mode)?;
                }
                if let Some(upper) = upper {
                    env.assert_or_assume(&v.le(&upper), "Upper bound check failed", mode)?;
                }
                Ok(())
            }
            "bool" => {
                value.bool()?;
                Ok(())
            }
            "str" => {
                value.string()?;
                Ok(())
            }
            "void" => {
                value.void()
            }
            "Vec" => {
                if let Some(TypeArg::Type(expected_elem_type)) = self.type_args.get(0) {
                    match value {
                        Z3Value::Vec(v, elem_type) => {
                            if elem_type == expected_elem_type {
                                Ok(())
                            } else {
                                return Err(CheckError {
                                    message: "Element type mismatch in Vec".to_owned(),
                                });
                            }
                        }
                        Z3Value::UnknownSeq(xs) => {
                            for x in xs {
                                expected_elem_type.check_value(x, env)?;
                            }
                            Ok(())
                        }
                        _ => {
                            return Err(CheckError {
                                message: format!("Expected Vec type, got {}", value),
                            });
                        }
                    }
                } else {
                    Err(CheckError {
                        message: "Vector type missing element type".to_owned(),
                    })
                }
            }
            _ => Err(CheckError {
                message: format!("Unsupported type for check_or_assume_value: {}", self),
            }),
        }
    }

    fn coerce_z3_dynamic(&self, dyn_ast: &z3::ast::Dynamic) -> Result<Z3Value, CheckError> {
        match self.name.as_str() {
            "u8" | "i8" | "u16" | "i16" | "u32" | "i32" | "u64" | "i64" | "nat" | "int" => {
                Ok(Z3Value::Int(dyn_ast.as_int().ok_or_else(|| {
                    CheckError {
                        message: "Expected Int type".to_owned(),
                    }
                })?))
            }
            "bool" => Ok(Z3Value::Bool(dyn_ast.as_bool().ok_or_else(|| {
                CheckError {
                    message: "Expected Bool type".to_owned(),
                }
            })?)),
            "str" => Ok(Z3Value::Str(dyn_ast.as_string().ok_or_else(|| {
                CheckError {
                    message: "Expected String type".to_owned(),
                }
            })?)),
            "void" => Err(CheckError {
                message: "Void type cannot be converted from Z3 dynamic".to_owned(),
            }),
            _ => Err(CheckError {
                message: format!("Unsupported type for coerce_z3_dynamic: {}", self),
            }),
        }
    }

    // fn check_z3_dynamic(&self, dyn_ast: &z3::ast::Dynamic, env: &mut Env) -> Result<Z3Value, CheckError> {
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

    fn to_z3_const(&self, name: &str) -> Result<Z3Value, CheckError> {
        match self.name.as_str() {
            "u8" | "i8" | "u16" | "i16" | "u32" | "i32" | "u64" | "i64" | "nat" | "int" =>
                Ok(Z3Value::Int(z3::ast::Int::new_const(name))),
            "bool" => Ok(Z3Value::Bool(z3::ast::Bool::new_const(name))),
            "str" => Ok(Z3Value::Str(z3::ast::String::new_const(name))),
            "void" => Ok(Z3Value::Void),
            "Vec" => {
                if let Some(TypeArg::Type(elem_type)) = self.type_args.get(0) {
                    let elem_sort = elem_type.to_z3_sort()?;
                    Ok(Z3Value::Vec(z3::ast::Seq::new_const(name, &elem_sort), elem_type.clone()))
                } else {
                    Err(CheckError {
                        message: "Vector type missing element type".to_owned(),
                    })
                }
            }
            "Array" => {
                if let Some(TypeArg::Type(elem_type)) = self.type_args.get(0) {
                    let elem_sort = elem_type.to_z3_sort()?;
                    Ok(Z3Value::Array(z3::ast::Seq::new_const(name, &elem_sort), elem_type.clone()))
                } else {
                    Err(CheckError {
                        message: "Array type missing element type".to_owned(),
                    })
                }
            }
            _ => Err(CheckError {
                message: format!("Unsupported type for to_z3_const: {}", self),
            }),
        }
    }
}

impl AssignOp {
    fn relate(
        &self,
        old_left: Z3Value,
        new_left: Z3Value,
        right: Z3Value,
    ) -> Result<z3::ast::Bool, CheckError> {
        match self {
            AssignOp::Assign => new_left.eq(&right),
            AssignOp::PlusAssign => {
                let left_int = old_left.int()?;
                let right_int = right.int()?;
                Ok(new_left.int()?.eq(left_int + right_int))
            }
            AssignOp::MinusAssign => {
                let left_int = old_left.int()?;
                let right_int = right.int()?;
                Ok(new_left.int()?.eq(left_int - right_int))
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

    fn get_var(&self, name: &str) -> Result<Z3Value, CheckError> {
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
    ) -> Result<Z3Value, CheckError> {
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

    fn assign(&mut self, var: &str, op: AssignOp, value: Z3Value) -> Result<(), CheckError> {
        let info = self.vars.get_mut(var).ok_or(CheckError {
            message: format!("Undefined variable: {}", var),
        })?;
        let ty = info.var_type.clone();
        if !info.mutable {
            return Err(CheckError {
                message: format!("Cannot assign to immutable variable: {}", var),
            });
        }
        let old_var = info.z3_const()?;
        info.mutate();
        let new_var = info.z3_const()?;
        self.assume(op.relate(old_var, new_var.clone(), value)?);
        // println!("Checking value of assigned variable {} to type {}", new_var, ty);
        ty.check_value(&new_var.clone(), self)
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
        args: &[Z3Value],
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
            new_env.assume(new_var.eq(value)?);
            arg.arg_type.check_value(&new_var, &mut new_env)?;
        }
        Ok(new_env)
    }

    fn check_preconditions(&mut self, func: &CheckedFunction) -> Result<(), CheckError> {
        for precondition in &func.preconditions {
            let cond_z3_value = precondition.z3_check(self)?;
            self.assert(cond_z3_value.bool()?, "Precondition failed")?;
        }
        Ok(())
    }
}

impl Stmt {
    fn z3_check(&self, env: &mut Env) -> Result<(), CheckError> {
        match self {
            Stmt::Expr(expr) => {
                expr.z3_check(env)?;
                Ok(())
            }
            Stmt::Let { name, value } => {
                let z3_value = value.z3_check(env)?;
                let typ = z3_value.guess_type();
                let z3_var = env.insert_var(name, false, &typ)?;
                env.assume(z3_var.eq(&z3_value)?);
                typ.check_value(&z3_var, env)?;
                Ok(())
            }
            Stmt::LetMut { name, typ, value } => {
                let z3_value = value.z3_check(env)?;
                let z3_var = env.insert_var(name, true, typ)?;
                typ.check_value(&z3_value, env)?;
                env.assume(z3_var.eq(&z3_value)?);
                // println!("Checking value of variable {} to type {}", z3_var, typ);
                Ok(())
            }
            Stmt::Assign { name, op, value } => {
                let z3_value = value.z3_check(env)?;
                env.assign(name, *op, z3_value)
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
//     let mut z3_elems:Vec<z3::ast::Dynamic> = Vec::new();
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

fn z3_function_call(name: &str, args: &[Z3Value], env: &mut Env) -> Result<Z3Value, CheckError> {
    match (name, args.len()) {
        ("==", 2) => {
            let eq_ast = args[0].eq(&args[1])?;
            Ok(Z3Value::Bool(eq_ast))
        }
        ("!=", 2) => {
            let eq_ast = args[0].ne(&args[1])?;
            Ok(Z3Value::Bool(eq_ast))
        }
        ("<", 2) => {
            let left_int = args[0].int()?;
            let right_int = args[1].int()?;
            Ok(Z3Value::Bool(left_int.lt(right_int)))
        }
        ("<=", 2) => {
            let left_int = args[0].int()?;
            let right_int = args[1].int()?;
            Ok(Z3Value::Bool(left_int.le(right_int)))
        }
        (">", 2) => {
            let left_int = args[0].int()?;
            let right_int = args[1].int()?;
            Ok(Z3Value::Bool(left_int.gt(right_int)))
        }
        (">=", 2) => {
            let left_int = args[0].int()?;
            let right_int = args[1].int()?;
            Ok(Z3Value::Bool(left_int.ge(right_int)))
        }
        ("+", 2) => Ok(Z3Value::Int(args[0].int()? + args[1].int()?)),
        ("-", 2) => Ok(Z3Value::Int(args[0].int()? - args[1].int()?)),
        ("assert", 1) => {
            let bool_arg = args[0].bool()?;
            env.assert(bool_arg, "Assertion failed")?;
            Ok(Z3Value::Void)
        }
        ("println", 1) => {
            args[0].string()?;
            env.prints();
            Ok(Z3Value::Void)
        }
        _ => {
            if let Some(user_func) = env.other_funcs.iter().find(|f| f.name == name) {
                let user_func = user_func.clone(); // clone it because we're doing other things to env and they conflict
                let func_decl = user_func.z3_func_decl()?;
                let mut call_env = env.enter_call_scope(&user_func, args)?;
                call_env.check_preconditions(&user_func)?;

                let z3_args = args
                    .iter()
                    .map(|arg| arg.to_z3_dynamic())
                    .collect::<Result<Vec<_>, _>>()?;
                let z3_argrefs = z3_args
                    .iter()
                    .map(|a| a as &dyn z3::ast::Ast)
                    .collect::<Vec<&dyn z3::ast::Ast>>();

                let retvar = call_env
                    .insert_var(&user_func.return_value, false, &user_func.return_type)?;

                // we can assume the bounds on the return value
                user_func.return_type.check_or_assume_value(&retvar, &mut call_env, AssertMode::Assume)?;
                // we can also assume the postconditions
                for postcondition in &user_func.postconditions {
                    let cond_z3_value = postcondition.z3_check(&mut call_env)?;
                    call_env.assume(cond_z3_value.bool()?.clone());
                }
                // don't forget the side effects
                for effect in &user_func.side_effects {
                    call_env.side_effects.insert(effect.clone());
                }

                // If body is visible, check it (which will add relevant assumptions)
                if let Some(body) = &user_func.body {
                    let body_z3_value = body.z3_check(&mut call_env)?;
                    env.assume(retvar.eq(&body_z3_value)?);
                }

                // fold back into main env
                env.fold_in_scope(&call_env);

                // unify return value with function call
                let ast = func_decl.apply(&z3_argrefs);
                let val = user_func.return_type.coerce_z3_dynamic(&ast)?; // don't perform type check - this is assumed
                env.assume(retvar.eq(&val)?);

                Ok(val)
            } else {
                Err(CheckError {
                    message: format!("Undefined function: {}", name),
                })
            }
        }
    }
}

impl Expr {
    fn z3_check(&self, env: &mut Env) -> Result<Z3Value, CheckError> {
        match self {
            Expr::Literal(literal) => literal.z3_check(),
            Expr::Variable(name) => env.get_var(name),
            Expr::FunctionCall { name, args } => {
                let z3args = args
                    .iter()
                    .map(|arg| arg.z3_check(env))
                    .collect::<Result<Vec<_>, _>>()?;
                z3_function_call(name, &z3args, env)
            }
            Expr::Semicolon(stmt, expr) => {
                stmt.z3_check(env)?;
                expr.z3_check(env)
            }
            Expr::Sequence(elements) => {
                let z3elems = elements
                    .iter()
                    .map(|elem| elem.z3_check(env))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Z3Value::UnknownSeq(z3elems))
            }
        }
    }
}

fn z3_check_funcdef(
    func: &FuncDef,
    other_funcs: &[CheckedFunction],
) -> Result<CheckedFunction, CheckError> {
    let mut env = Env::new(other_funcs, &func.sees);
    for arg in &func.args {
        let arg_var = env.insert_var(&arg.name, false, &arg.arg_type)?;
        arg.arg_type.check_or_assume_value(&arg_var, &mut env, AssertMode::Assume)?;
    }
    for precondition in &func.preconditions {
        let cond_z3_value = precondition.z3_check(&mut env)?;
        env.assume(cond_z3_value.bool()?.clone());
    }
    let body_z3_value = func.body.z3_check(&mut env)?;
    func.return_type.check_value(&body_z3_value, &mut env)?;

    // now check all the postconditions
    if !func.postconditions.is_empty() {
        if let Some(ret) = &func.return_name {
            let ret_var = env.insert_var(ret, false, &func.return_type)?;
            env.assume(ret_var.eq(&body_z3_value)?);
            for postcondition in &func.postconditions {
                let cond_z3_value = postcondition.z3_check(&mut env)?;
                env.assert(cond_z3_value.bool()?, "Postcondition failed")?;
            }
        } else {
            return Err(CheckError {
                message: "Postconditions specified but no return variable name provided".to_owned(),
            });
        }
    }

    print!("Checked function: {}", func.name);
    env.print_side_effects();
    Ok(CheckedFunction {
        name: func.name.clone(),
        args: func.args.clone(),
        return_type: func.return_type.clone(),
        return_value: func
            .return_name
            .clone()
            .unwrap_or_else(|| "__ret__".to_owned()),
        side_effects: env.side_effects,
        preconditions: func.preconditions.clone(),
        postconditions: func.postconditions.clone(),
        body: Some(func.body.clone()),
    })
}

pub fn z3_check(source_file: &SourceFile) -> Result<(), CheckError> {
    let mut other_funcs = vec![];
    for func in &source_file.functions {
        let checked_func = z3_check_funcdef(func, &other_funcs)?;
        other_funcs.push(checked_func);
    }
    Ok(())
}
