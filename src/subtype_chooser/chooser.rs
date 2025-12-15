use std::collections::HashMap;

use z3::ast::{Dynamic, Datatype};

use crate::{check::builtins::lookup_builtin, syntax::ast::{Expr, ExprKind, FuncDef, SourceFile, Type, TypeArg}};

const INT_TYPES:[&'static str; 8] = ["i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64"];

#[derive(Debug)]
pub struct OptimizationError{pub message: String}

impl std::fmt::Display for OptimizationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for OptimizationError {}

struct Chooser {
    soft_constraints: Vec<(z3::ast::Bool, usize)>,
    next_id: usize,
    functions: HashMap<String, FuncDef>,
    int_choice_dt: z3::DatatypeSort,
    verbosity: u8,
}

impl Type {
    fn is_int_id(&self) -> bool {
        self.type_args.is_empty() && self.name.starts_with("__Int") && self.name.ends_with("__")
    }

    fn is_int_or_int_id(&self) -> bool {
        self.is_int() || self.is_int_id()
    }
}

impl Expr {
    fn is_literal(&self) -> bool {
        matches!(self, Expr::Expr { kind: ExprKind::Literal{..}, .. })
    }
}

impl Chooser {
    fn new(verbosity: u8) -> Self {
        let mut dt_builder = z3::DatatypeBuilder::new("IntChoice");
        for int_type in &INT_TYPES {
            dt_builder = dt_builder.variant(int_type, vec![]);
        }
        let int_choice_dt = dt_builder.finish();
        Chooser {
            soft_constraints: vec![],
            next_id: 0,
            functions: HashMap::new(),
            int_choice_dt,
            verbosity,
        }
    }

    fn fresh_int_id(&mut self) -> String {
        let id = format!("__Int{}__", self.next_id);
        self.next_id += 1;
        id
    }

    fn give_int_ids(&mut self, typ: &mut Type) {
        if typ.is_int() {
            typ.name = self.fresh_int_id();
        }
        for arg in &mut typ.type_args {
            if let TypeArg::Type(t) = arg {
                self.give_int_ids(t);
            }
        }
    }

    fn z3_typeval(&self, typ: &Type) -> Result<Dynamic, OptimizationError> {
        if typ.is_int() {
            let index = INT_TYPES.iter().position(|&t| t == &typ.name).ok_or(OptimizationError{message: format!("Cannot optimize int type {}", typ.name)})?;
            Ok(self.int_choice_dt.variants[index].constructor.apply(&[]))
        } else if typ.is_int_id() {
            Ok(Datatype::new_const(typ.name.clone(), &self.int_choice_dt.sort).into())
        } else {
            Err(OptimizationError{message: format!("Cannot optimize type {}", typ.name)})
        }
    }

    fn soft_unify_types(&mut self, t0: &Type, t1: &Type, penalty: usize) -> Result<(), OptimizationError> {
        // println!("Soft unifying types: {:?} and {:?} with penalty {}", t0, t1, penalty);
        if t0 == t1 {
            return Ok(());
        }
        if t0.is_int_or_int_id() && t1.is_int_or_int_id() {
            let z3_t0 = self.z3_typeval(t0)?;
            let z3_t1 = self.z3_typeval(t1)?;
            let eq = z3_t0.eq(&z3_t1);
            self.soft_constraints.push((eq, penalty));
            if self.verbosity >= 2 {
                println!("Adding soft constraint: {:?} == {:?} with penalty {}", t0, t1, penalty);
            }
            Ok(())
        } else if t0.is_round_seq() && t1.is_round_seq() {
            let args0 = t0.get_round_elem_type_vector().unwrap();
            let args1 = t1.get_round_elem_type_vector().unwrap();
            assert!(args0.len() == args1.len());
            for (arg0, arg1) in args0.iter().zip(args1.iter()) {
                self.soft_unify_types(arg0, arg1, penalty)?;
            }
            Ok(())
        } else if t0.is_square_seq() && t1.is_square_seq() {
            let arg0 = t0.get_uniform_square_elem_type().unwrap();
            let arg1 = t1.get_uniform_square_elem_type().unwrap();
            self.soft_unify_types(&arg0, &arg1, penalty.max(10))  // increase penalty for Vec/Array elements
        } else {
            assert!(t0.name == t1.name, "Cannot unify types {:?} and {:?}", t0, t1);
            assert!(t0.type_args.len() == t1.type_args.len());
            Ok(())
        }
    }

    fn give_int_ids_to_expr(&mut self, expr: &mut Expr, env: &HashMap<String, Type>) {
        match expr {
            Expr::Expr { kind, args, type_instantiations, info } => {
                for ty in type_instantiations.iter_mut() {
                    self.give_int_ids(ty);
                }
                for arg in args {
                    self.give_int_ids_to_expr(arg, env);
                }
                let (arg_types, mut ret_type) = self.signature(&kind, type_instantiations, info.chooser.int_instantiation.as_ref());
                if arg_types.iter().any(|t|t.is_int()) || ret_type.is_int() {
                    // choose an int type for all remaining int arguments
                    let t = self.fresh_int_id();
                    info.chooser.int_instantiation = Some(Type::basic(&t));

                    // recompute signature now that we've chosen an int instantiation
                    (_, ret_type) = self.signature(&kind, type_instantiations, info.chooser.int_instantiation.as_ref());
                }
                info.typ = Some(ret_type);
            }
            Expr::Variable { name, info } => {
                info.typ = Some(env.get(name).unwrap().clone());
            }
            Expr::Lambda { args, body, info } => {
                let mut new_env = env.clone();
                let mut arg_types = vec![];
                for arg in args {
                    new_env.insert(arg.name.clone(), arg.arg_type.clone());
                    arg_types.push(arg.arg_type.clone());
                }
                self.give_int_ids_to_expr(body, &new_env);
                info.typ = Some(Type::lambda(&arg_types, &body.typ()));
            }
            Expr::Let { name, typ, value, body, info, .. } => {
                self.give_int_ids_to_expr(value, env);
                let mut new_env = env.clone();
                if let Some(t) = typ {
                    new_env.insert(name.clone(), t.clone());
                } else {
                    let val_type = value.typ();
                    new_env.insert(name.clone(), val_type.clone());
                }
                self.give_int_ids_to_expr(body, &new_env);
                info.typ = Some(body.typ());
            }
        }
    }

    fn soft_checks_for_expr(&mut self, expr: &Expr) -> Result<(), OptimizationError> {
        match expr {
            Expr::Expr { kind, args, type_instantiations, info } => {
                let (expected_arg_types, expected_ret_type) = self.signature(kind, type_instantiations, info.chooser.int_instantiation.as_ref());
                assert!(expected_arg_types.len() == args.len());
                for (arg, expected_type) in args.iter().zip(expected_arg_types.iter()) {
                    self.soft_unify_types(&arg.typ(), expected_type, 1)?;
                    self.soft_checks_for_expr(arg)?;
                }
                self.soft_unify_types(&expr.typ(), &expected_ret_type, 1)?;
            }
            Expr::Variable { .. } => {}
            Expr::Lambda { body, .. } => {
                self.soft_checks_for_expr(body)?;
            }
            Expr::Let { value, body, typ, .. } => {
                self.soft_checks_for_expr(value)?;
                if typ.is_some() {
                    self.soft_unify_types(&value.typ(), typ.as_ref().unwrap(), 1)?;
                }
                self.soft_checks_for_expr(body)?;
            }
        }
        Ok(())
    }

    fn signature(&self, kind: &ExprKind, type_instantiations: &[Type], int_instantiation: Option<&Type>) -> (Vec<Type>, Type) {
        let (arg_types, ret_type) = match kind {
            ExprKind::Function { name, .. } => {
                let func_def = lookup_builtin(name).or_else(|| {
                    self.functions.get(name).cloned()
                }).expect(&format!("Function {} not found in signature lookup", name));

                let ret_type = func_def.return_type.instantiate(&func_def.type_params, type_instantiations).unwrap();
                let arg_types = func_def.args.iter().map(|arg| {
                    arg.arg_type.instantiate(&func_def.type_params, type_instantiations).unwrap()
                }).collect();
                (arg_types, ret_type)
            }
            ExprKind::Literal { literal } => {
                assert!(type_instantiations.is_empty());
                (vec![], literal.typ())
            }
            ExprKind::SquareSequence { len } => {
                assert!(type_instantiations.len() == 1);
                (vec![type_instantiations[0].clone(); *len], type_instantiations[0].vec())
            }
            ExprKind::RoundSequence { len } => {
                assert!(type_instantiations.len() == *len);
                (type_instantiations.to_owned(), Type::tuple(type_instantiations))
            }
            ExprKind::TupleAt { len, index } => {
                assert!(type_instantiations.len() == *len);
                let elem_type = type_instantiations[*index].clone();
                (vec![Type::tuple(type_instantiations)], elem_type)
            }
            ExprKind::UnknownSequenceAt{..} => unreachable!(),
        };
        if int_instantiation.is_some() {
            let int_type = int_instantiation.unwrap();
            let new_arg_types = arg_types.into_iter().map(|t| {
                if t.is_int() {
                    int_type.clone()
                } else {
                    t
                }
            }).collect();
            let new_ret_type = if ret_type.is_int() {
                int_type.clone()
            } else {
                ret_type
            };
            (new_arg_types, new_ret_type)
        } else {
            (arg_types, ret_type)
        }
    }

    fn conclusion(&self) -> Result<HashMap<String, Type>, OptimizationError> {
        let solver = z3::Optimize::new();
        for (soft_constraint, penalty) in &self.soft_constraints {
            solver.assert_soft(soft_constraint, *penalty as u32, None);
        }
        if solver.check(&[]) != z3::SatResult::Sat {
            return Err(OptimizationError{message: "Could not solve optimization constraints".to_string()});
        }
        let model = solver.get_model().unwrap();
        let mut result = HashMap::new();
        for int_id in 0..self.next_id {
            let type_name = format!("__Int{}__", int_id);
            let z3_const = Datatype::new_const(type_name.clone(), &self.int_choice_dt.sort);
            let z3_value:Dynamic = model.eval(&z3_const, true).ok_or(OptimizationError{message: format!("Could not evaluate type for {}", type_name)})?.into();
            let mut found = false;
            for i in 0..INT_TYPES.len() {
                if z3_value.ast_eq(&self.int_choice_dt.variants[i].constructor.apply(&[])) {
                    let concrete_type = Type::basic(INT_TYPES[i]);
                    result.insert(type_name.clone(), concrete_type);
                    found = true;
                    break;
                }
            }
            if !found {
                return Err(OptimizationError{message: format!("Could not find concrete type for {}", type_name)});
            }
        }
        Ok(result)
    }

    fn fill_in_expr(&self, expr: &mut Expr, int_type_map: &HashMap<String, Type>) {
        match expr {
            Expr::Expr { type_instantiations, info, args, .. } => {
                for ty in type_instantiations.iter_mut() {
                    if ty.is_int_id() {
                        let concrete_type = int_type_map.get(&ty.name).unwrap().clone();
                        *ty = concrete_type;
                    }
                }
                if let Some(int_inst) = &info.chooser.int_instantiation {
                    if int_inst.is_int_id() {
                        let concrete_type = int_type_map.get(&int_inst.name).unwrap().clone();
                        info.chooser.int_instantiation = Some(concrete_type);
                    }
                }
                for arg in args {
                    self.fill_in_expr(arg, int_type_map);
                }
            }
            Expr::Variable { info, .. } => {
                if let Some(int_inst) = &info.chooser.int_instantiation {
                    if int_inst.is_int_id() {
                        let concrete_type = int_type_map.get(&int_inst.name).unwrap().clone();
                        info.typ = Some(concrete_type);
                    }
                }
            }
            Expr::Lambda { body, info, .. } => {
                self.fill_in_expr(body, int_type_map);
                if let Some(int_inst) = &info.chooser.int_instantiation {
                    if int_inst.is_int_id() {
                        let concrete_type = int_type_map.get(&int_inst.name).unwrap().clone();
                        info.typ = Some(concrete_type);
                    }
                }
            }
            Expr::Let { value, body, info, .. } => {
                self.fill_in_expr(value, int_type_map);
                self.fill_in_expr(body, int_type_map);
                if let Some(int_inst) = &info.chooser.int_instantiation {
                    if int_inst.is_int_id() {
                        let concrete_type = int_type_map.get(&int_inst.name).unwrap().clone();
                        info.typ = Some(concrete_type);
                    }
                }
            }
        }
    }
}

pub fn subtype_chooser(source_file: &mut SourceFile, verbosity: u8) -> Result<(), OptimizationError> {
    let mut chooser = Chooser::new(verbosity);

    for func in &mut source_file.functions {
        if verbosity >= 1 {
            println!("Choosing subtypes for function {}", func.name);
        }
        let mut env = HashMap::new();
        for arg in &func.args {
            env.insert(arg.name.clone(), arg.arg_type.clone());
        }
        chooser.give_int_ids_to_expr(&mut func.body, &env);
        if verbosity >= 2 {
            println!("After giving int ids:\n{:?}", func.body);
        }
        chooser.soft_checks_for_expr(&mut func.body)?;
        chooser.functions.insert(func.name.clone(), func.clone());
        let conc = chooser.conclusion()?;
        chooser.fill_in_expr(&mut func.body, &conc);
        if verbosity >= 2 {
            println!("{:?}", conc);
            println!("After filling in types:\n{:?}", func.body);
        }
    }

    Ok(())
}