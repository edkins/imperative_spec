use std::collections::HashMap;

use crate::{check::builtins::lookup_builtin, syntax::ast::{Expr, ExprKind, FuncDef, Type, TypeArg}};

#[derive(Default)]
struct Chooser {
    soft_constraints: Vec<(z3::ast::Bool, usize)>,
    next_id: usize,
    functions: HashMap<String, FuncDef>,
}

impl Type {
    fn is_int_id(&self) -> bool {
        self.type_args.is_empty() && self.name.starts_with("__Int") && self.name.ends_with("__")
    }
}

impl Chooser {
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

    fn soft_unify_types(&mut self, t0: &Type, t1: &Type, penalty: usize) {
        
    }

    fn give_int_ids_to_expr(&mut self, expr: &mut Expr, env: &HashMap<String, Type>) {
        match expr {
            Expr::Expr { args, type_instantiations, .. } => {
                for ty in type_instantiations {
                    self.give_int_ids(ty);
                }
                for arg in args {
                    self.give_int_ids_to_expr(arg, env);
                }
            }
            Expr::Variable { info, .. } => {
                info.typ = Some(env.get(&info.id).unwrap().clone());
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

    fn signature(&self, kind: &ExprKind, type_instantiations: &[Type]) -> (Vec<Type>, Type) {
        match kind {
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
        }
    }
}
