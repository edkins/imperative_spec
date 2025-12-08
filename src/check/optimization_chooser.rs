use std::collections::HashMap;

use crate::{
    check::{
        overloads::ConcreteOptimization,
        ztype_ast::{TExpr, TFuncAttribute, TFuncDef, TSourceFile, TStmt},
    },
    syntax::ast::{Literal, Type},
};

#[derive(Clone, Default)]
struct CEnv {
    uses: HashMap<String, TypeExpectations>,
    decisions: Vec<String>,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum TypeSize {
    S32,
    S64,
    Inf,
}

#[derive(Clone, Default)]
struct TypeExpectations(Vec<Type>);

#[derive(Debug)]
pub struct OptimizationError {
    message: String,
}

impl OptimizationError {
    fn new(message: &str) -> Self {
        OptimizationError {
            message: message.to_owned(),
        }
    }
}

impl std::fmt::Display for OptimizationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "OptimizationError: {}", self.message)
    }
}

impl std::error::Error for OptimizationError {}

impl Type {
    fn zsize(&self) -> TypeSize {
        match self.name.as_str() {
            "u32" | "i32" | "z32" => TypeSize::S32,
            "u64" | "i64" | "z64" => TypeSize::S64,
            _ => TypeSize::Inf,
        }
    }
}

impl std::fmt::Display for TypeExpectations {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let types_str = self
            .0
            .iter()
            .map(|t| t.to_string())
            .collect::<Vec<String>>()
            .join(", ");
        write!(f, "[{}]", types_str)
    }
}

impl TypeExpectations {
    fn new(expected_type: &Type) -> Self {
        if expected_type.is_void() {
            TypeExpectations(vec![])
        } else {
            TypeExpectations(vec![expected_type.clone()])
        }
    }

    fn add_type(&mut self, typ: Type) {
        if !self.0.contains(&typ) {
            self.0.push(typ);
        }
    }

    fn push(&mut self, other: &TypeExpectations) {
        for typ in &other.0 {
            self.add_type(typ.clone());
        }
    }

    fn enough_to_get_from(&self, established_type: &Type, optim_type: &Type) -> bool {
        if established_type.is_subtype_of(optim_type) {
            return true;
        }
        if established_type.is_int() && optim_type.is_int() {
            for user in &self.0 {
                if user.is_int() && user.zsize() <= optim_type.zsize() {
                    return true;
                }
            }
        }
        false
    }

    fn decide_optimization(
        &self,
        established_type: &Type,
        optims: &[ConcreteOptimization],
    ) -> Option<ConcreteOptimization> {
        // println!(
        //     "Deciding optimization out of {:?} for established type {} with expectations {}",
        //     optims.iter().map(|o| o.debug_name.clone()).collect::<Vec<String>>(),
        //     established_type,
        //     self
        // );
        for optim in optims {
            if self.enough_to_get_from(established_type, &optim.func.return_type) {
                return Some(optim.clone());
            }
        }
        // println!("No optimization chosen");
        None
    }

    fn decide_literal(&self, literal: &Literal) -> TExpr {
        TExpr::Literal(literal.clone()) // TODO: SizedLiteral
    }

    fn seq_element(&self) -> TypeExpectations {
        let mut elem_expectations = TypeExpectations::default();
        for typ in &self.0 {
            if let Some(elem_type) = typ.get_named_seq() {
                elem_expectations.add_type(elem_type.clone());
            }
        }
        elem_expectations
    }
}

impl CEnv {
    fn hide_var(&mut self, name: &str) {
        self.uses.remove(name);
    }

    fn add_use(&mut self, name: String, expectations: &TypeExpectations) {
        self.uses.entry(name).or_default().push(expectations);
    }

    fn lookup_expectations(&self, name: &str) -> TypeExpectations {
        self.uses.get(name).cloned().unwrap_or_default()
    }
}

impl TExpr {
    fn choose_optimization(&self, env: &mut CEnv, expectations: &TypeExpectations) -> TExpr {
        match self {
            TExpr::Literal(literal) => expectations.decide_literal(literal),
            TExpr::Variable { name, typ } => {
                env.add_use(name.clone(), expectations);
                TExpr::Variable {
                    name: name.clone(),
                    typ: typ.clone(),
                }
            }
            TExpr::Semicolon(stmt, expr) => {
                let expr = expr.choose_optimization(env, expectations);
                let stmt = stmt.choose_optimization(env);
                TExpr::Semicolon(Box::new(stmt), Box::new(expr))
            }
            TExpr::FunctionCall {
                name,
                args,
                return_type,
                optimizations,
            } => {
                // println!("Choosing optimization for function call {} with expectations {}", name, expectations);
                if let Some(optim) = expectations.decide_optimization(return_type, optimizations) {
                    env.decisions.push(optim.debug_name.clone());
                    assert!(optim.func.arg_types.len() == args.len());
                    TExpr::FunctionCall {
                        name: name.clone(),
                        args: args
                            .iter()
                            .zip(optim.func.arg_types.iter())
                            .map(|(arg, expected_type)| {
                                arg.choose_optimization(env, &TypeExpectations::new(expected_type))
                            })
                            .collect(),
                        return_type: optim.func.return_type.clone(),
                        optimizations: vec![optim],
                    }
                } else {
                    TExpr::FunctionCall {
                        name: name.clone(),
                        args: args
                            .iter()
                            .map(|arg| {
                                arg.choose_optimization(env, &TypeExpectations::new(&arg.typ()))
                            })
                            .collect(),
                        return_type: return_type.clone(),
                        optimizations: vec![],
                    }
                }
            }
            TExpr::Sequence {
                elements,
                elem_type,
            } => {
                let elem_expectations = expectations.seq_element();
                let elements = elements
                    .iter()
                    .map(|elem| elem.choose_optimization(env, &elem_expectations))
                    .collect();
                TExpr::Sequence {
                    elements,
                    elem_type: elem_type.clone(),
                }
            }
            TExpr::EmptySequence => unreachable!("Should have decided empty sequence type earlier"),
            TExpr::Lambda { args, body } => {
                let mut new_env = env.clone();
                for arg in args {
                    new_env.hide_var(&arg.name);
                }
                let body = body.choose_optimization(&mut new_env, expectations);
                TExpr::Lambda {
                    args: args.clone(),
                    body: Box::new(body),
                }
            }
        }
    }
}

impl TStmt {
    fn choose_optimization(&self, env: &mut CEnv) -> TStmt {
        match self {
            TStmt::Expr(expr) => {
                let expr = expr.choose_optimization(env, &TypeExpectations::default());
                TStmt::Expr(expr)
            }
            TStmt::Assign { name, typ, value } => {
                let value = value.choose_optimization(env, &TypeExpectations::new(typ));
                TStmt::Assign {
                    name: name.clone(),
                    typ: typ.clone(),
                    value,
                }
            }
            TStmt::Let {
                name,
                typ,
                mutable,
                type_declared,
                value,
            } => {
                let expectations = if *type_declared {
                    TypeExpectations::new(typ)
                } else {
                    env.lookup_expectations(name)
                };
                let value = value.choose_optimization(env, &expectations);
                TStmt::Let {
                    name: name.clone(),
                    typ: typ.clone(),
                    mutable: *mutable,
                    type_declared: *type_declared,
                    value,
                }
            }
        }
    }
}

impl TFuncDef {
    pub fn choose_optimization(&self) -> Result<TFuncDef, OptimizationError> {
        let mut env = CEnv::default();
        let body = self
            .body
            .choose_optimization(&mut env, &TypeExpectations::new(&self.return_type));

        for attrib in &self.attributes {
            #[allow(irrefutable_let_patterns)]
            if let TFuncAttribute::CheckDecisions(decision_names) = attrib
                && env.decisions != *decision_names
            {
                return Err(OptimizationError::new(&format!(
                    "Decisions mismatch in function {}: expected {:?}, got {:?}",
                    self.name, decision_names, env.decisions
                )));
            }
        }

        Ok(TFuncDef {
            name: self.name.clone(),
            args: self.args.clone(),
            return_name: self.return_name.clone(),
            return_type: self.return_type.clone(),
            attributes: self.attributes.clone(),
            preconditions: self.preconditions.clone(),
            postconditions: self.postconditions.clone(),
            sees: self.sees.clone(),
            body,
        })
    }
}

impl TSourceFile {
    pub fn choose_optimization(&self) -> Result<TSourceFile, OptimizationError> {
        let functions = self
            .functions
            .iter()
            .map(|func| func.choose_optimization())
            .collect::<Result<Vec<TFuncDef>, OptimizationError>>()?;
        Ok(TSourceFile { functions })
    }
}
