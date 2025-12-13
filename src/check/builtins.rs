use std::{collections::HashMap, slice::from_ref};
// don't use std::ops::Ops here to avoid circular dependencies

use crate::syntax::ast::{Arg, Expr, FuncDef, Literal, Type, TypeArg};

thread_local! {
    static BUILTIN_FUNCTIONS: HashMap<String, FuncDef> = builtins();
}

fn insert_multiple(map: &mut HashMap<String, FuncDef>, names: &[&str], func: FuncDef) {
    for &name in names {
        if map.contains_key(name) {
            panic!("Builtin function {} defined multiple times", name);
        } else {
            let mut named_func = func.clone();
            named_func.name = name.to_owned();
            map.insert(name.to_owned(), named_func);
        }
    }
}

fn args2(t0: &Type, t1: &Type) -> Vec<Arg> {
    vec![
        Arg {
            name: "arg0".to_owned(),
            mutable: false,
            arg_type: t0.clone(),
        },
        Arg {
            name: "arg1".to_owned(),
            mutable: false,
            arg_type: t1.clone(),
        },
    ]
}

fn args1(t0: &Type) -> Vec<Arg> {
    vec![Arg {
        name: "arg0".to_owned(),
        mutable: false,
        arg_type: t0.clone(),
    }]
}

pub fn known_builtin(name: &'static str) -> FuncDef {
    lookup_builtin(name).expect(&format!("Builtin function {} not found", name))
}

pub fn lookup_builtin(name: &str) -> Option<FuncDef> {
    BUILTIN_FUNCTIONS.with(|builtins| builtins.get(name).cloned())
}

pub fn all_builtins() -> HashMap<String, FuncDef> {
    BUILTIN_FUNCTIONS.with(|builtins| builtins.clone())
}

const DUMMY_BODY: Expr = Expr::Literal(Literal::Unit); // this isn't correct, but the body should be ignored for builtins

impl FuncDef {
    pub fn simple(name: &str, arg_types: &[Type], return_type: &Type) -> Self {
        FuncDef::psimple(name, arg_types, return_type, &[])
    }

    pub fn psimple(
        name: &str,
        arg_types: &[Type],
        return_type: &Type,
        type_param_list: &[&str],
    ) -> Self {
        FuncDef {
            attributes: vec![],
            name: name.to_owned(),
            return_name: "__ret__".to_owned(),
            return_type: return_type.clone(),
            args: arg_types
                .iter()
                .enumerate()
                .map(|(i, t)| Arg {
                    name: format!("arg{}", i),
                    mutable: false,
                    arg_type: t.clone(),
                })
                .collect::<Vec<Arg>>(),
            preconditions: vec![],
            postconditions: vec![],
            body: DUMMY_BODY,
            type_params: type_param_list.iter().map(|s| s.to_string()).collect(),
        }
    }
}

fn builtins() -> HashMap<String, FuncDef> {
    // Don't call ops.rs directly here, or we'll end up with infinite recursion
    let mut functions = HashMap::new();
    let tint = Type::basic("int");
    let tbool = Type::basic("bool");
    let tstr = Type::basic("str");
    let tvoid = Type::basic("void");
    let tparam = Type::basic("T");
    let uparam = Type::basic("U");
    let vect = Type {
        name: "Vec".to_owned(),
        type_args: vec![TypeArg::Type(tparam.clone())],
    };
    let vecu = Type {
        name: "Vec".to_owned(),
        type_args: vec![TypeArg::Type(uparam.clone())],
    };

    let eq = FuncDef::psimple("==", &[tparam.clone(), tparam.clone()], &tbool, &["T"]);
    let ne = FuncDef::psimple("!=", &[tparam.clone(), tparam.clone()], &tbool, &["T"]);
    functions.insert("==".to_owned(), eq.clone());
    functions.insert("!=".to_owned(), ne.clone());

    let lt = FuncDef::simple("<", &[tint.clone(), tint.clone()], &tbool);
    let le = FuncDef::simple("<=", &[tint.clone(), tint.clone()], &tbool);
    let gt = FuncDef::simple(">", &[tint.clone(), tint.clone()], &tbool);
    let ge = FuncDef::simple(">=", &[tint.clone(), tint.clone()], &tbool);
    functions.insert("<".to_owned(), lt.clone());
    functions.insert("<=".to_owned(), le.clone());
    functions.insert(">".to_owned(), gt.clone());
    functions.insert(">=".to_owned(), ge.clone());

    functions.insert(
        "neg".to_owned(),
        FuncDef {
            name: "neg".to_owned(),
            args: args1(&tint),
            return_name: "__ret__".to_owned(),
            return_type: tint.clone(),
            type_params: vec![],
            // optimizations: vec![
            //     Optimization {
            //         debug_name: "z32_neg".to_owned(),
            //         arg_types: vec![z32.clone()],
            //         return_type: z32.clone(),
            //         preconditions: vec![],
            //     },
            //     Optimization {
            //         debug_name: "z64_neg".to_owned(),
            //         arg_types: vec![z64.clone()],
            //         return_type: z64.clone(),
            //         preconditions: vec![],
            //     },
            // ],
            preconditions: vec![],
            attributes: vec![],
            postconditions: vec![],
            body: DUMMY_BODY,
        },
    );

    for (symbol, name) in [("+", "add"), ("-", "sub"), ("*", "mul")] {
        functions.insert(
            symbol.to_owned(),
            FuncDef {
                args: args2(&tint, &tint),
                return_type: tint.clone(),
                type_params: vec![],
                // optimizations: vec![
                //     Optimization {
                //         debug_name: format!("z32_{}", name),
                //         arg_types: vec![z32.clone(), z32.clone()],
                //         return_type: z32.clone(),
                //         preconditions: vec![],
                //     },
                //     Optimization {
                //         debug_name: format!("z64_{}", name),
                //         arg_types: vec![z64.clone(), z64.clone()],
                //         return_type: z64.clone(),
                //         preconditions: vec![],
                //     },
                // ],
                preconditions: vec![],
                attributes: vec![],
                name: symbol.to_owned(),
                return_name: "__ret__".to_owned(),
                postconditions: vec![],
                body: DUMMY_BODY,
            },
        );
    }

    for (symbol, name) in [("/", "div"), ("%", "mod")] {
        functions.insert(
            symbol.to_owned(),
            FuncDef {
                args: args2(&tint, &tint),
                return_type: tint.clone(),
                type_params: vec![],
                // optimizations: vec![
                //     Optimization {
                //         debug_name: format!("u32_{}", name),
                //         arg_types: vec![tu32.clone(), tu32.clone()],
                //         return_type: tu32.clone(),
                //         preconditions: vec![], // the "nonzero" precondition from the main function still applies
                //     },
                //     Optimization {
                //         debug_name: format!("u64_{}", name),
                //         arg_types: vec![tu64.clone(), tu64.clone()],
                //         return_type: tu64.clone(),
                //         preconditions: vec![],
                //     },
                //     Optimization {
                //         debug_name: format!("i32_{}", name),
                //         arg_types: vec![ti32.clone(), ti32.clone()],
                //         return_type: ti32.clone(),
                //         preconditions: vec![],
                //     },
                //     Optimization {
                //         debug_name: format!("i64_{}", name),
                //         arg_types: vec![ti64.clone(), ti64.clone()],
                //         return_type: ti64.clone(),
                //         preconditions: vec![],
                //     },
                // ],
                preconditions: vec![
                    ne.pmake_func_call(&[tint.var("arg1"), Expr::zero()], &[tint.clone()])
                        .unwrap(),
                ],
                attributes: vec![],
                name: symbol.to_owned(),
                return_name: "__ret__".to_owned(),
                postconditions: vec![],
                body: DUMMY_BODY,
            },
        );
    }

    insert_multiple(
        &mut functions,
        &["&&", "||", "==>"],
        FuncDef::simple("", &[tbool.clone(), tbool.clone()], &tbool),
    );

    functions.insert(
        "println".to_owned(),
        FuncDef::simple("println", from_ref(&tstr), &tvoid),
    );
    functions.insert(
        "assert".to_owned(),
        FuncDef::simple("assert", from_ref(&tbool), &tvoid),
    );
    let seq_len = FuncDef::psimple("len", from_ref(&vect), &tint, &["T"]);
    functions.insert("len".to_owned(), seq_len.clone());

    functions.insert(
        "append".to_owned(),
        FuncDef::psimple(
            "append",
            &[vect.clone(), vect.clone()],
            &vect,
            &["T"],
        ),
    );

    functions.insert(
        "seq_map".to_owned(),
        FuncDef::psimple(
            "seq_map",
            &[vect.clone(), Type::lambda(from_ref(&tparam), &uparam)],
            &vecu,
            &["T", "U"],
        ),
    );
    functions.insert(
        "seq_foldl".to_owned(),
        FuncDef::psimple(
            "seq_foldl",
            &[
                vect.clone(),
                Type::lambda(&[uparam.clone(), tparam.clone()], &uparam),
                uparam.clone(),
            ],
            &uparam,
            &["T", "U"],
        ),
    );
    functions.insert(
        "seq_at".to_owned(),
        FuncDef {
            name: "seq_at".to_owned(),
            args: args2(&vect, &tint),
            return_name: "__ret__".to_owned(),
            return_type: tparam.clone(),
            type_params: vec!["T".to_owned()],
            preconditions: vec![
                ge.make_func_call(&[
                    Expr::Variable {
                        name: "arg1".to_owned(),
                        typ: Some(tint.clone()),
                    },
                    Expr::zero(),
                ])
                .unwrap(),
                lt.make_func_call(&[
                    Expr::Variable {
                        name: "arg1".to_owned(),
                        typ: Some(tint.clone()),
                    },
                    seq_len
                        .pmake_func_call(
                            from_ref(&Expr::Variable {
                                name: "arg0".to_owned(),
                                typ: Some(vect.clone()),
                            }),
                            &[tparam.clone()],
                        )
                        .unwrap(),
                ])
                .unwrap(),
            ],
            attributes: vec![],
            postconditions: vec![],
            body: DUMMY_BODY,
        },
    );
    functions.insert(
        "=".to_owned(),
        FuncDef {
            name: "=".to_owned(),
            args: vec![
                Arg {
                    name: "lhs".to_owned(),
                    mutable: false,
                    arg_type: tparam.clone(),
                },
                Arg {
                    name: "rhs".to_owned(),
                    mutable: false,
                    arg_type: tparam.clone(),
                },
            ],
            attributes: vec![],
            return_name: "__ret__".to_owned(),
            return_type: tvoid.clone(),
            type_params: vec!["T".to_owned()],
            preconditions: vec![],
            postconditions: vec![],
            body: DUMMY_BODY,
        },
    );
    for name in ["+=", "-=", "*="] {
        functions.insert(
            name.to_owned(),
            FuncDef {
                name: name.to_owned(),
                args: vec![
                    Arg {
                        name: "lhs".to_owned(),
                        mutable: true,
                        arg_type: tint.clone(),
                    },
                    Arg {
                        name: "rhs".to_owned(),
                        mutable: false,
                        arg_type: tint.clone(),
                    },
                ],
                attributes: vec![],
                return_name: "__ret__".to_owned(),
                return_type: tvoid.clone(),
                type_params: vec![],
                preconditions: vec![],
                postconditions: vec![],
                body: DUMMY_BODY,
            },
        );
    }
    functions
}
