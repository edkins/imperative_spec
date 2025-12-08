use std::{collections::HashMap, slice::from_ref};

use crate::{
    check::{
        overloads::{Optimization, TFunc, TOverloadedFunc},
        ztype_ast::TExpr,
    },
    syntax::ast::{Arg, Type, TypeArg},
};

fn insert_multiple(
    map: &mut HashMap<String, TOverloadedFunc>,
    names: &[&str],
    func: TOverloadedFunc,
) {
    for &name in names {
        if map.contains_key(name) {
            panic!("Builtin function {} defined multiple times", name);
        } else {
            map.insert(name.to_owned(), func.clone());
        }
    }
}

fn args2(t0: &Type, t1: &Type) -> Vec<Arg> {
    vec![
        Arg {
            name: "arg0".to_owned(),
            arg_type: t0.clone(),
        },
        Arg {
            name: "arg1".to_owned(),
            arg_type: t1.clone(),
        },
    ]
}

fn args1(t0: &Type) -> Vec<Arg> {
    vec![Arg {
        name: "arg0".to_owned(),
        arg_type: t0.clone(),
    }]
}

pub fn builtins() -> HashMap<String, TOverloadedFunc> {
    let mut functions = HashMap::new();
    let tu32 = Type::basic("u32");
    let tu64 = Type::basic("u64");
    let ti32 = Type::basic("i32");
    let ti64 = Type::basic("i64");
    let z32 = Type::basic("z32");
    let z64 = Type::basic("z64");
    let tint = Type::basic("int");
    let tbool = Type::basic("bool");
    let tstr = Type::basic("str");
    let tvoid = Type::basic("void");
    let tparam = Type::basic("T");
    let uparam = Type::basic("U");
    let seqt = Type {
        name: "Seq".to_owned(),
        type_args: vec![TypeArg::Type(tparam.clone())],
    };
    let sequ = Type {
        name: "Seq".to_owned(),
        type_args: vec![TypeArg::Type(uparam.clone())],
    };

    insert_multiple(
        &mut functions,
        &["==", "!="],
        TOverloadedFunc::psimple(&[tparam.clone(), tparam.clone()], &tbool, &["T"]),
    );

    insert_multiple(
        &mut functions,
        &["<", "<=", ">", ">="],
        TOverloadedFunc::simple(&[tint.clone(), tint.clone()], &tbool),
    );

    functions.insert(
        "neg".to_owned(),
        TOverloadedFunc {
            headline: TFunc {
                args: args1(&tint),
                return_type: tint.clone(),
                type_param_list: vec![],
            },
            optimizations: vec![
                Optimization {
                    debug_name: "z32_neg".to_owned(),
                    arg_types: vec![z32.clone()],
                    return_type: z32.clone(),
                    preconditions: vec![],
                },
                Optimization {
                    debug_name: "z64_neg".to_owned(),
                    arg_types: vec![z64.clone()],
                    return_type: z64.clone(),
                    preconditions: vec![],
                },
            ],
            preconditions: vec![],
        },
    );

    for (symbol, name) in [("+", "add"), ("-", "sub"), ("*", "mul")] {
        functions.insert(
            symbol.to_owned(),
            TOverloadedFunc {
                headline: TFunc {
                    args: args2(&tint, &tint),
                    return_type: tint.clone(),
                    type_param_list: vec![],
                },
                optimizations: vec![
                    Optimization {
                        debug_name: format!("z32_{}", name),
                        arg_types: vec![z32.clone(), z32.clone()],
                        return_type: z32.clone(),
                        preconditions: vec![],
                    },
                    Optimization {
                        debug_name: format!("z64_{}", name),
                        arg_types: vec![z64.clone(), z64.clone()],
                        return_type: z64.clone(),
                        preconditions: vec![],
                    },
                ],
                preconditions: vec![],
            },
        );
    }

    for (symbol, name) in [("/", "div"), ("%", "mod")] {
        functions.insert(
            symbol.to_owned(),
            TOverloadedFunc {
                headline: TFunc {
                    args: args2(&tint, &tint),
                    return_type: tint.clone(),
                    type_param_list: vec![],
                },
                optimizations: vec![
                    Optimization {
                        debug_name: format!("u32_{}", name),
                        arg_types: vec![tu32.clone(), tu32.clone()],
                        return_type: tu32.clone(),
                        preconditions: vec![], // the "nonzero" precondition from the main function still applies
                    },
                    Optimization {
                        debug_name: format!("u64_{}", name),
                        arg_types: vec![tu64.clone(), tu64.clone()],
                        return_type: tu64.clone(),
                        preconditions: vec![],
                    },
                    Optimization {
                        debug_name: format!("i32_{}", name),
                        arg_types: vec![ti32.clone(), ti32.clone()],
                        return_type: ti32.clone(),
                        preconditions: vec![],
                    },
                    Optimization {
                        debug_name: format!("i64_{}", name),
                        arg_types: vec![ti64.clone(), ti64.clone()],
                        return_type: ti64.clone(),
                        preconditions: vec![],
                    },
                ],
                preconditions: vec![tint.var("arg1").ne(&TExpr::zero()).unwrap()],
            },
        );
    }

    insert_multiple(
        &mut functions,
        &["&&", "||"],
        TOverloadedFunc::simple(&[tbool.clone(), tbool.clone()], &tbool),
    );

    functions.insert(
        "println".to_owned(),
        TOverloadedFunc::simple(from_ref(&tstr), &tvoid),
    );
    functions.insert(
        "assert".to_owned(),
        TOverloadedFunc::simple(from_ref(&tbool), &tvoid),
    );
    functions.insert(
        "seq_len".to_owned(),
        TOverloadedFunc::psimple(from_ref(&seqt), &tint, &["T"]),
    );
    functions.insert(
        "seq_map".to_owned(),
        TOverloadedFunc::psimple(
            &[seqt.clone(), Type::lambda(from_ref(&tparam), &uparam)],
            &sequ,
            &["T", "U"],
        ),
    );
    functions.insert(
        "seq_foldl".to_owned(),
        TOverloadedFunc::psimple(
            &[
                seqt.clone(),
                Type::lambda(&[uparam.clone(), tparam.clone()], &uparam),
                uparam.clone(),
            ],
            &uparam,
            &["T", "U"],
        ),
    );
    functions
}
