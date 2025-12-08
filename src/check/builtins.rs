use std::{collections::HashMap, slice::from_ref};

use crate::check::{
    overloads::{Optimization, TFunc, TOverloadedFunc},
    parameterized::{ParameterizedType, ParameterizedTypeArg},
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

pub fn builtins() -> HashMap<String, TOverloadedFunc> {
    let mut functions = HashMap::new();
    let z32 = ParameterizedType::basic("z32");
    let z64 = ParameterizedType::basic("z64");
    let tint = ParameterizedType::basic("int");
    let tbool = ParameterizedType::basic("bool");
    let tstr = ParameterizedType::basic("str");
    let tvoid = ParameterizedType::basic("void");
    let tparam = ParameterizedType::Param("T".to_owned());
    let uparam = ParameterizedType::Param("U".to_owned());
    let seqt = ParameterizedType::Named(
        "Seq".to_owned(),
        vec![ParameterizedTypeArg::Type(tparam.clone())],
    );
    let sequ = ParameterizedType::Named(
        "Seq".to_owned(),
        vec![ParameterizedTypeArg::Type(uparam.clone())],
    );

    insert_multiple(
        &mut functions,
        &["==", "!="],
        TOverloadedFunc::psimple(&[tparam.clone(), tparam.clone()], &tbool),
    );

    insert_multiple(
        &mut functions,
        &["<", "<=", ">", ">="],
        TOverloadedFunc::psimple(&[tint.clone(), tint.clone()], &tbool),
    );

    for &(symbol, name) in &[("+", "add"), ("-", "sub"), ("*", "mul")] {
        functions.insert(
            symbol.to_owned(),
            TOverloadedFunc {
                headline: TFunc {
                    arg_types: vec![tint.clone(), tint.clone()],
                    return_type: tint.clone(),
                },
                optimizations: vec![
                    Optimization {
                        debug_name: format!("z32_{}", name),
                        func: TFunc {
                            arg_types: vec![z32.clone(), z32.clone()],
                            return_type: z32.clone(),
                        },
                    },
                    Optimization {
                        debug_name: format!("z64_{}", name),
                        func: TFunc {
                            arg_types: vec![z64.clone(), z64.clone()],
                            return_type: z64.clone(),
                        },
                    },
                ],
            },
        );
    }

    insert_multiple(
        &mut functions,
        &["&&", "||"],
        TOverloadedFunc::psimple(&[tbool.clone(), tbool.clone()], &tbool),
    );

    functions.insert(
        "println".to_owned(),
        TOverloadedFunc::psimple(from_ref(&tstr), &tvoid),
    );
    functions.insert(
        "assert".to_owned(),
        TOverloadedFunc::psimple(from_ref(&tbool), &tvoid),
    );
    functions.insert(
        "seq_len".to_owned(),
        TOverloadedFunc::psimple(from_ref(&seqt), &tint),
    );
    functions.insert(
        "seq_map".to_owned(),
        TOverloadedFunc::psimple(
            &[
                seqt.clone(),
                ParameterizedType::lambda_type(from_ref(&tparam), &uparam),
            ],
            &sequ,
        ),
    );
    functions.insert(
        "seq_foldl".to_owned(),
        TOverloadedFunc::psimple(
            &[
                seqt.clone(),
                ParameterizedType::lambda_type(&[uparam.clone(), tparam.clone()], &uparam),
                uparam.clone(),
            ],
            &uparam,
        ),
    );
    functions
}
