use std::{collections::HashMap, slice::from_ref};

use crate::check::{overloads::{TFunc, TOptimizedFunc, TOverloadedFunc}, parameterized::{ParameterizedType, ParameterizedTypeArg}};

pub fn builtins() -> HashMap<String, TOverloadedFunc> {
    let mut functions = HashMap::new();
    let tint = ParameterizedType::basic("int");
    let tbool = ParameterizedType::basic("bool");
    let tstr = ParameterizedType::basic("str");
    let tvoid = ParameterizedType::basic("void");
    let tparam = ParameterizedType::Param("T".to_owned());
    let seqt = ParameterizedType::Named(
        "Seq".to_owned(),
        vec![ParameterizedTypeArg::Type(tparam.clone())],
    );
    let int_rel = TOverloadedFunc::psimple(&[tint.clone(), tint.clone()], &tbool);
    let int_binop = TOverloadedFunc::psimple(&[tint.clone(), tint.clone()], &tint);
    let print_sig = TOverloadedFunc::psimple(from_ref(&tstr), &tvoid);
    let assert_sig = TOverloadedFunc::psimple(from_ref(&tbool), &tvoid);
    let bool_op = TOverloadedFunc::psimple(&[tbool.clone(), tbool.clone()], &tbool);
    let eq_sig = TOverloadedFunc(
        vec![
            TOptimizedFunc {
                headline: TFunc {
                    arg_types: vec![tparam.clone(), tparam.clone()],
                    return_type: tbool.clone(),
                },
                optimizations: vec![],
            },
        ]
    );


    functions
        .insert("==".to_owned(), eq_sig.clone());
    functions
        .insert("!=".to_owned(), eq_sig.clone());
    functions.insert(
        "<".to_owned(),
        int_rel.clone(),
    );
    functions.insert(
        "<=".to_owned(),
        int_rel.clone(),
    );
    functions.insert(
        ">".to_owned(),
        int_rel.clone(),
    );
    functions.insert(
        ">=".to_owned(),
        int_rel.clone(),
    );
    functions.insert(
        "+".to_owned(),
        int_binop.clone(),
    );
    functions.insert(
        "-".to_owned(),
        int_binop.clone(),
    );
    functions.insert(
        "&&".to_owned(),
        bool_op.clone(),
    );
    functions.insert(
        "||".to_owned(),
        bool_op.clone(),
    );
    functions.insert(
        "println".to_owned(),
        print_sig.clone(),
    );
    functions.insert(
        "assert".to_owned(),
        assert_sig.clone(),
    );
    functions.insert(
        "seq_len".to_owned(),
        TOverloadedFunc::psimple(from_ref(&seqt), &tint),
    );
    functions
}