use std::{collections::HashMap, slice::from_ref};

use crate::{check::overloads::{TFunc, TOptimizedFunc, TOverloadedFunc}, syntax::ast::Type};

pub fn builtins() -> HashMap<String, TOverloadedFunc> {
    let mut functions = HashMap::new();
    let tint = Type::basic("int");
    let tbool = Type::basic("bool");
    let int_rel = TOverloadedFunc::simple(&[tint.clone(), tint.clone()], &tbool);
    let int_binop = TOverloadedFunc::simple(&[tint.clone(), tint.clone()], &tint);
    let print_sig = TOverloadedFunc::simple(&[Type::basic("str")], &Type::basic("void"));
    let assert_sig = TOverloadedFunc::simple(from_ref(&tbool), &Type::basic("void"));
    let bool_op = TOverloadedFunc::simple(&[tbool.clone(), tbool.clone()], &tbool);
    let eq_sig = TOverloadedFunc(
        vec![
            TOptimizedFunc {
                headline: TFunc {
                    arg_types: vec![tint.clone(), tint.clone()],
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
    functions
}