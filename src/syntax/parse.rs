use nom::{
    IResult, Parser,
    branch::alt,
    bytes::complete::{tag, take_until, take_while, take_while1},
    character::complete::{anychar, satisfy},
    combinator::{all_consuming, map, opt, recognize, value},
    multi::{many0, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, terminated},
};

use crate::syntax::ast::*;

enum Word {
    Identifier(String),
    Fn,
    Let,
    Mut,
    Requires,
    Ensures,
    Sees,
    False,
    True,
}

#[derive(PartialEq, Eq, Copy, Clone)]
enum Symbol {
    Semicolon,
    Comma,
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
    OpenSquare,
    CloseSquare,

    Colon,
    Assign,
    Arrow,
    Plus,
    Minus,
    Star,
    Slash,
    EqualEqual,
    NotEqual,
    AddAssign,
    SubAssign,
    MulAssign,
    Lt,
    Le,
    Gt,
    Ge,
    Exclaim,
    LogicalAnd,
    LogicalOr,
    Hash,
    Percent,
}

fn pure_whitespace1(input: &str) -> IResult<&str, &str> {
    take_while1(|c: char| c.is_whitespace())(input)
}

fn comment(input: &str) -> IResult<&str, &str> {
    preceded(tag("//"), take_while(|c| c != '\n')).parse(input)
}

fn multiline_comment(input: &str) -> IResult<&str, &str> {
    preceded(tag("/*"), take_until("*/")).parse(input)
}

fn whitespace_section(input: &str) -> IResult<&str, &str> {
    alt((pure_whitespace1, comment, multiline_comment)).parse(input)
}

fn whitespace0(input: &str) -> IResult<&str, ()> {
    value((), many0(whitespace_section)).parse(input)
}

fn alpha_underscore(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn alphanum_underscore(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn word(input: &str) -> IResult<&str, Word> {
    let (input, ident) = preceded(
        whitespace0,
        recognize(preceded(
            satisfy(alpha_underscore),
            take_while(alphanum_underscore),
        )),
    )
    .parse(input)?;
    let word = match ident {
        "fn" => Word::Fn,
        "let" => Word::Let,
        "mut" => Word::Mut,
        "requires" => Word::Requires,
        "ensures" => Word::Ensures,
        "sees" => Word::Sees,
        "false" => Word::False,
        "true" => Word::True,
        _ => Word::Identifier(ident.to_string()),
    };
    Ok((input, word))
}

fn integer(input: &str) -> IResult<&str, Literal> {
    let (input, int_str) = preceded(
        whitespace0,
        recognize(many0(satisfy(|c| c.is_ascii_digit()))),
    )
    .parse(input)?;
    let int_value: Result<i64, _> = int_str.parse();
    match int_value {
        Ok(v) => Ok((input, Literal::I64(v))),
        Err(_) => {
            let uint_value: Result<u64, _> = int_str.parse();
            match uint_value {
                Ok(uv) => Ok((input, Literal::U64(uv))),
                Err(_) => Err(nom::Err::Error(nom::error::Error::new(
                    input,
                    nom::error::ErrorKind::Digit,
                ))),
            }
        }
    }
}

fn integer_u64(input: &str) -> IResult<&str, u64> {
    let (input, literal) = integer(input)?;
    match literal {
        Literal::U64(v) => Ok((input, v)),
        Literal::I64(v) if v >= 0 => Ok((input, v as u64)),
        _ => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Digit,
        ))),
    }
}

fn normal_string_char(c: char) -> bool {
    c != '"' && c != '\\'
}

fn normal_string_contents1(input: &str) -> IResult<&str, String> {
    map(take_while1(normal_string_char), |s: &str| s.to_owned()).parse(input)
}

fn escaped_char(input: &str) -> IResult<&str, String> {
    map(
        preceded(
            tag("\\"),
            alt((
                value('\\', tag("\\")),
                value('\"', tag("\"")),
                value('\'', tag("\'")),
                value('\n', tag("n")),
                value('\r', tag("r")),
                value('\t', tag("t")),
            )),
        ),
        |c| c.to_string(),
    )
    .parse(input)
}

fn string_contents(input: &str) -> IResult<&str, String> {
    map(
        many0(alt((normal_string_contents1, escaped_char))),
        |pieces: Vec<String>| pieces.concat(),
    )
    .parse(input)
}

fn string(input: &str) -> IResult<&str, Literal> {
    map(
        preceded(
            whitespace0,
            delimited(tag("\""), string_contents, tag("\"")),
        ),
        Literal::Str,
    )
    .parse(input)
}

fn single_char_sym(input: &str) -> IResult<&str, Symbol> {
    let (input, c) = anychar(input)?;
    match c {
        ';' => Ok((input, Symbol::Semicolon)),
        ',' => Ok((input, Symbol::Comma)),
        '(' => Ok((input, Symbol::OpenParen)),
        ')' => Ok((input, Symbol::CloseParen)),
        '{' => Ok((input, Symbol::OpenBrace)),
        '}' => Ok((input, Symbol::CloseBrace)),
        '[' => Ok((input, Symbol::OpenSquare)),
        ']' => Ok((input, Symbol::CloseSquare)),
        _ => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Char,
        ))),
    }
}

fn is_multi_char_sym(ch: char) -> bool {
    matches!(
        ch,
        ':' | '=' | '+' | '-' | '*' | '<' | '>' | '!' | '&' | '|' | '#' | '%' | '/'
    )
}

fn multi_char_sym(input: &str) -> IResult<&str, Symbol> {
    let (input, string) = take_while1(is_multi_char_sym)(input)?;
    match string {
        ":" => Ok((input, Symbol::Colon)),
        "=" => Ok((input, Symbol::Assign)),
        "->" => Ok((input, Symbol::Arrow)),
        "+" => Ok((input, Symbol::Plus)),
        "-" => Ok((input, Symbol::Minus)),
        "*" => Ok((input, Symbol::Star)),
        "!=" => Ok((input, Symbol::NotEqual)),
        "==" => Ok((input, Symbol::EqualEqual)),
        "+=" => Ok((input, Symbol::AddAssign)),
        "-=" => Ok((input, Symbol::SubAssign)),
        "*=" => Ok((input, Symbol::MulAssign)),
        "<" => Ok((input, Symbol::Lt)),
        "<=" => Ok((input, Symbol::Le)),
        ">" => Ok((input, Symbol::Gt)),
        ">=" => Ok((input, Symbol::Ge)),
        "!" => Ok((input, Symbol::Exclaim)),
        "&&" => Ok((input, Symbol::LogicalAnd)),
        "||" => Ok((input, Symbol::LogicalOr)),
        "#" => Ok((input, Symbol::Hash)),
        "%" => Ok((input, Symbol::Percent)),
        "/" => Ok((input, Symbol::Slash)),
        _ => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Char,
        ))),
    }
}

fn any_symbol(input: &str) -> IResult<&str, Symbol> {
    alt((single_char_sym, multi_char_sym)).parse(input)
}

fn symbol(expected: Symbol) -> impl Fn(&str) -> IResult<&str, Symbol> {
    move |input: &str| {
        let (input, sym) = preceded(whitespace0, any_symbol).parse(input)?;
        if sym == expected {
            Ok((input, sym))
        } else {
            Err(nom::Err::Error(nom::error::Error::new(
                input,
                nom::error::ErrorKind::Tag,
            )))
        }
    }
}

fn boolean(input: &str) -> IResult<&str, Literal> {
    alt((
        value(Literal::Bool(true), keyword(Word::True)),
        value(Literal::Bool(false), keyword(Word::False)),
    ))
    .parse(input)
}

fn literal(input: &str) -> IResult<&str, Expr> {
    map(alt((integer, string, boolean)), Expr::Literal).parse(input)
}

// fn variable(input: &str) -> IResult<&str, Expr> {
//     let (input, word) = word(input)?;
//     match word {
//         Word::Identifier(name) => Ok((input, Expr::Variable(name))),
//         _ => Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Tag))),
//     }
// }

fn identifier(input: &str) -> IResult<&str, String> {
    let (input, word) = word(input)?;
    match word {
        Word::Identifier(name) => Ok((input, name)),
        _ => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Tag,
        ))),
    }
}

fn specific_identifier(expected: &str) -> impl Fn(&str) -> IResult<&str, String> {
    move |input: &str| {
        let (input, word) = word(input)?;
        match word {
            Word::Identifier(name) if name == expected => Ok((input, name)),
            _ => Err(nom::Err::Error(nom::error::Error::new(
                input,
                nom::error::ErrorKind::Tag,
            ))),
        }
    }
}

fn variable_or_call(input: &str) -> IResult<&str, Expr> {
    let (input, name) = identifier(input)?;
    let (input, call_opt) = opt(call_suffix(name.clone())).parse(input)?;
    match call_opt {
        Some(call_expr) => Ok((input, call_expr)),
        None => Ok((input, Expr::Variable { name, typ: None })),
    }
}

fn typ_arg(input: &str) -> IResult<&str, TypeArg> {
    let (input, type_arg) = alt((
        map(integer, |lit| match lit {
            Literal::I64(v) => TypeArg::Bound(Bound::I64(v)),
            Literal::U64(v) => TypeArg::Bound(Bound::U64(v)),
            _ => unreachable!(),
        }),
        map(typ, TypeArg::Type),
    ))
    .parse(input)?;
    Ok((input, type_arg))
}

fn typ(input: &str) -> IResult<&str, Type> {
    alt((
        delimited(
            symbol(Symbol::OpenParen),
            typ_parenthesized,
            symbol(Symbol::CloseParen),
        ),
        delimited(
            symbol(Symbol::OpenSquare),
            typ_squared,
            symbol(Symbol::CloseSquare),
        ),
        named_typ,
    ))
    .parse(input)
}

fn typ_parenthesized(input: &str) -> IResult<&str, Type> {
    // separated_list1 because () is not a valid type (it's called `void` instead)
    // TODO: should it be called void or ()?
    let (input, type_args) = separated_list1(symbol(Symbol::Comma), typ).parse(input)?;
    assert!(!type_args.is_empty());
    if type_args.len() == 1 {
        // (T,) or (T;n)
        // Note that (T,) resolves to the same thing as (T;1)
        // (T;0) resolves to void
        let (input, length) = alt((
            value(1u64, symbol(Symbol::Comma)),
            preceded(symbol(Symbol::Semicolon), integer_u64),
        ))
        .parse(input)?;
        let type_arg = type_args.into_iter().next().unwrap();
        if length == 0 {
            Ok((
                input,
                Type {
                    name: "void".to_owned(),
                    type_args: vec![],
                },
            ))
        } else {
            let type_args = vec![type_arg; length as usize]; // TODO: let's hope it's not stupidly long
            Ok((
                input,
                Type {
                    name: "Tuple".to_owned(),
                    type_args: type_args.into_iter().map(TypeArg::Type).collect(),
                },
            ))
        }
    } else {
        // (T1, T2...) optionally with a comma at the end
        let (input, _) = opt(symbol(Symbol::Comma)).parse(input)?;
        Ok((
            input,
            Type {
                name: "Tuple".to_owned(),
                type_args: type_args.into_iter().map(TypeArg::Type).collect(),
            },
        ))
    }
}

fn typ_squared(input: &str) -> IResult<&str, Type> {
    // This time I'm sure. [] is not a valid type name.
    let (input, type_arg) = typ(input)?;
    let (input, length) = opt(preceded(symbol(Symbol::Semicolon), integer_u64)).parse(input)?;
    if let Some(length) = length {
        Ok((
            input,
            Type {
                name: "Array".to_owned(),
                type_args: vec![TypeArg::Type(type_arg), TypeArg::Bound(Bound::U64(length))],
            },
        ))
    } else {
        Ok((
            input,
            Type {
                name: "Vec".to_owned(),
                type_args: vec![TypeArg::Type(type_arg)],
            },
        ))
    }
}

fn named_typ(input: &str) -> IResult<&str, Type> {
    let (input, name) = identifier(input)?;
    let (input, type_args) = opt(delimited(
        symbol(Symbol::Lt),
        separated_list1(symbol(Symbol::Comma), typ_arg),
        symbol(Symbol::Gt),
    ))
    .parse(input)?;
    let type_args = type_args.unwrap_or_else(Vec::new);
    Ok((input, Type { name, type_args }))
}

fn call_arg_mut(input: &str) -> IResult<&str, CallArg> {
    let (input, name) = preceded(keyword(Word::Mut), identifier).parse(input)?;
    Ok((input, CallArg::MutVar { name, typ: None }))
}

fn call_arg_expr(input: &str) -> IResult<&str, CallArg> {
    let (input, expr) = expr_comma(input)?;
    Ok((input, CallArg::Expr(expr)))
}

fn call_suffix(name: String) -> impl Fn(&str) -> IResult<&str, Expr> {
    move |input: &str| {
        let (input, args) = delimited(
            symbol(Symbol::OpenParen),
            separated_list0(symbol(Symbol::Comma), alt((call_arg_mut, call_arg_expr))),
            symbol(Symbol::CloseParen),
        )
        .parse(input)?;
        Ok((
            input,
            Expr::FunctionCall {
                name: name.clone(),
                args,
                type_instantiations: vec![],
                return_type: None,
            },
        ))
    }
}
fn semicolon_suffix(left: Expr) -> impl Fn(&str) -> IResult<&str, Expr> {
    move |input: &str| {
        let (input, _) = symbol(Symbol::Semicolon)(input)?;
        let (input, right) = opt(expr).parse(input)?;
        let right = right.unwrap_or(Expr::Literal(Literal::Unit));
        Ok((
            input,
            Expr::Semicolon(Box::new(Stmt::Expr(left.clone())), Box::new(right)),
        ))
    }
}

fn expr_tight(input: &str) -> IResult<&str, Expr> {
    alt((
        variable_or_call,
        literal,
        delimited(
            symbol(Symbol::OpenSquare),
            expr_array_contents,
            symbol(Symbol::CloseSquare),
        ),
        delimited(
            symbol(Symbol::OpenParen),
            expr_parenthesized,
            symbol(Symbol::CloseParen),
        ),
        delimited(symbol(Symbol::OpenBrace), expr, symbol(Symbol::CloseBrace)),
    ))
    .parse(input)
}

fn expr_suffixed(input: &str) -> IResult<&str, Expr> {
    let (input, base) = expr_tight(input)?;
    let (input, index) = opt(delimited(
        symbol(Symbol::OpenSquare),
        expr_comma,
        symbol(Symbol::CloseSquare),
    ))
    .parse(input)?;
    if let Some(index) = index {
        Ok((
            input,
            Expr::SeqAt {
                seq: Box::new(base),
                index: Box::new(index),
            },
        ))
    } else {
        Ok((input, base))
    }
}

fn expr_prefixed(input: &str) -> IResult<&str, Expr> {
    alt((
        preceded(
            symbol(Symbol::Minus),
            map(expr_prefixed, |e| Expr::FunctionCall {
                name: "neg".to_owned(),
                args: vec![CallArg::Expr(e)],
                type_instantiations: vec![],
                return_type: None,
            }),
        ),
        expr_tight,
    ))
    .parse(input)
}

fn plusminus(input: &str) -> IResult<&str, Symbol> {
    alt((symbol(Symbol::Plus), symbol(Symbol::Minus))).parse(input)
}

fn timesdividemod(input: &str) -> IResult<&str, Symbol> {
    alt((
        symbol(Symbol::Star),
        symbol(Symbol::Slash),
        symbol(Symbol::Percent),
    ))
    .parse(input)
}

fn cmpop(input: &str) -> IResult<&str, Symbol> {
    alt((
        symbol(Symbol::EqualEqual),
        symbol(Symbol::NotEqual),
        symbol(Symbol::Lt),
        symbol(Symbol::Le),
        symbol(Symbol::Gt),
        symbol(Symbol::Ge),
    ))
    .parse(input)
}

impl Symbol {
    fn to_function_name(&self) -> String {
        match self {
            Symbol::Plus => "+".to_owned(),
            Symbol::Minus => "-".to_owned(),
            Symbol::Star => "*".to_owned(),
            Symbol::Slash => "/".to_owned(),
            Symbol::Percent => "%".to_owned(),
            Symbol::EqualEqual => "==".to_owned(),
            Symbol::NotEqual => "!=".to_owned(),
            Symbol::Lt => "<".to_owned(),
            Symbol::Le => "<=".to_owned(),
            Symbol::Gt => ">".to_owned(),
            Symbol::Ge => ">=".to_owned(),
            _ => unreachable!(),
        }
    }
}

fn expr_times_divide_mod(input: &str) -> IResult<&str, Expr> {
    let (input, mut exprs) = expr_prefixed(input)?;
    let mut inp = input;
    loop {
        let (input, op) = opt(pair(timesdividemod, expr_prefixed)).parse(inp)?;
        inp = input;

        if let Some((sym, rhs)) = op {
            let new_expr = Expr::FunctionCall {
                name: sym.to_function_name(),
                args: vec![CallArg::Expr(exprs.clone()), CallArg::Expr(rhs)],
                type_instantiations: vec![],
                return_type: None,
            };
            exprs = new_expr;
        } else {
            break;
        }
    }
    Ok((inp, exprs))
}

fn expr_plusminus(input: &str) -> IResult<&str, Expr> {
    let (input, mut exprs) = expr_times_divide_mod(input)?;
    let mut inp = input;
    loop {
        let (input, op) = opt(pair(plusminus, expr_times_divide_mod)).parse(inp)?;
        inp = input;

        if let Some((sym, rhs)) = op {
            let new_expr = Expr::FunctionCall {
                name: sym.to_function_name(),
                args: vec![CallArg::Expr(exprs.clone()), CallArg::Expr(rhs)],
                type_instantiations: vec![],
                return_type: None,
            };
            exprs = new_expr;
        } else {
            break;
        }
    }
    Ok((inp, exprs))
}

fn expr_cmp(input: &str) -> IResult<&str, Expr> {
    let (input, expr) = expr_plusminus(input)?;
    let (input, cmp_opt) = opt(pair(cmpop, expr_plusminus)).parse(input)?;
    match cmp_opt {
        Some((sym, rhs)) => {
            let new_expr = Expr::FunctionCall {
                name: sym.to_function_name(),
                args: vec![CallArg::Expr(expr), CallArg::Expr(rhs)],
                type_instantiations: vec![],
                return_type: None,
            };
            Ok((input, new_expr))
        }
        None => Ok((input, expr)),
    }
}

fn expr_conjunction(input: &str) -> IResult<&str, Expr> {
    let (input, expr) = expr_cmp(input)?;
    let (input, and_opt) =
        opt(preceded(symbol(Symbol::LogicalAnd), expr_conjunction)).parse(input)?;
    match and_opt {
        Some(rhs) => {
            let new_expr = Expr::FunctionCall {
                name: "&&".to_owned(),
                args: vec![CallArg::Expr(expr), CallArg::Expr(rhs)],
                type_instantiations: vec![],
                return_type: None,
            };
            Ok((input, new_expr))
        }
        None => Ok((input, expr)),
    }
}

fn expr_disjunction(input: &str) -> IResult<&str, Expr> {
    let (input, expr) = expr_conjunction(input)?;
    let (input, or_opt) =
        opt(preceded(symbol(Symbol::LogicalOr), expr_disjunction)).parse(input)?;
    match or_opt {
        Some(rhs) => {
            let new_expr = Expr::FunctionCall {
                name: "||".to_owned(),
                args: vec![CallArg::Expr(expr), CallArg::Expr(rhs)],
                type_instantiations: vec![],
                return_type: None,
            };
            Ok((input, new_expr))
        }
        None => Ok((input, expr)),
    }
}

fn expr_comma(input: &str) -> IResult<&str, Expr> {
    expr_disjunction(input)
}

fn expr_semicolon(input: &str) -> IResult<&str, Expr> {
    let (input, first) = expr_comma(input)?;
    let (input, second) = opt(semicolon_suffix(first.clone())).parse(input)?;
    match second {
        Some(expr) => Ok((input, expr)),
        None => Ok((input, first)),
    }
}

fn expr_parenthesized(input: &str) -> IResult<&str, Expr> {
    let (input, elems) = separated_list0(symbol(Symbol::Comma), expr_comma).parse(input)?;
    if elems.is_empty() {
        // ()
        Ok((input, Expr::Literal(Literal::Unit)))
    } else {
        let (input, comma) = opt(symbol(Symbol::Comma)).parse(input)?;
        if comma.is_some() || elems.len() > 1 {
            // (x,) or (x,y...)
            Ok((input, Expr::RoundSequence { elems }))
        } else {
            // (x)
            Ok((input, elems.into_iter().next().unwrap()))
        }
    }
}

fn expr_array_contents(input: &str) -> IResult<&str, Expr> {
    let (input, elems) = separated_list0(symbol(Symbol::Comma), expr_comma).parse(input)?;
    let input = if !elems.is_empty() {
        opt(symbol(Symbol::Comma)).parse(input)?.0
    } else {
        input
    };
    Ok((
        input,
        Expr::SquareSequence {
            elems,
            elem_type: None,
        },
    ))
}

// fn expr_vec(input: &str) -> IResult<&str, Expr> {
//     // vec isn't a keyword. It only has special meaning when followed by '!'
//     map(
//         preceded(pair(specific_identifier("vec"), symbol(Symbol::Exclaim)), expr_array),
//         |array_expr| Expr::Sequence {
//             seq_type: SeqType::Vec,
//             elements: match array_expr {
//                 Expr::Sequence { elements, .. } => elements,
//                 _ => unreachable!(),
//             },
//         },
//     ).parse(input)
// }

fn keyword(expected: Word) -> impl Fn(&str) -> IResult<&str, Word> {
    move |input: &str| {
        let (input, word) = preceded(whitespace0, word).parse(input)?;
        if std::mem::discriminant(&word) == std::mem::discriminant(&expected) {
            Ok((input, word))
        } else {
            Err(nom::Err::Error(nom::error::Error::new(
                input,
                nom::error::ErrorKind::Tag,
            )))
        }
    }
}

fn stmt_let(input: &str) -> IResult<&str, Stmt> {
    let (input, _) = keyword(Word::Let)(input)?;
    let (input, mutable) = opt(keyword(Word::Mut)).parse(input)?;
    let (input, name) = identifier(input)?;
    let (input, t) = opt(preceded(symbol(Symbol::Colon), typ)).parse(input)?;
    if mutable.is_some() && t.is_none() {
        return Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Tag,
        )));
    }
    let (input, _) = symbol(Symbol::Assign)(input)?;
    let (input, value) = expr_comma(input)?;
    Ok((
        input,
        Stmt::Let {
            name,
            mutable: mutable.is_some(),
            typ: t,
            value,
        },
    ))
}

fn assignop(input: &str) -> IResult<&str, AssignOp> {
    alt((
        value(AssignOp::Assign, symbol(Symbol::Assign)),
        value(AssignOp::AddAssign, symbol(Symbol::AddAssign)),
        value(AssignOp::SubAssign, symbol(Symbol::SubAssign)),
        value(AssignOp::MulAssign, symbol(Symbol::MulAssign)),
    ))
    .parse(input)
}

fn stmt_assign(input: &str) -> IResult<&str, Stmt> {
    let (input, name) = identifier(input)?;
    let (input, op) = assignop(input)?;
    let (input, value) = expr_comma(input)?;
    Ok((input, Stmt::Assign { name, op, value }))
}

fn stmt(input: &str) -> IResult<&str, Stmt> {
    alt((stmt_let, stmt_assign)).parse(input)
}

fn stmt_semicolon(input: &str) -> IResult<&str, Expr> {
    let (input, first) = stmt(input)?;
    let (input, _) = symbol(Symbol::Semicolon)(input)?;
    let (input, second) = expr(input)?;
    Ok((input, Expr::Semicolon(Box::new(first), Box::new(second))))
}

fn expr(input: &str) -> IResult<&str, Expr> {
    alt((stmt_semicolon, expr_semicolon)).parse(input)
}

fn arg(input: &str) -> IResult<&str, Arg> {
    let (input, name) = identifier(input)?;
    let (input, _) = symbol(Symbol::Colon)(input)?;
    let (input, arg_type) = typ(input)?;
    Ok((
        input,
        Arg {
            name,
            mutable: false,
            arg_type,
        },
    ))
}

fn named_ret(input: &str) -> IResult<&str, (Option<String>, Type)> {
    let (input, _) = symbol(Symbol::OpenParen)(input)?;
    let (input, return_name) = identifier(input)?;
    let (input, _) = symbol(Symbol::Colon)(input)?;
    let (input, return_type) = typ(input)?;
    let (input, _) = symbol(Symbol::CloseParen)(input)?;
    Ok((input, (Some(return_name), return_type)))
}

fn unnamed_ret(input: &str) -> IResult<&str, (Option<String>, Type)> {
    let (input, return_type) = typ(input)?;
    Ok((input, (None, return_type)))
}

fn ret(input: &str) -> IResult<&str, (Option<String>, Type)> {
    alt((named_ret, unnamed_ret)).parse(input)
}

fn expr_or_empty(input: &str) -> IResult<&str, Expr> {
    let (input, expr_opt) = opt(expr).parse(input)?;
    match expr_opt {
        Some(e) => Ok((input, e)),
        None => Ok((input, Expr::Literal(Literal::Unit))),
    }
}

fn attribute_check_decisions(input: &str) -> IResult<&str, FuncAttribute> {
    let (input, _) = specific_identifier("check_decisions")(input)?;
    let (input, decisions) = delimited(
        symbol(Symbol::OpenParen),
        separated_list1(symbol(Symbol::Comma), identifier),
        symbol(Symbol::CloseParen),
    )
    .parse(input)?;
    Ok((input, FuncAttribute::CheckDecisions(decisions)))
}

fn attribute(input: &str) -> IResult<&str, FuncAttribute> {
    let (input, _) = symbol(Symbol::Hash)(input)?;
    let (input, attr) = delimited(
        symbol(Symbol::OpenSquare),
        alt((attribute_check_decisions,)),
        symbol(Symbol::CloseSquare),
    )
    .parse(input)?;
    Ok((input, attr))
}

fn funcdef(input: &str) -> IResult<&str, FuncDef> {
    let (input, mut attributes) = many0(attribute).parse(input)?;
    let (input, _) = keyword(Word::Fn)(input)?;
    let (input, name) = identifier(input)?;
    let (input, args) = delimited(
        symbol(Symbol::OpenParen),
        separated_list0(symbol(Symbol::Comma), arg),
        symbol(Symbol::CloseParen),
    )
    .parse(input)?;
    let (input, return_stuff) = opt(preceded(symbol(Symbol::Arrow), ret)).parse(input)?;
    let (input, preconditions) = opt(preceded(
        keyword(Word::Requires),
        separated_list1(symbol(Symbol::Comma), expr_comma),
    ))
    .parse(input)?;
    let (input, postconditions) = opt(preceded(
        keyword(Word::Ensures),
        separated_list1(symbol(Symbol::Comma), expr_comma),
    ))
    .parse(input)?;
    let (input, sees) = opt(preceded(
        keyword(Word::Sees),
        separated_list1(symbol(Symbol::Comma), identifier),
    ))
    .parse(input)?;

    let (input, body) = delimited(
        symbol(Symbol::OpenBrace),
        expr_or_empty,
        symbol(Symbol::CloseBrace),
    )
    .parse(input)?;

    let (return_name, return_type) = match return_stuff {
        Some((rn, rt)) => (rn, rt),
        None => (
            None,
            Type {
                name: "void".to_string(),
                type_args: Vec::new(),
            },
        ),
    };

    if let Some(sees) = sees {
        for see in sees.into_iter() {
            attributes.push(FuncAttribute::Sees(see));
        }
    }

    Ok((
        input,
        FuncDef {
            attributes,
            name,
            type_params: vec![],
            args,
            return_name: return_name.unwrap_or_else(|| "__ret__".to_owned()),
            return_type,
            preconditions: preconditions.unwrap_or_else(Vec::new),
            postconditions: postconditions.unwrap_or_else(Vec::new),
            body,
        },
    ))
}

fn source_file(input: &str) -> IResult<&str, SourceFile> {
    let (input, functions) = all_consuming(terminated(many0(funcdef), whitespace0)).parse(input)?;
    Ok((input, SourceFile { functions }))
}

#[derive(Debug)]
pub struct ErrorLocation {
    pub line: usize,
    pub column: usize,
}

impl std::fmt::Display for ErrorLocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Parse error Line {}, Column {}", self.line, self.column)
    }
}

impl std::error::Error for ErrorLocation {}

pub fn parse_source_file(input: &str) -> Result<SourceFile, ErrorLocation> {
    match source_file(input) {
        Ok((_, src_file)) => Ok(src_file),
        Err(e) => {
            let offset = match e {
                nom::Err::Error(err) | nom::Err::Failure(err) => input.len() - err.input.len(),
                nom::Err::Incomplete(_) => input.len(),
            };
            let mut line = 1;
            let mut column = 1;
            for (i, c) in input.chars().enumerate() {
                if i == offset {
                    break;
                }
                if c == '\n' {
                    line += 1;
                    column = 1;
                } else {
                    column += 1;
                }
            }
            Err(ErrorLocation { line, column })
        }
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn test_var() {
        let expr = "my_variable";
        let result = super::variable_or_call(expr);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    #[test]
    fn test_empty() {
        let expr = "";
        let result = super::expr(expr);
        assert!(!result.is_ok());
    }

    #[test]
    fn test_empty_call_suffix() {
        let suffix = "()";
        let result = super::call_suffix("my_function".to_string())(suffix);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    #[test]
    fn test_empty_call() {
        let expr = "foo()";
        let result = super::expr(expr);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    #[test]
    fn test_hello() {
        let expr = "println(\"Hello, world!\")";
        let result = super::expr(expr);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    #[test]
    fn test_let() {
        let stmt = "let x = 5";
        let result = super::stmt(stmt);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    #[test]
    fn test_let_mut() {
        let stmt = "let mut x:u64 = 5";
        let result = super::stmt(stmt);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    #[test]
    fn test_let_semicolon() {
        let expr = "let x = 5; x";
        let result = super::expr(expr);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    #[test]
    fn test_plusassign() {
        let stmt = "x += 10";
        let result = super::stmt(stmt);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    #[test]
    fn test_function_with_let_semicolon() {
        let funcdef = "fn main() -> void { let x = 2; x }";
        let result = super::funcdef(funcdef);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    #[test]
    fn test_function_implied_void_return() {
        let funcdef = "fn main() { println(\"Hello\") }";
        let result = super::funcdef(funcdef);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    #[test]
    fn test_function_type_args() {
        let input = "Vec<u64>";
        let result = super::typ(input);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    // #[test]
    // fn test_vec() {
    //     let expr = "vec![1, 2, 3]";
    //     let result = super::expr(expr);
    //     assert!(result.is_ok());
    //     assert_eq!(result.unwrap().0, "");
    // }
}
