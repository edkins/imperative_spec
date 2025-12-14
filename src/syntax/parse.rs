use nom::{
    IResult, Parser,
    branch::alt,
    bytes::complete::{tag, take_until, take_while, take_while1},
    character::complete::{anychar, satisfy},
    combinator::{all_consuming, map, opt, recognize, value},
    multi::{many0, separated_list0, separated_list1},
    sequence::{delimited, pair, preceded, terminated},
};

use crate::syntax::{ast::*, mk};

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
    Dot,

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
        ':' | '=' | '+' | '-' | '*' | '<' | '>' | '!' | '&' | '|' | '#' | '%' | '/' | '.'
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
        "." => Ok((input, Symbol::Dot)),
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
    let (input, _) = whitespace0(input)?;
    let (input1, lit) = alt((integer, string, boolean)).parse(input)?;
    Ok((input1, lit.as_expr().between(input, input1)))
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
    let (input0, _) = whitespace0(input)?;
    let (input1, name) = identifier(input0)?;
    let (input2, call_opt) = opt(call_suffix(name.clone())).parse(input1)?;
    match call_opt {
        Some(call_expr) => Ok((input2, call_expr.between(input0, input1))),
        None => Ok((input2, mk::untyped_var(name).between(input0, input1))),
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

fn opt_mut(input: &str) -> IResult<&str, bool> {
    opt(keyword(Word::Mut)).map(|o|o.is_some()).parse(input)
}

fn call_suffix(name: String) -> impl Fn(&str) -> IResult<&str, Expr> {
    move |input: &str| {
        let (input, args) = delimited(
            symbol(Symbol::OpenParen),
            separated_list0(symbol(Symbol::Comma), pair(opt_mut, expr_comma)),
            symbol(Symbol::CloseParen),
        )
        .parse(input)?;
        let (mutable_args, args) = args.into_iter().unzip();
        Ok((
            input,
            mk::function_call(&name, args, mutable_args)
        ))
    }
}

fn expr_or_empty(input: &str) -> IResult<&str, Expr> {
    let (input, expr_opt) = opt(expr).parse(input)?;
    match expr_opt {
        Some(expr) => Ok((input, expr)),
        None => Ok((input, Literal::Unit.as_expr().between(input, input))),
    }
}

fn semicolon_suffix(left: Expr) -> impl Fn(&str) -> IResult<&str, Expr> {
    move |input: &str| {
        let (input0, _) = whitespace0(input)?;
        let (input1, _) = symbol(Symbol::Semicolon)(input0)?;
        let (input2, right) = expr_or_empty(input1)?;
        Ok((
            input2,
            left.clone().semicolon(right).between(input1, input2)
        ))
    }
}

fn expr_tight(input: &str) -> IResult<&str, Expr> {
    alt((
        variable_or_call,
        literal,
        expr_vector,
        expr_parenthesized,
        delimited(symbol(Symbol::OpenBrace), expr, symbol(Symbol::CloseBrace)),
    ))
    .parse(input)
}

fn expr_suffixed(input: &str) -> IResult<&str, Expr> {
    let (input0, base) = expr_tight(input)?;
    let (input1, sym) = opt(alt((symbol(Symbol::OpenSquare), /*symbol(Symbol::Dot)*/))).parse(input0)?;
    match sym {
        None => Ok((input1, base)),
        Some(Symbol::OpenSquare) => {
            let (input2, index) = terminated(expr_comma, symbol(Symbol::CloseSquare)).parse(input1)?;
            Ok((
                input2,
                base.square_bracket_at(index).between(input0, input1)
            ))
        }
        // Some(Symbol::Dot) => {
        //     let (input2, index) = integer_u64(input1)?;
        //     Ok((
        //         input2,
        //         base.dot_at(index as usize).between(input0, input2)
        //     ))
        // }
        _ => unreachable!()
    }
}

fn expr_prefixed(input: &str) -> IResult<&str, Expr> {
    let (input0, _) = whitespace0(input)?;
    let (input1, minus) = opt(symbol(Symbol::Minus)).parse(input0)?;
    if minus.is_none() {
        return expr_suffixed(input0);
    }
    let (input2, expr) = expr_suffixed(input1)?;
    Ok((
        input2,
        mk::immut_function_call("neg", vec![expr]).between(input0, input1)
    ))
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
    fn to_function_name(&self) -> &'static str {
        match self {
            Symbol::Plus => "+",
            Symbol::Minus => "-",
            Symbol::Star => "*",
            Symbol::Slash => "/",
            Symbol::Percent => "%",
            Symbol::EqualEqual => "==",
            Symbol::NotEqual => "!=",
            Symbol::Lt => "<",
            Symbol::Le => "<=",
            Symbol::Gt => ">",
            Symbol::Ge => ">=",
            _ => unreachable!(),
        }
    }
}

fn expr_times_divide_mod(input: &str) -> IResult<&str, Expr> {
    let (input, mut exprs) = expr_prefixed(input)?;
    let mut inp = input;
    loop {
        let (input0, _) = whitespace0(inp)?;
        let (input1, sym) = opt(timesdividemod).parse(input0)?;
        if sym.is_none() {
            return Ok((input1, exprs));
        }
        let (input2, rhs) = expr_prefixed(input1)?;
        exprs = mk::immut_function_call(sym.unwrap().to_function_name(), vec![exprs, rhs]).between(input0, input1);
        inp = input2;
    }
}

fn expr_plusminus(input: &str) -> IResult<&str, Expr> {
    let (input, mut exprs) = expr_times_divide_mod(input)?;
    let mut inp = input;
    loop {
        let (input0, _) = whitespace0(inp)?;
        let (input1, sym) = opt(plusminus).parse(input0)?;
        if sym.is_none() {
            return Ok((input1, exprs));
        }
        let (input2, rhs) = expr_times_divide_mod(input1)?;
        exprs = mk::immut_function_call(sym.unwrap().to_function_name(), vec![exprs, rhs]).between(input0, input1);
        inp = input2;
    }
}

fn expr_cmp(input: &str) -> IResult<&str, Expr> {
    let (input, expr) = expr_plusminus(input)?;
    let (input0, _) = whitespace0(input)?;
    let (input1, sym) = opt(cmpop).parse(input0)?;
    if sym.is_none() {
        return Ok((input1, expr));
    }
    let (input2, rhs) = expr_plusminus(input1)?;
    let new_expr = mk::immut_function_call(
        sym.unwrap().to_function_name(),
        vec![expr, rhs],
    ).between(input0, input1);
    Ok((input2, new_expr))
}

fn expr_conjunction(input: &str) -> IResult<&str, Expr> {
    let (input, expr) = expr_cmp(input)?;
    let (input0, _) = whitespace0(input)?;
    let (input1, sym) = opt(symbol(Symbol::LogicalAnd)).parse(input0)?;
    if sym.is_none() {
        return Ok((input1, expr));
    }
    let (input2, rhs) = expr_conjunction(input1)?;
    let new_expr = mk::immut_function_call(
        "&&",
        vec![expr, rhs],
    ).between(input0, input1);
    Ok((input2, new_expr))
}

fn expr_disjunction(input: &str) -> IResult<&str, Expr> {
    let (input, expr) = expr_conjunction(input)?;
    let (input0, _) = whitespace0(input)?;
    let (input1, sym) = opt(symbol(Symbol::LogicalOr)).parse(input0)?;
    if sym.is_none() {
        return Ok((input1, expr));
    }
    let (input2, rhs) = expr_disjunction(input1)?;
    let new_expr = mk::immut_function_call(
        "||",
        vec![expr, rhs],
    ).between(input0, input1);
    Ok((input2, new_expr))
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
    let (input0, _) = whitespace0(input)?;
    let (input1, _) = symbol(Symbol::OpenParen)(input0)?;
    let (input2, elems) = separated_list0(symbol(Symbol::Comma), expr_comma).parse(input1)?;
    let (input3, comma) = opt(symbol(Symbol::Comma)).parse(input2)?;
    let (input4, _) = symbol(Symbol::CloseParen)(input3)?;
    if elems.is_empty() {
        if comma.is_some() {
            // (,) is invalid
            return Err(nom::Err::Error(nom::error::Error::new(
                input4,
                nom::error::ErrorKind::Tag,
            )));
        }
        // ()
        Ok((input4, Literal::Unit.as_expr().between(input0, input4)))
    } else {
        if comma.is_some() || elems.len() > 1 {
            // (x,) or (x,y...)
            Ok((input4, mk::tuple(elems).between(input0, input1)))
        } else {
            // (x)
            Ok((input4, elems.into_iter().next().unwrap()))
        }
    }
}

fn expr_vector(input: &str) -> IResult<&str, Expr> {
    let (input0, _) = whitespace0(input)?;
    let (input1, _) = symbol(Symbol::OpenSquare)(input0)?;
    let (input2, elems) = separated_list0(symbol(Symbol::Comma), expr_comma).parse(input1)?;
    let (input3, comma) = opt(symbol(Symbol::Comma)).parse(input2)?;
    let (input4, _) = symbol(Symbol::CloseSquare)(input3)?;
    if comma.is_some() && elems.is_empty() {
        // [,] is invalid
        return Err(nom::Err::Error(nom::error::Error::new(
            input4,
            nom::error::ErrorKind::Tag,
        )));
    }
    Ok((
        input4,
        mk::vector(elems).between(input0, input1)
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

fn expr_let(input: &str) -> IResult<&str, Expr> {
    let (input0, _) = whitespace0(input)?;
    let (input1, _) = keyword(Word::Let)(input)?;
    let (input2, mutable) = opt(keyword(Word::Mut)).parse(input1)?;
    let (input3, name) = identifier(input2)?;
    let (input4, t) = opt(preceded(symbol(Symbol::Colon), typ)).parse(input3)?;
    if mutable.is_some() && t.is_none() {
        return Err(nom::Err::Error(nom::error::Error::new(
            input4,
            nom::error::ErrorKind::Tag,
        )));
    }
    let (input5, _) = symbol(Symbol::Assign)(input4)?;
    let (input6, value) = expr_comma(input5)?;
    let (input7, _) = symbol(Symbol::Semicolon)(input6)?;
    let (input8, body) = expr_or_empty(input7)?;  // empty would be a bit weird here as we'd be defining a variable that then goes unused
    Ok((
        input8,
        mk::let_expr(name, mutable.is_some(), t, value, body).between(input0, input2)
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

fn expr_assign(input: &str) -> IResult<&str, Expr> {
    let (input0, name) = identifier(input)?;
    let (input1, _) = whitespace0(input0)?;
    let (input2, op) = assignop(input1)?;
    let (input3, value) = expr_comma(input2)?;
    let (input4, _) = symbol(Symbol::Semicolon)(input3)?;
    let (input5, body) = expr_or_empty(input4)?;
    Ok((input5, mk::assign(mk::untyped_var(name), op, value).between(input1, input2).semicolon(body).between(input3, input4)))
}

fn expr(input: &str) -> IResult<&str, Expr> {
    alt((expr_let, expr_assign, expr_semicolon)).parse(input)
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
    let (input, type_params) = opt(delimited(
        symbol(Symbol::Lt),
        separated_list1(symbol(Symbol::Comma), identifier),
        symbol(Symbol::Gt),
    ))
    .parse(input)?;
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
            type_params: type_params.unwrap_or_else(Vec::new),
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
        let stmt = "let x = 5; ()";
        let result = super::expr(stmt);
        assert!(result.is_ok());
        assert_eq!(result.unwrap().0, "");
    }

    #[test]
    fn test_let_mut() {
        let stmt = "let mut x:u64 = 5; ()";
        let result = super::expr(stmt);
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
        let stmt = "x += 10; ()";
        let result = super::expr(stmt);
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
