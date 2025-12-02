use nom::{IResult, Parser, branch::alt, bytes::complete::{tag, take_until, take_while, take_while1}, character::complete::{anychar, satisfy}, combinator::{all_consuming, map, opt, recognize, value}, multi::{many0, separated_list0}, sequence::{delimited, preceded, terminated}};

use crate::syntax::ast::*;

enum Word {
    Identifier(String),
    Fn,
    Let,
}

#[derive(PartialEq, Eq, Copy, Clone)]
enum Symbol {
    Semicolon,
    Comma,
    OpenParen,
    CloseParen,
    OpenBrace,
    CloseBrace,
 
    Colon,
    Assign,
    Arrow,
}

fn pure_whitespace1(input: &str) -> IResult<&str, &str> {
    take_while1(|c: char| c.is_whitespace())(input)
}

fn comment(input: &str) -> IResult<&str, &str> {
    preceded(
        tag("//"),
        take_while(|c| c != '\n')
    ).parse(input)
}

fn multiline_comment(input: &str) -> IResult<&str, &str> {
    preceded(
        tag("/*"),
        take_until("*/")
    ).parse(input)
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
    let (input, ident) = preceded(whitespace0, recognize(
        preceded(satisfy(alpha_underscore), take_while(alphanum_underscore))
    )).parse(input)?;
    let word = match ident {
        "fn" => Word::Fn,
        _ => Word::Identifier(ident.to_string()),
    };
    Ok((input, word))
}

fn integer(input: &str) -> IResult<&str, Literal> {
    let (input, int_str) = preceded(whitespace0, recognize(
        many0(satisfy(|c| c.is_ascii_digit()))
    )).parse(input)?;
    let int_value: Result<i64,_> = int_str.parse();
    match int_value {
        Ok(v) => Ok((input, Literal::I64(v))),
        Err(_) => {
            let uint_value: Result<u64,_> = int_str.parse();
            match uint_value {
                Ok(uv) => Ok((input, Literal::U64(uv))),
                Err(_) => Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Digit))),
            }
        }
    }
}

fn normal_string_char(c: char) -> bool {
    c != '"' && c != '\\'
}

fn normal_string_contents1(input: &str) -> IResult<&str, String> {
    map(take_while1(normal_string_char), |s: &str| s.to_owned()).parse(input)
}

fn escaped_char(input: &str) -> IResult<&str, String> {
    map(preceded(
        tag("\\"),
        alt((
            value('\\', tag("\\")),
            value('\"', tag("\"")),
            value('\'', tag("\'")),
            value('\n', tag("n")),
            value('\r', tag("r")),
            value('\t', tag("t")),
        ))
    ), |c| c.to_string()).parse(input)
}

fn string_contents(input: &str) -> IResult<&str, String> {
    map(many0(alt((
        normal_string_contents1,
        escaped_char
    ))), |pieces: Vec<String>| pieces.concat()).parse(input)
}

fn string(input: &str) -> IResult<&str, Literal> {
    map(
        preceded(whitespace0, delimited(tag("\""), string_contents, tag("\""))),
        Literal::Str)
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
        _ => Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Char))),
    }
}

fn is_multi_char_sym(ch: char) -> bool {
    match ch {
        ':' | '=' | '-' | '<' | '>' => true,
        _ => false,
    }
}

fn multi_char_sym(input: &str) -> IResult<&str, Symbol> {
    let (input, string) = take_while1(is_multi_char_sym)(input)?;
    match string {
        ":" => Ok((input, Symbol::Colon)),
        "=" => Ok((input, Symbol::Assign)),
        "->" => Ok((input, Symbol::Arrow)),
        _ => Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Char))),
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
            Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Tag)))
        }
    }
}

fn literal(input: &str) -> IResult<&str, Expr> {
    map(alt((
        integer,
        string,
    )), Expr::Literal).parse(input)
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
        _ => Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Tag))),
    }
}

fn variable_or_call(input: &str) -> IResult<&str, Expr> {
    let (input, name) = identifier(input)?;
    let (input, call_opt) = opt(call_suffix(name.clone())).parse(input)?;
    match call_opt {
        Some(call_expr) => Ok((input, call_expr)),
        None => Ok((input, Expr::Variable(name))),
    }
}

fn typ(input: &str) -> IResult<&str, Type> {
    let (input, name) = identifier(input)?;
    Ok((input, Type { name }))
}

fn call_suffix(name: String) -> impl Fn(&str) -> IResult<&str, Expr> {
    move |input: &str| {
        let (input, args) = delimited(
            symbol(Symbol::OpenParen),
            separated_list0(symbol(Symbol::Comma), expr_comma),
            symbol(Symbol::CloseParen)
        ).parse(input)?;
        Ok((input, Expr::FunctionCall {
            name: name.clone(),
            args,
        }))
    }
}
fn semicolon_suffix(left: Expr) -> impl Fn(&str) -> IResult<&str, Expr> {
    move |input: &str| {
        let (input, _) = symbol(Symbol::Semicolon)(input)?;
        let (input, right) = expr(input)?;
        Ok((input, Expr::Semicolon(Box::new(Stmt::Expr(left.clone())), Box::new(right))))
    }
}

fn expr_comma(input: &str) -> IResult<&str, Expr> {
    alt((
        variable_or_call,
        literal,
        delimited(symbol(Symbol::OpenParen), expr, symbol(Symbol::CloseParen)),
        delimited(symbol(Symbol::OpenBrace), expr, symbol(Symbol::CloseBrace))
    )).parse(input)
}

fn expr_semicolon(input: &str) -> IResult<&str, Expr> {
    let (input, first) = expr_comma(input)?;
    let (input, second) = opt(semicolon_suffix(first.clone())).parse(input)?;
    match second {
        Some(expr) => Ok((input, expr)),
        None => Ok((input, first)),
    }
}

fn keyword(expected: Word) -> impl Fn(&str) -> IResult<&str, Word> {
    move |input: &str| {
        let (input, word) = preceded(whitespace0, word).parse(input)?;
        if std::mem::discriminant(&word) == std::mem::discriminant(&expected) {
            Ok((input, word))
        } else {
            Err(nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Tag)))
        }
    }
}

fn stmt_let(input: &str) -> IResult<&str, Stmt> {
    let (input, _) = keyword(Word::Let)(input)?;
    let (input, name) = identifier(input)?;
    let (input, _) = symbol(Symbol::Assign)(input)?;
    let (input, value) = expr(input)?;
    Ok((input, Stmt::Let {
        name,
        value,
    }))
}

fn stmt(input: &str) -> IResult<&str, Stmt> {
    alt((
        stmt_let,
    )).parse(input)
}

fn stmt_semicolon(input: &str) -> IResult<&str, Expr> {
    let (input, first) = stmt(input)?;
    let (input, _) = symbol(Symbol::Semicolon)(input)?;
    let (input, second) = expr(input)?;
    Ok((input, Expr::Semicolon(Box::new(first), Box::new(second))))
}

fn expr(input: &str) -> IResult<&str, Expr> {
    alt((expr_semicolon, stmt_semicolon)).parse(input)
}

fn arg(input: &str) -> IResult<&str, Arg> {
    let (input, name) = identifier(input)?;
    let (input, _) = symbol(Symbol::Colon)(input)?;
    let (input, arg_type) = typ(input)?;
    Ok((input, Arg {
        name,
        arg_type,
    }))
}

fn funcdef(input: &str) -> IResult<&str, FuncDef> {
    let (input, _) = keyword(Word::Fn)(input)?;
    let (input, name) = identifier(input)?;
    let (input, args) = delimited(
        symbol(Symbol::OpenParen),
        separated_list0(symbol(Symbol::Comma), arg),
        symbol(Symbol::CloseParen)
    ).parse(input)?;
    let (input, _) = symbol(Symbol::Arrow)(input)?;
    let (input, return_type) = typ(input)?;
    let (input, body) = delimited(
        symbol(Symbol::OpenBrace),
        expr,
        symbol(Symbol::CloseBrace)
    ).parse(input)?;
    Ok((input, FuncDef {
        name,
        args,
        return_type,
        body,
    }))
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
    use nom::bytes::complete::tag;
    use nom::multi::{many0, separated_list0};
    use nom::sequence::{delimited};
    use nom::Parser;

    use crate::syntax::parse::Symbol;

    #[test]
    fn test_var()
    {
        let expr = "my_variable";
        let result = super::variable_or_call(expr);
        assert!(result.is_ok());
    }

    #[test]
    fn test_empty()
    {
        let expr = "";
        let result = super::expr(expr);
        assert!(!result.is_ok());
    }

    #[test]
    fn test_parens() {
        let expr = "()";
        let result = delimited(super::symbol(Symbol::OpenParen), separated_list0(super::symbol(Symbol::Comma), super::expr), super::symbol(Symbol::CloseParen)).parse(expr);
        assert!(result.expect("Failed to parse parens").0.is_empty());
    }

    #[test]
    fn test_empty_call_suffix()
    {
        let suffix = "()";
        let result = super::call_suffix("my_function".to_string())(suffix);
        assert!(result.is_ok());
    }

    #[test]
    fn test_empty_call()
    {
        let expr = "foo()";
        let result = super::expr(expr);
        assert!(result.is_ok());
    }

    #[test]
    fn test_hello() {
        let expr = "println(\"Hello, world!\")";
        let result = super::expr(expr);
        assert!(result.is_ok());
    }
}