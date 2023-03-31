use std::iter::Peekable;

#[derive(PartialEq, Debug, Clone)]
enum TokenType {
    Symbol(String),
    String(String),
    Num(f64),
    LeftParen,
    RightParen,
    Comma,
    Plus,
    Minus,
    Divide,
    Multiply,
    Assign,
    Void,

    Unknown(String),
}

impl ToString for TokenType {
    fn to_string(&self) -> String {
        match self {
            TokenType::Symbol(s) => format!("Symbol({})", s),
            TokenType::String(s) => format!("String({})", s),
            TokenType::Num(n) => format!("Num({})", n),
            TokenType::LeftParen => "(".to_owned(),
            TokenType::RightParen => ")".to_owned(),
            TokenType::Comma => ",".to_owned(),
            TokenType::Plus => "+".to_owned(),
            TokenType::Minus => "-".to_owned(),
            TokenType::Divide => "/".to_owned(),
            TokenType::Multiply => "*".to_owned(),
            TokenType::Assign => "=".to_owned(),
            TokenType::Void => "void".to_owned(),
            TokenType::Unknown(unknown) => format!("Unknown({})", unknown)
        }
    }
}

#[derive(Debug, PartialEq, Default, Clone)]
struct Loc<'a> {
    file_path: Option<&'a str>,
    row: usize,
    col: usize,
}

impl std::fmt::Display for Loc<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut file_path = String::new();
        if let Some(fp) = self.file_path {
            file_path = format!("{}:", fp);
        }
        write!(f, "{}{}:{}", file_path, self.row, self.col)
    }
}

#[derive(Debug, PartialEq)]
struct Token<'a> {
    loc: Loc<'a>,
    token_type: TokenType,
}

struct Lexer<'a> {
    file_path: Option<&'a str>,
    row: usize,
    col: usize,
    source: std::iter::Peekable<std::str::Chars<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(path: Option<&'a str>, source: &'a str) -> Self {
        Self {
            file_path: path,
            col: 0,
            row: 1,
            source: source.chars().peekable(),
        }
    }

    fn trim_white_space(&mut self) {
        let mut char = self.source.peek();
        while char.is_some() && char.unwrap().is_whitespace() {
            self.col += 1;
            if char.unwrap() == &'\n' {
                self.col = 0;
                self.row += 1;
            }
            self.source.next();
            char = self.source.peek();
        }
    }

    fn consume_until_string_end(&mut self) -> String {
        let mut string = String::new();
        let mut char = self.source.next();
        self.col += 1;
        while char.is_some() {
            let c = char.unwrap();
            if c == '\\' {
                let nc = self.source.next();
                self.col += 1;
                if nc == None || nc == Some('\n') {
                    return string;
                }
                string.push(nc.unwrap());
            } else if c == '"' {
                return string;
            } else {
                string.push(c);
            }
            char = self.source.next();
            self.col += 1;
        }
        string
    }

    fn consume_number(&mut self, first: char) -> Option<f64> {
        let mut string = String::new();
        string.push(first);
        let mut char = self.source.peek();
        while char.is_some() && (char.unwrap().is_numeric() || char.unwrap() == &'.') {
            string.push(self.source.next().unwrap());
            self.col += 1;
            char = self.source.peek();
        }
        string.parse::<f64>().ok()
    }

    fn consume_symbol(&mut self, first: char) -> String {
        let mut string = String::new();
        string.push(first);
        let mut char = self.source.peek();
        while char.is_some() && (char.unwrap().is_alphanumeric() || char.unwrap() == &'_') {
            string.push(self.source.next().unwrap());
            self.col += 1;
            char = self.source.peek();
        }
        string
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        self.trim_white_space();
        match self.source.next() {
            Some(char) => {
                self.col += 1;
                let loc = Loc {
                    file_path: self.file_path,
                    row: self.row.clone(),
                    col: self.col.clone(),
                };
                let mut token_type = TokenType::Unknown(char.to_string());
                if char == '(' {
                    token_type = TokenType::LeftParen;
                }
                if char == ')' {
                    token_type = TokenType::RightParen;
                }
                if char == ',' {
                    token_type = TokenType::Comma;
                }
                if char == '"' {
                    let string = self.consume_until_string_end();
                    token_type = TokenType::String(string);
                }
                if char == '+' {
                    token_type = TokenType::Plus;
                }
                if char == '-' {
                    token_type = TokenType::Minus;
                }
                if char == '/' {
                    token_type = TokenType::Divide;
                }
                if char == '*' {
                    token_type = TokenType::Multiply;
                }
                if char == '=' {
                    token_type = TokenType::Assign;
                }
                if char.is_numeric() {
                    match self.consume_number(char) {
                        Some(num) => token_type = TokenType::Num(num),
                        None => (),
                    }
                }
                if char.is_alphabetic() || char == '_' {
                    let symbol = self.consume_symbol(char);
                    token_type = TokenType::Symbol(symbol.clone());
                    if symbol == "void" {
                        token_type = TokenType::Void;
                    }
                }

                Some(Token { loc, token_type })
            }
            None => None,
        }
    }
}

#[derive(PartialEq, Debug)]
enum ExprType<'a> {
    Void,
    Num(f64),
    Str(String),
    Var(String),
    Plus(Box<Expr<'a>>, Box<Expr<'a>>),
    Minus(Box<Expr<'a>>, Box<Expr<'a>>),
    Multiply(Box<Expr<'a>>, Box<Expr<'a>>),
    Divide(Box<Expr<'a>>, Box<Expr<'a>>),
    Assignment(Box<Expr<'a>>, Box<Expr<'a>>),
    FunCall(FunCall<'a>),
}

impl ToString for ExprType<'_> {
    fn to_string(&self) -> String {
        match self {
            ExprType::Void => "Void",
            ExprType::Num(_) => "Number",
            ExprType::Str(_) => "String",
            ExprType::Var(_) => "Variable",
            ExprType::Plus(_, _) => "Plus operator",
            ExprType::Minus(_, _) => "Minus operator",
            ExprType::Multiply(_, _) => "Multiply operator",
            ExprType::Divide(_, _) => "Divide operator",
            ExprType::Assignment(_, _) => "Assignment operator",
            ExprType::FunCall(_) => "Function call",
        }
        .to_string()
    }
}

impl<'a> ExprType<'a> {
    fn is_var(&self) -> bool {
        matches!(self, Self::Var(..))
    }

    fn as_fun_call(&self) -> Option<&FunCall<'a>> {
        if let Self::FunCall(v) = self {
            Some(v)
        } else {
            None
        }
    }

    fn as_var(&self) -> Option<&String> {
        if let Self::Var(v) = self {
            Some(v)
        } else {
            None
        }
    }

    fn as_num(&self) -> Option<&f64> {
        if let Self::Num(v) = self {
            Some(v)
        } else {
            None
        }
    }

    fn as_plus(&self) -> Option<(&Box<Expr<'a>>, &Box<Expr<'a>>)> {
        if let Self::Plus(lhs, rhs) = self {
            Some((lhs, rhs))
        } else {
            None
        }
    }

    fn as_minus(&self) -> Option<(&Box<Expr<'a>>, &Box<Expr<'a>>)> {
        if let Self::Minus(lhs, rhs) = self {
            Some((lhs, rhs))
        } else {
            None
        }
    }

    fn as_multiply(&self) -> Option<(&Box<Expr<'a>>, &Box<Expr<'a>>)> {
        if let Self::Multiply(lhs, rhs) = self {
            Some((lhs, rhs))
        } else {
            None
        }
    }

    fn as_divide(&self) -> Option<(&Box<Expr<'a>>, &Box<Expr<'a>>)> {
        if let Self::Divide(lhs, rhs) = self {
            Some((lhs, rhs))
        } else {
            None
        }
    }

    fn as_assignment(&self) -> Option<(&Box<Expr<'a>>, &Box<Expr<'a>>)> {
        if let Self::Assignment(lhs, rhs) = self {
            Some((lhs, rhs))
        } else {
            None
        }
    }

    fn as_str(&self) -> Option<&String> {
        if let Self::Str(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

/// Expression in an expression tree following the grammar:
/// ```ignore
/// expr        => assignment 
/// assignment  => var "=" fun_call | fun_call
/// fun_call    => term "(" expr ("," expr )* ")" | term
/// term        => factor (("+" | "-") term)
/// factor      => primary (("*" | "/") factor)
/// primary     => num | str | var | "(" num | fun_call | term | factor ")" | "void"
/// ```
#[derive(PartialEq)]
struct Expr<'a> {
    loc: Loc<'a>,
    expr_type: ExprType<'a>,
}

impl std::fmt::Debug for Expr<'_> {
    fn fmt(&self, _: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.dump_expr(0);
        Ok(())
    }
}

#[derive(PartialEq, Debug)]
struct FunCall<'a> {
    fun: Box<Expr<'a>>,
    args: Vec<Expr<'a>>,
}

#[derive(Debug)]
enum ExprParsingErrorType {
    UnexpectedEOFWhile(String),
    PrimaryExprExpected(String),
    CannotAssignToNonVar(String),
    UnexpectedToken(String),
    CanNotNest(String),
}

#[derive(Debug)]
struct ExprParsingError<'a> {
    err_type: ExprParsingErrorType,
    loc: Loc<'a>,
}

impl std::fmt::Display for ExprParsingError<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "ERROR: while parsing at: {}", self.loc)?;
        match &self.err_type {
            ExprParsingErrorType::UnexpectedEOFWhile(string) => {
                writeln!(f, "  Unexpected end of file while {}", string)
            }
            ExprParsingErrorType::UnexpectedToken(token) => {
                writeln!(f, "  Unexpected Token: {}", token)
            }
            ExprParsingErrorType::PrimaryExprExpected(string) => {
                writeln!(
                    f,
                    "  A primary expression expected (number, string, variable, function), got: {}",
                    string
                )
            }
            ExprParsingErrorType::CannotAssignToNonVar(string) => {
                writeln!(f, "  Can not assign to a {}", string)
            }
            ExprParsingErrorType::CanNotNest(string) => {
                writeln!(f, "  Can not nest {}", string)
            }
        }
    }
}
impl std::error::Error for ExprParsingError<'_> {}

impl<'a> Expr<'a> {
    fn dump_expr(&self, level: usize) {
        for _ in 0..level {
            print!("  ");
        }

        match &self.expr_type {
            ExprType::Void => println!("{} Void", self.loc),
            ExprType::Num(num) => println!("{} Number: {}", self.loc, num),
            ExprType::Str(string) => println!("{} String: \"{}\"", self.loc, string),
            ExprType::Var(var) => println!("{} Variable: {}", self.loc, var),

            ExprType::FunCall(fc) => {
                println!("{} Function Call:", self.loc);
                fc.fun.dump_expr(level+1);
                for fc_arg in &fc.args {
                    fc_arg.dump_expr(level + 1)
                }
            }
            ExprType::Plus(lhs, rhs) => {
                println!("{} Plus:", self.loc);
                lhs.dump_expr(level + 1);
                for _ in 0..level + 1 {
                    print!("  ");
                }
                println!("+");
                rhs.dump_expr(level + 1);
            }
            ExprType::Minus(lhs, rhs) => {
                println!("{} Minus:", self.loc);
                lhs.dump_expr(level + 1);
                for _ in 0..level + 1 {
                    print!("  ");
                }
                println!("-");
                rhs.dump_expr(level + 1);
            }
            ExprType::Multiply(lhs, rhs) => {
                println!("{} Multiply:", self.loc);
                lhs.dump_expr(level + 1);
                for _ in 0..level + 1 {
                    print!("  ");
                }
                println!("*");
                rhs.dump_expr(level + 1);
            }
            ExprType::Divide(lhs, rhs) => {
                println!("{} Divide:", self.loc);
                lhs.dump_expr(level + 1);
                for _ in 0..level + 1 {
                    print!("  ");
                }
                println!("/");
                rhs.dump_expr(level + 1);
            }

            ExprType::Assignment(lhs, rhs) => {
                println!("{} Assignment:", self.loc);
                lhs.dump_expr(level + 1);
                for _ in 0..level + 1 {
                    print!("  ");
                }
                println!("=");
                rhs.dump_expr(level + 1);
            }
        }
    }

    fn parse_primary(lexer: &mut Peekable<Lexer<'a>>) -> Result<Expr<'a>, ExprParsingError<'a>> {
        match lexer.next() {
            Some(token) => match token.token_type {
                TokenType::Symbol(symbol) => {
                    Ok(Expr {
                        expr_type: ExprType::Var(symbol.clone()),
                        loc: token.loc.clone(),
                    })
                }
                TokenType::String(string) => Ok(Expr {
                    loc: token.loc,
                    expr_type: ExprType::Str(string),
                }),
                TokenType::Num(num) => Ok(Expr {
                    loc: token.loc,
                    expr_type: ExprType::Num(num),
                }),
                TokenType::LeftParen => {
                    let expr: Expr = Expr::parse_expr(lexer)?;
                    if let Some(t) = lexer.next() {
                        if t.token_type != TokenType::RightParen {
                            return Err(ExprParsingError { err_type: ExprParsingErrorType::UnexpectedToken(format!("{}, expected: )", t.token_type.to_string())), loc: t.loc })
                        }
                    } else {
                        return Err(ExprParsingError { err_type: ExprParsingErrorType::UnexpectedEOFWhile("parsing a nesting".to_string()), loc: token.loc });
                    }
                    match expr.expr_type {
                        ExprType::Num(_) | ExprType::Plus(_, _) | ExprType::Minus(_, _) | ExprType::Multiply(_, _) | ExprType::Divide(_, _) | ExprType::FunCall(_) => {
                            Ok(expr)
                        },
                        
                        ExprType::Void | ExprType::Var(_) | ExprType::Str(_) | ExprType::Assignment(_, _) => {
                            Err(ExprParsingError { err_type: ExprParsingErrorType::CanNotNest(expr.expr_type.to_string()), loc: expr.loc })
                        },
                    }
                }
                TokenType::Void => {
                    Ok( Expr { expr_type: ExprType::Void, loc: token.loc } )
                }
                _ => Err(ExprParsingError {
                    err_type: ExprParsingErrorType::PrimaryExprExpected(
                        token.token_type.to_string(),
                    ),
                    loc: token.loc,
                }),
            },
            None => unreachable!("Make sure to handle EOFs"),
        }
    }

    fn parse_factor(lexer: &mut Peekable<Lexer<'a>>) -> Result<Expr<'a>, ExprParsingError<'a>> {
        let primary = Expr::parse_primary(lexer)?;
        if lexer.peek().is_some()
            && (lexer.peek().unwrap().token_type == TokenType::Multiply
                || lexer.peek().unwrap().token_type == TokenType::Divide)
        {
            let token = lexer.next().expect("This token to be multiply or divide");
            match token.token_type {
                TokenType::Multiply => {
                    if lexer.peek().is_none() {
                        return Err(ExprParsingError {
                            err_type: ExprParsingErrorType::UnexpectedEOFWhile(
                                "parsing a multiplication. Did you forget to add a second value?"
                                    .to_owned(),
                            ),
                            loc: token.loc,
                        });
                    }
                    return Ok(Expr {
                        loc: token.loc,
                        expr_type: ExprType::Multiply(
                            Box::new(primary),
                            Box::new(Expr::parse_factor(lexer)?),
                        ),
                    });
                }
                TokenType::Divide => {
                    if lexer.peek().is_none() {
                        return Err(ExprParsingError {
                            err_type: ExprParsingErrorType::UnexpectedEOFWhile(
                                "parsing a division. Did you forget to add a second value?"
                                    .to_owned(),
                            ),
                            loc: token.loc,
                        });
                    }
                    return Ok(Expr {
                        loc: token.loc,
                        expr_type: ExprType::Divide(
                            Box::new(primary),
                            Box::new(Expr::parse_factor(lexer)?),
                        ),
                    });
                }
                _ => {
                    return Err(ExprParsingError {
                        err_type: ExprParsingErrorType::UnexpectedToken(
                            token.token_type.to_string(),
                        ),
                        loc: token.loc,
                    });
                }
            }
        }
        Ok(primary)
    }

    fn parse_term(lexer: &mut Peekable<Lexer<'a>>) -> Result<Expr<'a>, ExprParsingError<'a>> {
        let factor = Expr::parse_factor(lexer)?;
        if lexer.peek().is_some()
            && (lexer.peek().unwrap().token_type == TokenType::Plus
                || lexer.peek().unwrap().token_type == TokenType::Minus)
        {
            let token = lexer.next().expect("This token to be plus or minus");
            match token.token_type {
                TokenType::Plus => {
                    if lexer.peek().is_none() {
                        return Err(ExprParsingError {
                            err_type: ExprParsingErrorType::UnexpectedEOFWhile(
                                "parsing an addition. Did you forget to add a second value?"
                                    .to_owned(),
                            ),
                            loc: token.loc,
                        });
                    }
                    return Ok(Expr {
                        loc: token.loc,
                        expr_type: ExprType::Plus(
                            Box::new(factor),
                            Box::new(Expr::parse_term(lexer)?),
                        ),
                    });
                }
                TokenType::Minus => {
                    if lexer.peek().is_none() {
                        return Err(ExprParsingError {
                            err_type: ExprParsingErrorType::UnexpectedEOFWhile(
                                "parsing a subtraction. Did you forget to add a second value?"
                                    .to_owned(),
                            ),
                            loc: token.loc,
                        });
                    }
                    return Ok(Expr {
                        loc: token.loc,
                        expr_type: ExprType::Minus(
                            Box::new(factor),
                            Box::new(Expr::parse_term(lexer)?),
                        ),
                    });
                }
                _ => {
                    return Err(ExprParsingError {
                        err_type: ExprParsingErrorType::UnexpectedToken(
                            token.token_type.to_string(),
                        ),
                        loc: factor.loc,
                    });
                }
            }
        }
        Ok(factor)
    }

    fn parse_fun_call(lexer: &mut Peekable<Lexer<'a>>) -> Result<Expr<'a>, ExprParsingError<'a>> {
        let expr = Expr::parse_term(lexer)?;
        if lexer.peek().is_some() && lexer.peek().unwrap().token_type == TokenType::LeftParen {
            lexer.next(); // left paren (
            let mut args = vec![];
            if let Some(nt) = lexer.peek() {
                if nt.token_type == TokenType::RightParen {
                    lexer.next(); // right paren )
                    Ok(Expr { loc: expr.loc.clone(), expr_type: ExprType::FunCall(FunCall { fun: Box::new(expr), args }) })
                } else {
                    args.push(Expr::parse_term(lexer)?);
                    while lexer.peek().is_some() && lexer.peek().unwrap().token_type == TokenType::Comma {
                        lexer.next(); // comma ,
                        if lexer.peek().is_none() {
                            return Err(ExprParsingError { err_type: ExprParsingErrorType::UnexpectedEOFWhile("parsing a function call.\n  Expected a term".to_string()), loc: expr.loc })
                        } else {
                            args.push(Expr::parse_term(lexer)?);
                        }
                    };
                    let right_paren = lexer.next();
                    if right_paren.is_some() {
                        let right_paren = right_paren.unwrap();
                        if right_paren.token_type == TokenType::RightParen {
                            Ok(Expr { loc: expr.loc.clone(), expr_type: ExprType::FunCall(FunCall { fun: Box::new(expr), args }) })
                        } else {
                            Err(ExprParsingError { err_type: ExprParsingErrorType::UnexpectedToken(right_paren.token_type.to_string()), loc: expr.loc })
                        }
                    } else {
                        Err(ExprParsingError { err_type: ExprParsingErrorType::UnexpectedEOFWhile("parsing a function call.\n  Expected one of: ',' ')'".to_string()), loc: expr.loc })
                    }
                }
            } else {
                Err(ExprParsingError { err_type: ExprParsingErrorType::UnexpectedEOFWhile("parsing a function call".to_string()), loc: expr.loc })
            }
        } else {
            Ok(expr)
        }
    }


    fn parse_assignment(lexer: &mut Peekable<Lexer<'a>>) -> Result<Expr<'a>, ExprParsingError<'a>> {

        let expr = Expr::parse_fun_call(lexer)?;

        if lexer.peek().is_some() && lexer.peek().unwrap().token_type == TokenType::Assign {
            if !expr.expr_type.is_var() {
                return Err(ExprParsingError {
                    err_type: ExprParsingErrorType::CannotAssignToNonVar(
                        expr.expr_type.to_string(),
                    ),
                    loc: lexer.peek().unwrap().loc.clone(),
                });
            }
            let eq = lexer.next().unwrap();
            let rhs = Expr::parse_expr(lexer)?;
            return Ok(Expr {
                loc: eq.loc,
                expr_type: ExprType::Assignment(Box::new(expr), Box::new(rhs)),
            });
        }
        Ok(expr)
    }

    fn parse_expr(lexer: &mut Peekable<Lexer<'a>>) -> Result<Expr<'a>, ExprParsingError<'a>> {
        if lexer.peek().is_some() {
            return Ok(Expr::parse_assignment(lexer)?);
        }
        Err(ExprParsingError {
            err_type: ExprParsingErrorType::UnexpectedEOFWhile(
                "parsing expression. Expression expected".to_string(),
            ),
            loc: Loc {
                file_path: None,
                row: 0,
                col: 0,
            },
        })
    }
}

struct TLDR<'a> {
    lexer: Peekable<Lexer<'a>>,
}

impl TLDR<'static> {
    fn new(source_code: &'static str) -> Self {
        Self {lexer: Lexer::new(None, source_code).peekable()}
    }

    fn parse_expr(mut self) -> Result<Expr<'static>, Box<dyn std::error::Error>> {
        Ok(Expr::parse_expr(&mut self.lexer)?)
    }
}







fn main() {
    let tldr = TLDR::new("print(\"Hello, World!\")");
    println!("{:?}", tldr.parse_expr().unwrap());
}






#[cfg(test)]
mod tests {
    use super::*;

    fn debug_lexer<'a>(source_code: &'a str) -> Peekable<Lexer<'a>> {
        Lexer::new(None, source_code).peekable()
    }

    #[test]
    fn tokenizer_gives_correct_tokens() {
        let mut t = debug_lexer("print(\"Hello world\", 69.420) +-/*;");
        assert_eq!(
            t.next().unwrap().token_type,
            TokenType::Symbol("print".to_string())
        );
        assert_eq!(t.next().unwrap().token_type, TokenType::LeftParen);
        assert_eq!(
            t.next().unwrap().token_type,
            TokenType::String("Hello world".to_string())
        );
        assert_eq!(t.next().unwrap().token_type, TokenType::Comma);
        assert_eq!(t.next().unwrap().token_type, TokenType::Num(69.420));
        assert_eq!(t.next().unwrap().token_type, TokenType::RightParen);
        assert_eq!(t.next().unwrap().token_type, TokenType::Plus);
        assert_eq!(t.next().unwrap().token_type, TokenType::Minus);
        assert_eq!(t.next().unwrap().token_type, TokenType::Divide);
        assert_eq!(t.next().unwrap().token_type, TokenType::Multiply);
        assert_eq!(
            t.next().unwrap().token_type,
            TokenType::Unknown(";".to_owned())
        );
        assert_eq!(t.next(), None);
    }

    #[test]
    fn test_primary_parsing() -> Result<(), Box<dyn std::error::Error>> {
        let mut var = debug_lexer("a");
        let mut num = debug_lexer("1");
        let mut string = debug_lexer("\"string\"");
        let mut string_unclosed = debug_lexer("\"string");
        let mut void = debug_lexer("void");
        let mut parens = debug_lexer("((1))");

        let expr = Expr::parse_primary(&mut var)?;
        assert_eq!(
            expr.expr_type
                .as_var()
                .unwrap(),
            &"a".to_string()
        );

        let expr = Expr::parse_primary(&mut num)?;
        assert_eq!(
            expr.expr_type
                .as_num()
                .unwrap(),
            &1.
        );

        let expr = Expr::parse_primary(&mut string)?;
        assert_eq!(
            expr.expr_type
                .as_str()
                .unwrap(),
            &"string".to_string()
        );

        let expr = Expr::parse_primary(&mut string_unclosed)?;
        assert_eq!(
            expr.expr_type
                .as_str()
                .unwrap(),
            &"string".to_string()
        );

        let expr = Expr::parse_primary(&mut void)?;
        assert_eq!(
            expr.expr_type,
            ExprType::Void
        );

        let expr = Expr::parse_primary(&mut parens)?;
        assert_eq!(
            expr.expr_type
                .as_num()
                .unwrap(),
            &1.
        );


        Ok(())
    }

    #[test]
    fn test_parse_factor() -> Result<(), Box<dyn std::error::Error>> {
        let expr = Expr::parse_factor(&mut debug_lexer("420.69"))?;
        assert_eq!(expr.expr_type.as_num().unwrap(), &420.69);

        let expr = Expr::parse_factor(&mut debug_lexer("\"source \" * \"code\""))?;
        assert_eq!(
            expr.expr_type
                .as_multiply()
                .unwrap()
                .0
                .expr_type
                .as_str()
                .unwrap(),
            &"source ".to_string()
        );
        assert_eq!(
            expr.expr_type
                .as_multiply()
                .unwrap()
                .1
                .expr_type
                .as_str()
                .unwrap(),
            &"code".to_string()
        );

        let expr = Expr::parse_factor(&mut debug_lexer("\"source \" / \"code\" * 55 / 22"))?;
        assert_eq!(
            expr.expr_type
                .as_divide()
                .unwrap()
                .0
                .expr_type
                .as_str()
                .unwrap(),
            &"source ".to_string()
        );
        assert_eq!(
            expr.expr_type
                .as_divide()
                .unwrap()
                .1
                .expr_type
                .as_multiply()
                .unwrap()
                .0
                .expr_type
                .as_str()
                .unwrap(),
            &"code".to_string()
        );

        assert_eq!(
            expr.expr_type
                .as_divide()
                .unwrap()
                .1
                .expr_type
                .as_multiply()
                .unwrap()
                .1
                .expr_type
                .as_divide()
                .unwrap()
                .0
                .expr_type
                .as_num()
                .unwrap(),
            &55.
        );

        assert_eq!(
            expr.expr_type
                .as_divide()
                .unwrap()
                .1
                .expr_type
                .as_multiply()
                .unwrap()
                .1
                .expr_type
                .as_divide()
                .unwrap()
                .1
                .expr_type
                .as_num()
                .unwrap(),
            &22.
        );

        let expr = Expr::parse_factor(&mut debug_lexer("(1 + 5) * 5"))?;
        assert_eq!(
            expr.expr_type
                .as_multiply()
                .unwrap()
                .0
                .expr_type
                .as_plus()
                .unwrap()
                .0
                .expr_type
                .as_num()
                .unwrap(),
            &1.
        );
        assert_eq!(
            expr.expr_type
                .as_multiply()
                .unwrap()
                .0
                .expr_type
                .as_plus()
                .unwrap()
                .1
                .expr_type
                .as_num()
                .unwrap(),
            &5.
        );
        assert_eq!(
            expr.expr_type
                .as_multiply()
                .unwrap()
                .1
                .expr_type
                .as_num()
                .unwrap(),
            &5.
        );

        Expr::parse_factor(&mut debug_lexer("\"source \" * "))
            .expect_err("Expected to err");

        Expr::parse_factor(&mut debug_lexer("\"source \" / /"))
            .expect_err("Expected to err");
        
        Ok(())
    }

    #[test]
    fn test_parse_term() -> Result<(), Box<dyn std::error::Error>> {
        let expr = Expr::parse_term(&mut debug_lexer("420.69"))?;
        assert_eq!(
            expr.expr_type
                .as_num()
                .unwrap(),
            &420.69
        );

        let expr = Expr::parse_term(&mut debug_lexer("\"source \" + \"code\""))?;
        assert_eq!(
            expr.expr_type
                .as_plus()
                .unwrap()
                .0
                .expr_type
                .as_str()
                .unwrap(),
            &"source ".to_string()
        );
        assert_eq!(
            expr.expr_type
                .as_plus()
                .unwrap()
                .1
                .expr_type
                .as_str()
                .unwrap(),
            &"code".to_string()
        );

        let expr = Expr::parse_term(&mut debug_lexer("\"source \" - \"code\" * 1234"))?;
        assert_eq!(
            expr.expr_type
                .as_minus()
                .unwrap()
                .0
                .expr_type
                .as_str()
                .unwrap(),
            &"source ".to_string()
        );
        assert_eq!(
            expr.expr_type
                .as_minus()
                .unwrap()
                .1
                .expr_type
                .as_multiply()
                .unwrap()
                .0
                .expr_type
                .as_str()
                .unwrap(),
            &"code".to_string()
        );
        assert_eq!(
            expr.expr_type
                .as_minus()
                .unwrap()
                .1
                .expr_type
                .as_multiply()
                .unwrap()
                .1
                .expr_type
                .as_num()
                .unwrap(),
            &1234.
        );

        Expr::parse_term(&mut debug_lexer("\"source \" + ")).expect_err("Expected to err");
        

        Expr::parse_term(&mut debug_lexer("\"source \" - -")).expect_err("Expected to err");

        Ok(())
    }

    #[test]
    fn test_parse_fun_call() -> Result<(), Box<dyn std::error::Error>> {
        let mut function = debug_lexer("f()");
        let mut function_1_arg = debug_lexer("f(a)");
        let mut function_n_arg = debug_lexer("f(a,b,c,d)");
        let mut function_unclosed = debug_lexer("f(");
        let mut function_unfinished_list = debug_lexer("f(a,");

        let expr = Expr::parse_fun_call(&mut function)?;
        assert_eq!(
            expr.expr_type
                .as_fun_call()
                .unwrap()
                .fun
                .expr_type
                .as_var()
                .unwrap(),
            &"f".to_string()
        );
        assert_eq!(
            expr.expr_type
                .as_fun_call()
                .unwrap()
                .args
                .len(),
            0
        );

        let expr = Expr::parse_fun_call(&mut function_1_arg)?;
        assert_eq!(
            expr.expr_type
                .as_fun_call()
                .unwrap()
                .fun
                .expr_type
                .as_var()
                .unwrap(),
            &"f".to_string()
        );
        assert_eq!(
            expr.expr_type
                .as_fun_call()
                .unwrap()
                .args
                .len(),
            1
        );
        assert_eq!(
            expr.expr_type
                .as_fun_call()
                .unwrap()
                .args[0]
                .expr_type
                .as_var()
                .unwrap(),
            &"a".to_string()
        );

        let expr = Expr::parse_fun_call(&mut function_n_arg)?;
        assert_eq!(
            expr.expr_type
                .as_fun_call()
                .unwrap()
                .fun
                .expr_type
                .as_var()
                .unwrap(),
            &"f".to_string()
        );
        assert_eq!(
            expr.expr_type
                .as_fun_call()
                .unwrap()
                .args
                .len(),
            4
        );
        assert_eq!(
            expr.expr_type
                .as_fun_call()
                .unwrap()
                .args[0]
                .expr_type
                .as_var()
                .unwrap(),
            &"a".to_string()
        );
        assert_eq!(
            expr.expr_type
                .as_fun_call()
                .unwrap()
                .args[1]
                .expr_type
                .as_var()
                .unwrap(),
            &"b".to_string()
        );
        assert_eq!(
            expr.expr_type
                .as_fun_call()
                .unwrap()
                .args[2]
                .expr_type
                .as_var()
                .unwrap(),
            &"c".to_string()
        );
        assert_eq!(
            expr.expr_type
                .as_fun_call()
                .unwrap()
                .args[3]
                .expr_type
                .as_var()
                .unwrap(),
            &"d".to_string()
        );

        Expr::parse_fun_call(&mut function_unclosed).expect_err("Expect to err if function is unclosed");
        Expr::parse_fun_call(&mut function_unfinished_list).expect_err("Expect to err if function argument list is incomplete");

        Ok(())
    }

    #[test]
    fn test_parse_assignment() -> Result<(), Box<dyn std::error::Error>> {
        let expr = Expr::parse_expr(&mut debug_lexer("asdf = 420.69"))?;
        assert_eq!(
            expr.expr_type
                .as_assignment()
                .unwrap()
                .0
                .expr_type
                .as_var()
                .unwrap(),
            &"asdf".to_string()
        );

        Expr::parse_assignment(&mut debug_lexer("55 = 420.69")).expect_err("We should inform the user at parsing time when they try and assign to anything other than a variable");
        
        Ok(())
    }

}
