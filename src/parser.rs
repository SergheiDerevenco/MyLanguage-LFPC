use std::fmt;
use crate::lexer::{Lexer, Token};
use core::mem;


#[derive(PartialEq, Clone, Debug)]
pub struct Ident(pub String);

#[derive(PartialEq, Clone, Debug)]
pub enum Infix {
    Plus,
    Minus,
    Divide,
    Multiply,
    Equal,
    NotEqual,
    GreaterThanEqual,
    GreaterThan,
    LessThanEqual,
    LessThan,
}

impl fmt::Display for Infix {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Infix::Plus => write!(f, "+"),
            Infix::Minus => write!(f, "-"),
            Infix::Divide => write!(f, "/"),
            Infix::Multiply => write!(f, "*"),
            Infix::Equal => write!(f, "=="),
            Infix::NotEqual => write!(f, "!="),
            Infix::GreaterThanEqual => write!(f, ">="),
            Infix::GreaterThan => write!(f, ">"),
            Infix::LessThanEqual => write!(f, "<="),
            Infix::LessThan => write!(f, "<"),
        }
    }
}

#[derive(PartialEq, Clone, Debug)]
pub enum Expr {
    Identifier(Ident),
    Literal(Literal),
    Infix(Infix, Box<Expr>, Box<Expr>),
    Index(Box<Expr>, Box<Expr>),
    If {
        cond: Box<Expr>,
        consequence: BlockStmt,
        alternative: Option<BlockStmt>,
    },
    Func {
        params: Vec<Ident>,
        body: BlockStmt,
    },
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
}

#[derive(PartialEq, Clone, Debug)]
pub enum Literal {
    Int(i64),
    String(String),
    Bool(bool),
    Array(Vec<Expr>),
}

#[derive(PartialEq, Clone, Debug)]
pub enum Stmt {
    Blank,
    Let(Ident, Expr),
    Return(Expr),
    Expr(Expr),
}

pub type BlockStmt = Vec<Stmt>;

pub type Program = BlockStmt;

#[derive(PartialEq, PartialOrd, Debug, Clone)]
pub enum Precedence {
    Lowest,
    Equals,      // ==
    LessGreater, // > or <
    Sum,         // +
    Call,       //my_function(x)
    Product,     // *
    Index,      //array[index]
}

#[derive(Debug, Clone)]
pub enum ParseErrorKind {
    UnexpectedToken,
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            ParseErrorKind::UnexpectedToken => write!(f, "Unexpected Token"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ParseError {
    kind: ParseErrorKind,
    msg: String,
}

impl ParseError {
    fn new(kind: ParseErrorKind, msg: String) -> Self {
        ParseError { kind, msg }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: {}", self.kind, self.msg)
    }
}

pub type ParseErrors = Vec<ParseError>;

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    current_token: Token,
    pub next_token: Token,
    errors: ParseErrors,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        let mut parser = Parser {
            lexer,
            current_token: Token::Illegal,
            next_token: Token::Illegal,
            errors: vec![],
        };

        parser
    }

    fn token_to_precedence(tok: &Token) -> Precedence {
        match tok {
            Token::Equal | Token::NotEqual => Precedence::Equals,
            Token::LessThan | Token::LessThanEqual => Precedence::LessGreater,
            Token::GreaterThan | Token::GreaterThanEqual => Precedence::LessGreater,
            Token::Plus | Token::Minus => Precedence::Sum,
            Token::Slash | Token::Asterisk => Precedence::Product,
            Token::Lbracket => Precedence::Index,
            Token::Lparen => Precedence::Call,
            _ => Precedence::Lowest,
        }
    }

//    fn bump(&mut self) {
//        self.current_token = self.next_token.clone();
//        self.next_token = self.lexer.next_token();
//    }

    pub fn next_token(&mut self) {
        self.current_token = mem::replace(&mut self.next_token, *Box::new(self.lexer.next_token()));
    }

    fn current_token_precedence(&mut self) -> Precedence {
        Self::token_to_precedence(&self.current_token)
    }

    fn next_token_precedence(&mut self) -> Precedence {
        Self::token_to_precedence(&self.next_token)
    }

    fn error_next_token(&mut self, tok: Token) {
        self.errors.push(ParseError::new(
            ParseErrorKind::UnexpectedToken,
            format!(
                "expected next token to be {:?}, got {:?} instead",
                tok, self.next_token
            ),
        ));
    }

    fn error_no_prefix_parser(&mut self) {
        self.errors.push(ParseError::new(
            ParseErrorKind::UnexpectedToken,
            format!(
                "no prefix parse function for  \"{:?}\" found",
                self.current_token,
            ),
        ));
    }

    fn current_token_is(&mut self, tok: Token) -> bool {
        self.current_token == tok
    }

    fn next_token_is(&mut self, tok: &Token) -> bool {
        self.next_token == *tok
    }

    fn expect_next_token(&mut self, tok: Token) -> bool {
        if self.next_token_is(&tok) {
            self.next_token();
            return true;
        } else {
            self.error_next_token(tok);
            return false;
        }
    }

    pub fn parse(&mut self) -> Program {
        let mut program: Program = vec![];

        while !self.current_token_is(Token::Eof) {
            match self.parse_stmt() {
                Some(stmt) => program.push(stmt),
                None => {}
            }
            self.next_token();
        }

        program
    }

    fn parse_ident(&mut self) -> Option<Ident> {
        match self.current_token {
            Token::Identifier(ref mut ident) => Some(Ident(ident.clone())),
            _ => None,
        }
    }

    fn parse_block_stmt(&mut self) -> BlockStmt {
        self.next_token();

        let mut block = vec![];

        while !self.current_token_is(Token::Rbrace) && !self.current_token_is(Token::Eof) {
            match self.parse_stmt() {
                Some(stmt) => block.push(stmt),
                None => {}
            }
            self.next_token();
        }

        block
    }

    fn parse_stmt(&mut self) -> Option<Stmt> {
        match self.current_token {
            Token::Let => self.parse_let_stmt(),
            Token::Return => self.parse_return_stmt(),
            Token::Blank => Some(Stmt::Blank),
            _ => self.parse_expr_stmt(),
        }
    }

    fn parse_let_stmt(&mut self) -> Option<Stmt> {
        match &self.next_token {
            Token::Identifier(_) => self.next_token(),
            _ => return None,
        };

        let name = match self.parse_ident() {
            Some(name) => name,
            None => return None,
        };

        if !self.expect_next_token(Token::Assign) {
            return None;
        }

        self.next_token();

        let expr = match self.parse_expr(Precedence::Lowest) {
            Some(expr) => expr,
            None => return None,
        };

        if self.next_token_is(&Token::Semicolon) {
            self.next_token();
        }

        Some(Stmt::Let(name, expr))
    }

    fn parse_return_stmt(&mut self) -> Option<Stmt> {
        self.next_token();

        let expr = match self.parse_expr(Precedence::Lowest) {
            Some(expr) => expr,
            None => return None,
        };

        if self.next_token_is(&Token::Semicolon) {
            self.next_token();
        }

        Some(Stmt::Return(expr))
    }

    fn parse_expr_stmt(&mut self) -> Option<Stmt> {
        match self.parse_expr(Precedence::Lowest) {
            Some(expr) => {
                if self.next_token_is(&Token::Semicolon) {
                    self.next_token();
                }
                Some(Stmt::Expr(expr))
            }
            None => None,
        }
    }

    fn parse_expr(&mut self, precedence: Precedence) -> Option<Expr> {
        // prefix
        let mut left = match self.current_token {
            Token::Identifier(_) => self.parse_ident_expr(),
            Token::Int(_) => self.parse_int_expr(),
            Token::String(_) => self.parse_string_expr(),
            Token::And | Token::False => self.parse_bool_expr(),
            Token::Lbracket => self.parse_array_expr(),
            Token::If => self.parse_if_expr(),
            Token::Function => self.parse_func_expr(),
            _ => {
                self.error_no_prefix_parser();
                return None;
            }
        };

        // infix
        while !self.next_token_is(&Token::Semicolon) && precedence < self.next_token_precedence() {
            match self.next_token {
                Token::Plus
                | Token::Minus
                | Token::Slash
                | Token::Asterisk
                | Token::Equal
                | Token::NotEqual
                | Token::LessThan
                | Token::LessThanEqual
                | Token::GreaterThan
                | Token::GreaterThanEqual => {
                    self.next_token();
                    left = self.parse_infix_expr(left.unwrap());
                }
                Token::Lbracket => {
                    self.next_token();
                    left = self.parse_index_expr(left.unwrap());
                }
                Token::Lparen => {
                    self.next_token();
                    left = self.parse_call_expr(left.unwrap());
                }
                _ => return left,
            }
        }

        left
    }

    fn parse_ident_expr(&mut self) -> Option<Expr> {
        match self.parse_ident() {
            Some(ident) => Some(Expr::Identifier(ident)),
            None => None,
        }
    }

    fn parse_int_expr(&mut self) -> Option<Expr> {
        match self.current_token {
            Token::Int(ref mut int) => Some(Expr::Literal(Literal::Int(int.clone()))),
            _ => None,
        }
    }

    fn parse_string_expr(&mut self) -> Option<Expr> {
        match self.current_token {
            Token::String(ref mut s) => Some(Expr::Literal(Literal::String(s.clone()))),
            _ => None,
        }
    }

    fn parse_bool_expr(&mut self) -> Option<Expr> {
        match self.current_token {
            Token::True => Some(Expr::Literal(Literal::Bool(true))),
            Token::False => Some(Expr::Literal(Literal::Bool(false))),
            _ => None,
        }
    }

    fn parse_expr_list(&mut self, end: Token) -> Option<Vec<Expr>> {
        let mut list = vec![];

        if self.next_token_is(&end) {
            self.next_token();
            return Some(list);
        }

        self.next_token();

        match self.parse_expr(Precedence::Lowest) {
            Some(expr) => list.push(expr),
            None => return None,
        }

        while self.next_token_is(&Token::Comma) {
            self.next_token();
            self.next_token();

            match self.parse_expr(Precedence::Lowest) {
                Some(expr) => list.push(expr),
                None => return None,
            }
        }

        if !self.expect_next_token(end) {
            return None;
        }

        Some(list)
    }

    fn parse_array_expr(&mut self) -> Option<Expr> {
        match self.parse_expr_list(Token::Rbracket) {
            Some(list) => Some(Expr::Literal(Literal::Array(list))),
            None => None,
        }
    }

    fn parse_func_params(&mut self) -> Option<Vec<Ident>> {
        let mut params = vec![];

        if self.expect_next_token(Token::Rparen) {
            self.next_token();
            return Some(params);
        }

        self.next_token();

        match self.parse_ident() {
            Some(ident) => params.push(ident),
            None => return None,
        };

        while self.expect_next_token(Token::Comma) {
            self.next_token();
            self.next_token();

            match self.parse_ident() {
                Some(ident) => params.push(ident),
                None => return None,
            };
        }

        if !self.expect_next_token(Token::Rparen) {
            return None;
        }

        Some(params)
    }

    fn parse_func_expr(&mut self) -> Option<Expr> {
        if !self.expect_next_token(Token::Lparen) {
            return None;
        }

        let params = match self.parse_func_params() {
            Some(params) => params,
            None => return None,
        };

        if !self.expect_next_token(Token::Lbrace) {
            return None;
        }

        Some(Expr::Func {
            params,
            body: self.parse_block_stmt(),
        })
    }

    fn parse_if_expr(&mut self) -> Option<Expr> {
        if !self.expect_next_token(Token::Lparen) {
            return None;
        }

        self.next_token();

        let cond = match self.parse_expr(Precedence::Lowest) {
            Some(expr) => expr,
            None => return None,
        };

        if !self.expect_next_token(Token::Rparen) || !self.expect_next_token(Token::Lbrace) {
            return None;
        }

        let consequence = self.parse_block_stmt();
        let mut alternative = None;

        if self.next_token_is(&Token::Else) {
            self.next_token();

            if !self.expect_next_token(Token::Lbrace) {
                return None;
            }

            alternative = Some(self.parse_block_stmt());
        }

        Some(Expr::If {
            cond: Box::new(cond),
            consequence,
            alternative,
        })
    }

    fn parse_call_expr(&mut self, func: Expr) -> Option<Expr> {
        let args = match self.parse_expr_list(Token::Rparen) {
            Some(args) => args,
            None => return None,
        };

        Some(Expr::Call {
            func: Box::new(func),
            args,
        })
    }

    fn parse_infix_expr(&mut self, left: Expr) -> Option<Expr> {
        let infix = match self.current_token {
            Token::Plus => Infix::Plus,
            Token::Minus => Infix::Minus,
            Token::Slash => Infix::Divide,
            Token::Asterisk => Infix::Multiply,
            Token::Equal => Infix::Equal,
            Token::NotEqual => Infix::NotEqual,
            Token::LessThan => Infix::LessThan,
            Token::LessThanEqual => Infix::LessThanEqual,
            Token::GreaterThan => Infix::GreaterThan,
            Token::GreaterThanEqual => Infix::GreaterThanEqual,
            _ => return None,
        };

        let precedence = self.current_token_precedence();

        self.next_token();

        match self.parse_expr(precedence) {
            Some(expr) => Some(Expr::Infix(infix, Box::new(left), Box::new(expr))),
            None => None,
        }
    }

    fn parse_index_expr(&mut self, left: Expr) -> Option<Expr> {
        self.next_token();

        let index = match self.parse_expr(Precedence::Lowest) {
            Some(expr) => expr,
            None => return None,
        };

        if !self.expect_next_token(Token::Rbracket) {
            return None;
        }

        Some(Expr::Index(Box::new(left), Box::new(index)))
    }
}





