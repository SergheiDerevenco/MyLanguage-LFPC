mod lexer;
mod parser;
use lexer::Token;
use crate::lexer::Lexer;
use std::fs::File;
use std::io::{BufRead, BufReader};
use crate::parser::Parser;


fn main() {
    let file = File::open("program.txt").unwrap();

    let reader = BufReader::new(file);

    for val in reader.lines() {
        let mut line = val.unwrap();
        let mut lexer = Lexer::new(&mut line);
        let mut parser = Parser::new(lexer);

        let tok = parser.parse();
        println!("{:?}", tok);
//        loop {
//            let tok = parser.next_token();
//            println!("{:?}", tok);
//            if tok == Token::Eof {
//                break;
//            }
//        }
    }
}