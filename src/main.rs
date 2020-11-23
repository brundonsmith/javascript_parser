
#![allow(dead_code)]

mod parser_utils;
mod parser_model;
mod parser;

use parser::parse;

fn main() {
    println!("{:?}", parse("1 + 2"));
}
