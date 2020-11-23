
#![allow(dead_code)]

mod parser_utils;
mod parser_model;
mod parser;
mod serializer;

use parser::parse;

fn main() {
    println!("{:?}", parse("1 + 2"));
}
