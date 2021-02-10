
use std::{hash::Hash, collections::HashMap};

#[derive(Debug,Clone,PartialEq,PartialOrd,Hash)]
pub struct PathSegment {
    pub optional: bool,
    pub property: AST,
}

impl Eq for PathSegment { }

#[derive(Debug,Clone,PartialEq,PartialOrd,Hash)]
pub enum DeclarationKind {
    Var,
    Let,
    Const,
}

impl DeclarationKind {
    pub fn from_keyword(s: &str) -> Self {
        match s {
            "const" => DeclarationKind::Const,
            "let" => DeclarationKind::Let,
            "var" => DeclarationKind::Var,
            _ => panic!("Cannot derive a DeclarationKind from string '{}'", s),
        }
    }
    pub fn to_keyword(&self) -> &'static str {
        match self {
            DeclarationKind::Var => "var",
            DeclarationKind::Let => "let",
            DeclarationKind::Const => "const",
        }
    }
}

impl Eq for DeclarationKind { }

#[derive(Debug,Clone,PartialEq,Hash)]
pub enum OperatorSide {
    Left,
    Right
}

#[derive(Debug,Clone,PartialEq)]
pub struct ClassProperty {
    pub getter: Option<Box<AST>>,
    pub setter: Option<Box<AST>>,
}

#[derive(Debug,Clone,PartialEq)]
pub enum AST {
    Undefined,
    Null,
    BooleanLiteral(bool),
    NumberLiteral(String),
    StringLiteral(String),
    ArrayLiteral(Vec<AST>),
    ObjectLiteral(HashMap<AST,AST>),
    Function { name: Option<Box<AST>>, args: Vec<AST>, body: Box<AST>, is_arrow_function: bool },

    FunctionCall { func: Box<AST>, args: Vec<AST> },
    Identifier(String),
    Indexer(Box<AST>),
    PropertyPath(Vec<PathSegment>),
    Block(Vec<AST>),
    Class {
        name: Box<AST>,
        constructor: Option<Box<AST>>,
        fields: Vec<AST>,
        methods: Vec<AST>,
        properties: HashMap<AST, ClassProperty>,
    },
    ClassField { identifier: Box<AST>, expression: Option<Box<AST>> },
    Conditional { condition: Box<AST>, if_body: Box<AST>, else_body: Option<Box<AST>> },
    WhileLoop { condition: Box<AST>, body: Box<AST> },
    UnaryOperation { operator: &'static str, expr: Box<AST>, side: OperatorSide },
    BinaryOperation { operator: &'static str, left: Box<AST>, right: Box<AST> },
    VariableDeclaration { kind: DeclarationKind, identifier: Box<AST>, expression: Option<Box<AST>> },
    ReturnStatement(Option<Box<AST>>),
    Parenthesized(Box<AST>),
}

impl PartialOrd for AST {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AST {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        format!("{:?}", self).cmp(&format!("{:?}", other))
    }
}

impl Hash for AST {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            AST::ObjectLiteral(x) => {
                "AST::Object".hash(state);
                let mut keys: Vec<&AST> = x.keys().collect();
                keys.sort();

                for key in keys {
                    key.hash(state);
                    x.get(key).hash(state);
                }
            },


            AST::Undefined => "AST::Undefined".hash(state),
            AST::Null => "AST::Null".hash(state),
            AST::BooleanLiteral(x) => {
                "AST::Boolean".hash(state);
                x.hash(state);
            },
            AST::NumberLiteral(x) => {
                "AST::Number".hash(state);
                x.hash(state);
            },
            AST::StringLiteral(x) => {
                "AST::String".hash(state);
                x.hash(state);
            },
            AST::ArrayLiteral(x) => {
                "AST::Array".hash(state);
                x.hash(state);
            },
            AST::Function { name, args, body, is_arrow_function } => {
                "AST::Function".hash(state);
                name.hash(state);
                args.hash(state);
                body.hash(state);
                is_arrow_function.hash(state);
            },
            AST::FunctionCall { func, args } => {
                "AST::FunctionCall".hash(state);
                func.hash(state);
                args.hash(state);
            },
            AST::Identifier(x) => {
                "AST::Identifier".hash(state);
                x.hash(state);
            },
            AST::Indexer(x) => {
                "AST::Indexer".hash(state);
                x.hash(state);
            },
            AST::PropertyPath(x) => {
                "AST::PropertyPath".hash(state);
                x.hash(state);
            },
            AST::Block(x) => {
                "AST::Block".hash(state);
                x.hash(state);
            },
            AST::Conditional { condition: if_condition, if_body, else_body } => {
                "AST::Conditional".hash(state);
                if_condition.hash(state);
                if_body.hash(state);
                else_body.hash(state);
            },
            AST::WhileLoop { condition, body } => {
                "AST::WhileLoop".hash(state);
                condition.hash(state);
                body.hash(state);
            },
            AST::BinaryOperation { operator, left, right } => {
                "AST::BinaryOperation".hash(state);
                operator.hash(state);
                left.hash(state);
                right.hash(state);
            },
            AST::UnaryOperation { operator, expr, side } => {
                "AST::UnaryOperation".hash(state);
                operator.hash(state);
                expr.hash(state);
                side.hash(state);
            },
            AST::VariableDeclaration { kind, identifier, expression } => {
                "AST::VariableDeclaration".hash(state);
                kind.hash(state);
                identifier.hash(state);
                expression.hash(state);
            },
            AST::ReturnStatement(x) => {
                "AST::ReturnStatement".hash(state);
                x.hash(state);
            },
            AST::Parenthesized(x) => {
                "AST::ReturnStatement".hash(state);
                x.hash(state);
            },
            AST::Class { name, constructor, fields, methods, properties } => {
                "AST::Class".hash(state);
                name.hash(state);
                constructor.hash(state);
                fields.hash(state);
                methods.hash(state);
                // properties.hash(state); TODO
            },
            AST::ClassField { identifier, expression } => {
                "AST::ClassField".hash(state);
                identifier.hash(state);
                expression.hash(state);
            },
        }
    }
}

impl Eq for AST { }
