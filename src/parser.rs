
use crate::parser_model::AST;
use crate::parser_utils::ParseError;

const KEYWORDS: [&str;63] = ["abstract", "arguments", "boolean", "break", 
"byte", "case", "catch", "char", "const", "continue", "debugger", "default", 
"delete", "do", "double", "else", "eval", "false", "final", "finally", "float", 
"for", "function", "goto", "if", "implements", "in", "instanceof", "int", 
"interface", "let", "long", "native", "new", "null", "package", "private", 
"protected", "public", "return", "short", "static", "switch", "synchronized", 
"this", "throw", "throws", "transient", "true", "try", "typeof", "var", "void", 
"volatile", "while", "with", "yield", "class", "enum", "export", "extends", 
"import", "super"];


pub fn parse(code: &str) -> Result<AST, ParseError> {
    let mut index = 0;
    let mut file_block: Vec<AST> = Vec::new();

    while index < code.len() {
        file_block.push(parse::statement_or_expression(code, &mut index)?);
    }

    return Ok(AST::Block(file_block));
}

mod parse {
    use crate::{parser_model::AST, parser_utils::{ParseError, try_eat, try_eat_while}};

    use super::KEYWORDS;

    pub fn statement_or_expression(code: &str, index: &mut usize) -> Result<AST, ParseError> {
        let res = statement::statement(code, index)
            .or_else(|_| expression::expression(code, index));

        try_eat(code, index, ";").ok();

        return res;
    }

    mod statement {
        use crate::{parser_model::{AST, DeclarationKind}, parser_utils::{ParseError, try_eat}};
        use super::{expression::expression, identifier, statement_or_expression};

        pub fn statement(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            declaration(code, index)
                .or_else(|_| conditional(code, index))
                .or_else(|_| while_loop(code, index))
                .or_else(|_| block(code, index))
                .or_else(|_| return_statement(code, index))
                // .or_else(|_| for_loop(code, index))
        }

        fn declaration(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            let declaration_kind = try_eat(code, index, "const")
                .or_else(|_| try_eat(code, index, "let"))
                .or_else(|_| try_eat(code, index, "var"))
                .map(DeclarationKind::from_keyword);
    
            if let Ok(kind) = declaration_kind {
                let i = identifier(code, index)?;
                let identifier = Box::new(i);
                
                if try_eat(code, index, "=").is_ok() {
                    let expression = Some(Box::new(expression(code, index)?));
    
                    return Ok(AST::VariableDeclaration { kind, identifier, expression });
                }
    
                return Ok(AST::VariableDeclaration { kind, identifier, expression: None });
            } else {
                return Err(ParseError::new(code, *index, "Expected declaration"));
            }
        }
    
        fn conditional(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            if try_eat(code, index, "if").is_ok() {
                try_eat(code, index, "(")?;
                let if_condition = Box::new(expression(code, index)?);
                try_eat(code, index, ")")?;

                let if_body = Box::new(statement_or_expression(code, index)?);

                if try_eat(code, index, "else").is_ok() {
                    let else_body = Some(Box::new(statement_or_expression(code, index)?));
                    return Ok(AST::Conditional { condition: if_condition, if_body, else_body });
                }

                return Ok(AST::Conditional { condition: if_condition, if_body, else_body: None });
            }
    
            Err(ParseError::new(code, *index, "Expected return statement"))
        }
    
        fn while_loop(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            if try_eat(code, index, "while").is_ok() {
                try_eat(code, index, "(")?;
                let condition = Box::new(expression(code, index)?);
                try_eat(code, index, ")")?;

                let body = Box::new(statement_or_expression(code, index)?);

                return Ok(AST::WhileLoop { condition, body });
            }
    
            Err(ParseError::new(code, *index, "Expected return statement"))
        }
    
        // fn for_loop(code: &str, index: &mut usize) -> Result<AST, ParseError> {
        //     if try_eat(code, index, "for").is_ok() {
        //         try_eat(code, index, "(")?;
        //         let condition = Box::new(expression(code, index)?);
        //         try_eat(code, index, ")")?;

        //         let body = Box::new(statement_or_expression(code, index)?);

        //         return Ok(AST::WhileLoop { condition, body });
        //     }
    
        //     Err(ParseError::new(code, *index, "Expected return statement"))
        // }

        fn block(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            try_eat(code, index, "{")?;
            let mut statements = Vec::new();
            while let Ok(statement) = statement_or_expression(code, index) {
                statements.push(statement);
            }
            try_eat(code, index, "}")?;

            return Ok(AST::Block(statements));
        }

        fn return_statement(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            // TODO: only allow return in proper contexts?
            if try_eat(code, index, "return").is_ok() {
                let expression = expression(code, index).ok().map(Box::new);
    
                return Ok(AST::ReturnStatement(expression));
            }
    
            Err(ParseError::new(code, *index, "Expected return statement"))
        }
    }

    mod expression {
        use std::collections::HashMap;

        use crate::{parser_model::{AST, OperatorSide, PathSegment}, parser_utils::{ParseError, try_eat, try_eat_while}};
        use super::{identifier, indexer, statement_or_expression};

        pub fn expression(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            let expr = arrow_function(code, index) // arrow_function() has to go before parenthesized()
                .or_else(|_| operation(code, index, OPERATOR_TIERS.len() - 1));

            // function call
            if let Ok(expr) = expr {
                if try_eat(code, index, "(").is_ok() {
                    let mut args = vec![];

                    let first_arg = expression(code, index);

                    if let Ok(first_arg) = first_arg {
                        args.push(first_arg);

                        while try_eat(code, index, ",").is_ok() {
                            let arg = expression(code, index)?;
                            args.push(arg);
                        }
    
                        try_eat(code, index, ",").ok();
                    }
                    
                    try_eat(code, index, ")")?;

                    return Ok(AST::FunctionCall {
                        func: Box::new(expr),
                        args,
                    })
                }

                return Ok(expr);
            } else {
                return expr;
            }
        }

        fn operation(code: &str, index: &mut usize, operator_tier: usize) -> Result<AST, ParseError> {
            let tier: &OperatorTier = &OPERATOR_TIERS[operator_tier];

            let try_eat_operator = |code: &str, index: &mut usize| {
                tier.operators.iter()
                    .map(|op| try_eat(code, index, op))
                    .filter_map(Result::ok)
                    .next()
            };

            let parse_next_level = |code: &str, index: &mut usize| {                
                if operator_tier > 0 {
                    operation(code, index, operator_tier - 1)
                } else {
                    parenthesized(code, index)
                        .or_else(|_| primary(code, index))
                }
            };

            if tier.operator_postion == OperatorPosition::UnaryLeft {
                // look for operator first
                let operator = try_eat_operator(code, index);
                let expr = parse_next_level(code, index)?;

                if let Some(operator) = operator {
                    return Ok(AST::UnaryOperation { operator, expr: Box::new(expr), side: OperatorSide::Left });
                } else {
                    return Ok(expr)
                }
            } else {
                // look for leftmost expression first
                let mut expr = parse_next_level(code, index)?;
                let index_before_operator = *index;

                if tier.operator_postion == OperatorPosition::UnaryRight {
                    if let Some(operator) = try_eat_operator(code, index) {
                        return Ok(AST::UnaryOperation { operator, expr: Box::new(expr), side: OperatorSide::Right });
                    }

                    return Ok(expr);
                } else {
                    while let Some(operator) = try_eat_operator(code, index) { // binary
                        if let Some(right) = parse_next_level(code, index).ok() {
                            if tier.associativity == Associativity::LeftToRight {
                                expr = AST::BinaryOperation { operator, left: Box::new(expr), right: Box::new(right) };
                            } else {
                                if let AST::BinaryOperation { operator: expr_operator, left: expr_left, right: expr_right } = expr {
                                    let new_right = AST::BinaryOperation { operator, left: expr_right, right: Box::new(right) };
                                    expr = AST::BinaryOperation { operator: expr_operator, left: expr_left, right: Box::new(new_right) };
                                } else {
                                    expr = AST::BinaryOperation { operator, left: Box::new(expr), right: Box::new(right) };
                                }
                            }
                        } else {
                            // If we match an operator but fail to match an 
                            // expression on the right, backtrack to before
                            // the operator and continue. This covers situations
                            // like a += b, where a + _ will be tried first.
                            *index = index_before_operator;
                            return Ok(expr);
                        }
                    }

                    return Ok(expr);
                }

            }
        }
    
        fn parenthesized(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            try_eat(code, index, "(")?;

            let expr = expression(code, index)?;

            try_eat(code, index, ")")?;

            Ok(AST::Parenthesized(Box::new(expr)))
        }

        fn primary(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            number(code, index)
                .or_else(|_| function(code, index))
                .or_else(|_| boolean(code, index))
                .or_else(|_| string(code, index))
                .or_else(|_| null(code, index))
                .or_else(|_| undefined(code, index))
                .or_else(|_| identifier_or_path(code, index))
                .or_else(|_| array(code, index))
                .or_else(|_| object(code, index))
                .map_err(|ParseError { msg: _, line, column }| ParseError {
                    msg: String::from("Expected atom"),
                    line,
                    column
                })
        }
    
        fn function(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            if try_eat(code, index, "function").is_ok() {
                let name = identifier(code, index).ok().map(Box::new);
    
                try_eat(code, index, "(")?;
                let args = _function_args(code, index)?;
                try_eat(code, index, ")")?;
    
                try_eat(code, index, "{")?;
                let mut body_statements = Vec::new();
                while let Ok(arg_name) = statement_or_expression(code, index) {
                    body_statements.push(arg_name);
                }
                let body = Box::new(AST::Block(body_statements));
                try_eat(code, index, "}")?;
    
                return Ok(AST::Function { name, args, body, is_arrow_function: false });
            }
    
            Err(ParseError::new(code, *index, "Expected function"))
        }
    
        fn arrow_function(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            let original_index = *index;

            let args = _arrow_function_args_and_arrow(code, index);

            match args {
                Ok(args) => {
                    let body = Box::new(statement_or_expression(code, index)?);

                    Ok(AST::Function {
                        name: None,
                        args,
                        body,
                        is_arrow_function: true,
                    })
                },
                Err(e) => {
                    *index = original_index;
                    Err(ParseError::new(code, *index, "Expected arrow function"))
                },
            }
        }

        fn _arrow_function_args_and_arrow(code: &str, index: &mut usize) -> Result<Vec<AST>, ParseError> {
            if let Ok(arg) = identifier(code, index) {
                if try_eat(code, index, "=>").is_ok() {
                    return Ok(vec![ arg ]);
                }
            } else if try_eat(code, index, "(").is_ok() {
                let args = _function_args(code, index)?;
                try_eat(code, index, ")")?;

                if try_eat(code, index, "=>").is_ok() {
                    return Ok(args);
                }
            }

            Err(ParseError::new(code, *index, "Expected arrow function"))
        }

        fn _function_args(code: &str, index: &mut usize) -> Result<Vec<AST>, ParseError> {
            let mut args = Vec::new();

            // TODO: Rest parameters and default arg values
            while let Ok(arg_name) = identifier(code, index) {
                args.push(arg_name);
                try_eat(code, index, ",").ok();
            }

            return Ok(args);
        }
    
        fn undefined(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            if try_eat(code, index, "undefined").is_ok() {
                return Ok(AST::Undefined);
            }
    
            Err(ParseError::new(code, *index, "Expected undefined"))
        }
    
        fn null(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            if try_eat(code, index, "null").is_ok() {
                return Ok(AST::Null);
            }
    
            Err(ParseError::new(code, *index, "Expected null"))
        }
    
        fn boolean(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            if try_eat(code, index, "true").is_ok() {
                return Ok(AST::BooleanLiteral(true));
            }
    
            if try_eat(code, index, "false").is_ok() {
                return Ok(AST::BooleanLiteral(false));
            }
    
            Err(ParseError::new(code, *index, "Expected boolean"))
        }
    
        fn string(code: &str, index: &mut usize) -> Result<AST, ParseError> {
    
            let quote_type = try_eat(code, index, "\"")
                .or_else(|_| try_eat(code, index, "'"))
                .or_else(|_| try_eat(code, index, "`"))
                .map(|s| s.chars().next().unwrap())?;
    
            let string_contents_start = *index;
            
            let mut escape_next = false;
            for (i, c) in code[string_contents_start..].char_indices() {
                if !escape_next {
                    if c == '\\' {
                        escape_next = true;
                    } else if c == quote_type {
                        *index = string_contents_start + i + 1;

                        return Ok(AST::StringLiteral(String::from(&code[string_contents_start - 1..*index])));
                    }
                } else {
                    escape_next = false;
                }
            }
    
            return Err(ParseError::new(code, *index, "Expected string"));
        }
    
        fn number(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            // TODO: non-decimal bases

            let sign = try_eat(code, index, "-").ok();
            let front = try_eat_while(code, index, |ch| ch.is_numeric())?;

            let mut result = String::with_capacity(front.len());
            if let Some(sign) = sign {
                result.push_str(sign);
            }
            result.push_str(front);

            let decimal = try_eat(code, index, ".").ok();
            if let Some(decimal) = decimal {
                result.push_str(decimal);
                let rest = try_eat_while(code, index, |ch| ch.is_numeric())?;
                result.push_str(rest);
            }

            return Ok(AST::NumberLiteral(result));
        }

        fn array(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            try_eat(code, index, "[")?;
            let mut members = Vec::new();
            while let Ok(arg_name) = expression(code, index) {
                members.push(arg_name);
                try_eat(code, index, ",").ok();
            }
            try_eat(code, index, "]")?;

            return Ok(AST::ArrayLiteral(members));
        }

        fn object(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            try_eat(code, index, "{")?;
            let mut contents = HashMap::new();
            while let Ok(key) = _object_key(code, index) {
                try_eat(code, index, ":")?;
                let value = expression(code, index)?;
                contents.insert(key, value);
                try_eat(code, index, ",").ok();
            }
            try_eat(code, index, "}")?;

            return Ok(AST::ObjectLiteral(contents));
        }

        fn _object_key(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            identifier(code, index)
                .or_else(|_| string(code, index))
                .or_else(|_| indexer(code, index))
        }

        fn identifier_or_path(code: &str, index: &mut usize) -> Result<AST, ParseError> {
            let first = identifier(code, index)?;

            if try_eat(code, index, ".").is_ok() {
                // TODO: Optionals and array indexing

                let second = identifier(code, index)?;

                let mut path = vec![
                    PathSegment::Property { property: first, optional: false },
                    PathSegment::Property { property: second, optional: false },
                ];
                
                while try_eat(code, index, ".").is_ok() {
                    path.push(PathSegment::Property {
                        property: identifier(code, index)?,
                        optional: false
                    });
                }

                Ok(AST::PropertyPath(path))
            } else {
                Ok(first)
            }
        }

        const OPERATOR_TIERS: [OperatorTier;16] = [
            OperatorTier {
                operator_postion: OperatorPosition::UnaryRight,
                associativity: Associativity::RightToLeft,
                operators: &["++", "--"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::UnaryLeft,
                associativity: Associativity::RightToLeft,
                operators: &["!", "~", "++", "--", "+", "-", "typeof", "void", "delete", "await"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::RightToLeft,
                operators: &["**"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::LeftToRight,
                operators: &["*", "/", "%"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::LeftToRight,
                operators: &["+", "-"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::LeftToRight,
                operators: &["<<", ">>", ">>>"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::LeftToRight,
                operators: &["<=", "<", ">=", ">", "in", "instanceof"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::LeftToRight,
                operators: &["===", "==", "!==", "!="],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::LeftToRight,
                operators: &["&"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::LeftToRight,
                operators: &["^"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::LeftToRight,
                operators: &["|"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::LeftToRight,
                operators: &["&&"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::LeftToRight,
                operators: &["||"],
            },
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::LeftToRight,
                operators: &["??"],
            },
            // TODO: Ternary goes here
            OperatorTier {
                operator_postion: OperatorPosition::Binary,
                associativity: Associativity::RightToLeft,
                operators: &["=", "+=", "-=", "**=", "*=", "/=", "%=", "<<=", ">>=", 
                ">>>=", "&=", "^=", "|=", "&&=", "||=", "??="],
            },
            OperatorTier {
                operator_postion: OperatorPosition::UnaryLeft,
                associativity: Associativity::RightToLeft,
                operators: &["yield*", "yield"],
            },
        ];

        #[derive(Debug,Clone,PartialEq)]
        enum OperatorPosition {
            Binary,
            UnaryLeft,
            UnaryRight,
        }

        #[derive(Debug,Clone,PartialEq)]
        enum Associativity {
            LeftToRight,
            RightToLeft,
        }

        #[derive(Debug,Clone,PartialEq)]
        struct OperatorTier<'a> {
            pub operator_postion: OperatorPosition,
            pub associativity: Associativity,
            pub operators: &'a [&'a str],
        }
    }

    fn indexer(code: &str, index: &mut usize) -> Result<AST, ParseError> {
        try_eat(code, index, "[")?;
        let i = Box::new(expression::expression(code, index)?);
        try_eat(code, index, "]")?;

        return Ok(AST::Indexer(i));
    }

    fn identifier(code: &str, index: &mut usize) -> Result<AST, ParseError> {

        // first character(s) of the identifier has stricter constraints than
        // the rest of the identifier
        let front = try_eat_while(code, index, valid_identifier_start_char);

        let ident = front
            .map(|front| (
                front,
                try_eat_while(code, index, valid_identifier_char).ok()
            ))
            .map(|(front, rest)| {
                let mut s = String::from(front);

                if let Some(rest) = rest {
                    s += rest;
                }

                AST::Identifier(s)
            });
        
        // keywords are not valid identifiers
        if let Ok(AST::Identifier(ident)) = &ident {
            if KEYWORDS.iter().any(|k| ident == *k) {
                return Err(ParseError::new(code, *index, format!("'{}' is not a valid identifier, because it is a reserved keyword", ident)));
            }
        }

        return ident;
    }

    fn valid_identifier_start_char(ch: char) -> bool {
        ch.is_alphabetic() || ch == '$' || ch == '_'
    }

    fn valid_identifier_char(ch: char) -> bool {
        valid_identifier_start_char(ch) || ch.is_numeric() // TODO: There's more to this
    }
}

// TODO: Skip comments

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use crate::parser_model::{AST, DeclarationKind, PathSegment};

    use super::parse;

    #[test]
    fn test_declaration_1() {
        let code = "const foo = 12;";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::VariableDeclaration {
                    kind: DeclarationKind::Const,
                    identifier: identifierb("foo"),
                    expression: Some(intb(12)),
                }
            ])
        ))
    }

    #[test]
    fn test_declaration_2() {
        let code = "let _bar = false";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::VariableDeclaration {
                    kind: DeclarationKind::Let,
                    identifier: identifierb("_bar"),
                    expression: Some(Box::new(AST::BooleanLiteral(false))),
                }
            ])
        ))
    }

    #[test]
    fn test_declaration_3() {
        let code = "let _123 = \"hello\";";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::VariableDeclaration {
                    kind: DeclarationKind::Let,
                    identifier: identifierb("_123"),
                    expression: Some(stringb("\"hello\"")),
                }
            ])
        ))
    }

    #[test]
    fn test_declaration_4() {
        let code = "let thing;";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::VariableDeclaration {
                    kind: DeclarationKind::Let,
                    identifier: identifierb("thing"),
                    expression: None,
                }
            ])
        ))
    }

    #[test]
    fn test_operator_1() {
        let code = "1 + 2";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::BinaryOperation {
                    operator: "+",
                    left: intb(1),
                    right: intb(2),
                }
            ])
        ))
    }

    #[test]
    fn test_operator_2() {
        let code = "1 + 3 * 2";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::BinaryOperation {
                    operator: "+",
                    left: intb(1),
                    right: Box::new(AST::BinaryOperation {
                        operator: "*",
                        left: intb(3),
                        right: intb(2),
                    }),
                }
            ])
        ))
    }

    #[test]
    fn test_operator_3() {
        let code = "a ?? 2 / 3++";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::BinaryOperation {
                    operator: "??",
                    left: identifierb("a"),
                    right: Box::new(AST::BinaryOperation {
                        operator: "/",
                        left: intb(2),
                        right: Box::new(AST::UnaryOperation {
                            operator: "++",
                            side: crate::parser_model::OperatorSide::Right,
                            expr: intb(3),
                        }),
                    }),
                }
            ])
        ))
    }

    #[test]
    fn test_operator_4() {
        let code = "(1 + 3) * 2";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::BinaryOperation {
                    operator: "*",
                    left: Box::new(AST::Parenthesized(Box::new(AST::BinaryOperation {
                        operator: "+",
                        left: intb(1),
                        right: intb(3),
                    }))),
                    right: intb(2),
                }
            ])
        ))
    }

    #[test]
    fn test_operator_5() {
        let code = "previousValue = currentValue - previousValue;";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::BinaryOperation {
                    operator: "=",
                    left: identifierb("previousValue"),
                    right: Box::new(AST::BinaryOperation {
                        operator: "-",
                        left: identifierb("currentValue"),
                        right: identifierb("previousValue"),
                    }),
                }
            ])
        ))
    }

    #[test]
    fn test_operator_6() {
        let code = "currentValue += previousValue;";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::BinaryOperation {
                    operator: "+=",
                    left: identifierb("currentValue"),
                    right: identifierb("previousValue"),
                }
            ])
        ))
    }

    #[test]
    fn test_operator_7() {
        let code = "a - b + c";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::BinaryOperation {
                    operator: "+",
                    left: Box::new(AST::BinaryOperation {
                        operator: "-",
                        left: identifierb("a"),
                        right: identifierb("b"),
                    }),
                    right: identifierb("c"),
                }
            ])
        ))
    }

    #[test]
    fn test_operator_8() {
        let code = "a = b = c";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::BinaryOperation {
                    operator: "=",
                    left: identifierb("a"),
                    right: Box::new(AST::BinaryOperation {
                        operator: "=",
                        left: identifierb("b"),
                        right: identifierb("c"),
                    }),
                }
            ])
        ))
    }

    #[test]
    fn property_path_1() {
        let code = "a.b.c";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::PropertyPath(vec![
                    PathSegment::Property { property: identifier("a"), optional: false },
                    PathSegment::Property { property: identifier("b"), optional: false },
                    PathSegment::Property { property: identifier("c"), optional: false },
                ])
            ])
        ))
    }

    #[test]
    fn function_call_1() {
        let code = "a()";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::FunctionCall {
                    func: identifierb("a"),
                    args: vec![],
                }
            ])
        ))
    }

    #[test]
    fn function_call_2() {
        let code = "a(b)";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::FunctionCall {
                    func: identifierb("a"),
                    args: vec![ identifier("b") ],
                }
            ])
        ))
    }

    #[test]
    fn function_call_3() {
        let code = "a(b, c)";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::FunctionCall {
                    func: identifierb("a"),
                    args: vec![ identifier("b"), identifier("c") ],
                }
            ])
        ))
    }

    #[test]
    fn function_call_4() {
        let code = "a.b(b, c)";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::FunctionCall {
                    func: Box::new(AST::PropertyPath(vec![
                        PathSegment::Property { property: identifier("a"), optional: false },
                        PathSegment::Property { property: identifier("b"), optional: false },
                    ])),
                    args: vec![ identifier("b"), identifier("c") ],
                }
            ])
        ))
    }

    #[test]
    fn test_function_1() {
        let code = "
        function doThing(a, b) {
            let bar = a;

            return 12;
        }";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::Function {
                    name: Some(identifierb("doThing")),
                    args: vec![
                        identifier("a"),
                        identifier("b"),
                    ],
                    body: Box::new(AST::Block(vec![
                        AST::VariableDeclaration {
                            kind: DeclarationKind::Let,
                            identifier: identifierb("bar"),
                            expression: Some(identifierb("a")),
                        },
                        AST::ReturnStatement(Some(intb(12)))
                    ])),
                    is_arrow_function: false,
                }
            ])
        ))
    }

    #[test]
    fn test_arrow_function_1() {
        let code = "(a) => a + 2";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::Function {
                    name: None,
                    args: vec![
                        identifier("a"),
                    ],
                    body: Box::new(AST::BinaryOperation {
                        operator: "+",
                        left: identifierb("a"),
                        right: intb(2),
                    }),
                    is_arrow_function: true,
                }
            ])
        ))
    }

    #[test]
    fn test_arrow_function_2() {
        let code = "a => a + 2";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::Function {
                    name: None,
                    args: vec![
                        identifier("a"),
                    ],
                    body: Box::new(AST::BinaryOperation {
                        operator: "+",
                        left: identifierb("a"),
                        right: intb(2),
                    }),
                    is_arrow_function: true,
                }
            ])
        ))
    }

    #[test]
    fn test_arrow_function_3() {
        let code = "(a, b,) => a + 2";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::Function {
                    name: None,
                    args: vec![
                        identifier("a"),
                        identifier("b"),
                    ],
                    body: Box::new(AST::BinaryOperation {
                        operator: "+",
                        left: identifierb("a"),
                        right: intb(2),
                    }),
                    is_arrow_function: true,
                }
            ])
        ))
    }

    #[test]
    fn test_arrow_function_4() {
        let code = "
        (a, b) => {
            return a + 2;
        }";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::Function {
                    name: None,
                    args: vec![
                        identifier("a"),
                        identifier("b"),
                    ],
                    body: Box::new(AST::Block(vec![
                        AST::ReturnStatement(Some(
                            Box::new(AST::BinaryOperation {
                                operator: "+",
                                left: identifierb("a"),
                                right: intb(2),
                            })
                        ))
                    ])),
                    is_arrow_function: true,
                }
            ])
        ))
    }

    #[test]
    fn test_object_1() {
        let code = "
        var thing = {
            \"foo\": 12,
            'bar': 13,
            `blah`: 14,
            [stuff]: 15,
        }";

        let mut expected_object_contents = HashMap::new();
        expected_object_contents.insert(
            string("\"foo\""),
            int(12),
        );
        expected_object_contents.insert(
            string("'bar'"),
            int(13),
        );
        expected_object_contents.insert(
            string("`blah`"),
            int(14),
        );
        expected_object_contents.insert(
            AST::Indexer(identifierb("stuff")),
            int(15),
        );

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::VariableDeclaration {
                    kind: DeclarationKind::Var,
                    identifier: identifierb("thing"),
                    expression: Some(Box::new(AST::ObjectLiteral(expected_object_contents))),
                },
            ])
        ))
    }

    #[test]
    fn test_object_2() {
        let code = "
        var thing = {
            \"foo\": [
                4,
                { },
                [ ],
            ]
        }";

        let mut expected_object_contents = HashMap::new();
        expected_object_contents.insert(
            string("\"foo\""),
            AST::ArrayLiteral(vec![
                int(4),
                AST::ObjectLiteral(HashMap::new()),
                AST::ArrayLiteral(vec![]),
            ])
        );

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::VariableDeclaration {
                    kind: DeclarationKind::Var,
                    identifier: identifierb("thing"),
                    expression: Some(Box::new(AST::ObjectLiteral(expected_object_contents))),
                },
            ])
        ))
    }

    #[test]
    fn conditional_1() {
        let code = "
        if (n === 1) {
            return fibSequence;
        }";

        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::Conditional {
                    condition: Box::new(AST::BinaryOperation {
                        operator: "===",
                        left: identifierb("n"),
                        right: intb(1),
                    }),
                    if_body: Box::new(AST::Block(vec![
                        AST::ReturnStatement(Some(identifierb("fibSequence")))
                    ])),
                    else_body: None,
                }
            ])
        ))
    }

    #[test]
    fn test_algorithm() {
        let code = "
        function fibonacci(n) {
            const fibSequence = [1];
          
            let currentValue = 1;
            let previousValue = 0;
          
            if (n === 1) {
              return fibSequence;
            }
          
            let iterationsCounter = n - 1;
          
            while (iterationsCounter) {
              currentValue += previousValue;
              previousValue = currentValue - previousValue;

              fibSequence.push(currentValue);
          
              iterationsCounter -= 1;
            }
          
            return fibSequence;
        }";
          
        assert_eq!(parse(code), Ok(
            AST::Block(vec![
                AST::Function {
                    name: Some(identifierb("fibonacci")),
                    args: vec![ identifier("n") ],
                    body: Box::new(AST::Block(vec![

                        AST::VariableDeclaration {
                            kind: DeclarationKind::Const,
                            identifier: identifierb("fibSequence"),
                            expression: Some(Box::new(AST::ArrayLiteral(vec![ int(1) ]))),
                        },

                        AST::VariableDeclaration {
                            kind: DeclarationKind::Let,
                            identifier: identifierb("currentValue"),
                            expression: Some(intb(1)),
                        },
                        AST::VariableDeclaration {
                            kind: DeclarationKind::Let,
                            identifier: identifierb("previousValue"),
                            expression: Some(intb(0)),
                        },

                        AST::Conditional {
                            condition: Box::new(AST::BinaryOperation {
                                operator: "===",
                                left: identifierb("n"),
                                right: intb(1),
                            }),
                            if_body: Box::new(AST::Block(vec![
                                AST::ReturnStatement(Some(identifierb("fibSequence")))
                            ])),
                            else_body: None,
                        },

                        AST::VariableDeclaration {
                            kind: DeclarationKind::Let,
                            identifier: identifierb("iterationsCounter"),
                            expression: Some(Box::new(AST::BinaryOperation {
                                operator: "-",
                                left: identifierb("n"),
                                right: intb(1),
                            })),
                        },


                        AST::WhileLoop {
                            condition: identifierb("iterationsCounter"),
                            body: Box::new(AST::Block(vec![

                                AST::BinaryOperation {
                                    operator: "+=",
                                    left: identifierb("currentValue"),
                                    right: identifierb("previousValue"),
                                },

                                AST::BinaryOperation {
                                    operator: "=",
                                    left: identifierb("previousValue"),
                                    right: Box::new(AST::BinaryOperation {
                                        operator: "-",
                                        left: identifierb("currentValue"),
                                        right: identifierb("previousValue"),
                                    }),
                                },

                                AST::FunctionCall {
                                    func: Box::new(AST::PropertyPath(vec![
                                        PathSegment::Property { property: identifier("fibSequence"), optional: false },
                                        PathSegment::Property { property: identifier("push"), optional: false },
                                    ])),
                                    args: vec![
                                        identifier("currentValue"),
                                    ]
                                },

                                AST::BinaryOperation {
                                    operator: "-=",
                                    left: identifierb("iterationsCounter"),
                                    right: intb(1),
                                },

                            ])),
                        },

                        AST::ReturnStatement(Some(identifierb("fibSequence"))),

                    ])),
                    is_arrow_function: false,
                }
            ])
        ))
    }

    fn int(i: i32) -> AST {
        AST::NumberLiteral(format!("{}", i))
    }

    fn intb(i: i32) -> Box<AST> {
        Box::new(int(i))
    }

    fn float(f: f32) -> AST {
        AST::NumberLiteral(format!("{}", f))
    }

    fn floatb(f: f32) -> Box<AST> {
        Box::new(float(f))
    }

    fn identifier(s: &str) -> AST {
        AST::Identifier(String::from(s))
    }

    fn identifierb(s: &str) -> Box<AST> {
        Box::new(identifier(s))
    }

    fn string(s: &str) -> AST {
        AST::StringLiteral(String::from(s))
    }

    fn stringb(s: &str) -> Box<AST> {
        Box::new(string(s))
    }
}
