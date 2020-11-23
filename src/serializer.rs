use crate::{parser::parse, parser_model::{AST, OperatorSide}};

pub enum Indentation {
    Tabs,
    Spaces(u16),
    None,
}

pub struct SerializerOptions {
    // minify_names: bool,
    indentation: Indentation,
    indent_arrays: bool,
    indent_objects: bool,
    decorative_spaces: bool,
}

impl SerializerOptions {
    pub const DEFAULT: SerializerOptions = SerializerOptions {
        // minify_names: false,
        indentation: Indentation::Spaces(4),
        indent_arrays: false,
        indent_objects: true,
        decorative_spaces: true,
    };

    pub const MINIFY: SerializerOptions = SerializerOptions {
        // minify_names: true,
        indentation: Indentation::None,
        indent_arrays: false,
        indent_objects: false,
        decorative_spaces: false,
    };
}

pub fn serialize(ast: &AST, options: &SerializerOptions) -> Result<String, std::fmt::Error> {
    let mut s = String::new();
    if let AST::Block(lines) = ast {
        for line in lines {
            write_newline_and_indentation(options, &mut s, 0)?;
            serialize_inner(line, options, &mut s, 0)?;

            if !matches!(line, AST::Conditional { condition: _, if_body: _, else_body: _ }) && !matches!(line, AST::WhileLoop { condition: _, body: _ }) && !matches!(line, AST::Function { name: Some(_), args: _, body: _, is_arrow_function: false }) {
                s.push(';');
            }
        }
    } else {
        serialize_inner(ast, options, &mut s, 0)?;
    }
    return Ok(s);
}

fn serialize_inner<W: std::fmt::Write>(ast: &AST, options: &SerializerOptions, writer: &mut W, indentation: u16) -> Result<(), std::fmt::Error> {
    match ast {
        AST::Undefined => writer.write_str("undefined")?,
        AST::Null => writer.write_str("null")?,
        AST::BooleanLiteral(false) => writer.write_str("false")?,
        AST::BooleanLiteral(true) => writer.write_str("true")?,
        AST::NumberLiteral(x) => writer.write_str(x)?,
        AST::StringLiteral(x) => writer.write_str(x)?,
        AST::Identifier(x) => writer.write_str(x)?,
        AST::ArrayLiteral(x) => {
            writer.write_char('[')?;

            for (index, item) in x.iter().enumerate() {
                if index > 0 {
                    writer.write_char(',')?;
                    if options.decorative_spaces && !options.indent_arrays {
                        writer.write_char(' ')?;
                    }
                }

                if options.indent_arrays {
                    write_newline_and_indentation(options, writer, indentation + 1)?;
                }
                serialize_inner(item, options, writer, indentation + 1)?;
            }

            if options.indent_arrays {
                write_newline_and_indentation(options, writer, indentation)?;
            }
            writer.write_char(']')?;
        },
        AST::ObjectLiteral(x) => {
            writer.write_str("{")?;

            for (index, (key, value)) in x.iter().enumerate() {
                if index > 0 {
                    writer.write_char(',')?;
                    if options.decorative_spaces && !options.indent_objects {
                        writer.write_char(' ')?;
                    }
                }

                if options.indent_objects {
                    write_newline_and_indentation(options, writer, indentation + 1)?;
                }
                serialize_inner(key, options, writer, indentation + 1)?;

                writer.write_char(':')?;
                if options.decorative_spaces {
                    writer.write_char(' ')?;
                }

                serialize_inner(value, options, writer, indentation + 1)?;
            }

            if options.indent_objects {
                write_newline_and_indentation(options, writer, indentation)?;
            }
            writer.write_str("]")?;
        },
        AST::Function { name, args, body, is_arrow_function } => {
            if *is_arrow_function {
                if args.len() != 1 {
                    writer.write_char('(')?;
                }
                write_comma_separated(args, options, writer, indentation)?;
                if args.len() != 1 {
                    writer.write_char(')')?;
                }

                if options.decorative_spaces {
                    writer.write_char(' ')?;
                }

                writer.write_str("=>")?;

                if options.decorative_spaces {
                    writer.write_char(' ')?;
                }

                serialize_inner(body, options, writer, indentation)?;
            } else {
                writer.write_str("function")?;

                if let Some(name) = name {
                    writer.write_char(' ')?;
                    serialize_inner(name, options, writer, indentation)?;
                }

                writer.write_char('(')?;
                write_comma_separated(args, options, writer, indentation)?;
                writer.write_char(')')?;

                if options.decorative_spaces {
                    writer.write_char(' ')?;
                }

                serialize_inner(body, options, writer, indentation)?;
            }
        },
        AST::FunctionCall { func, args } => {
            serialize_inner(func, options, writer, indentation)?;

            writer.write_char('(')?;
            write_comma_separated(args, options, writer, indentation)?;
            writer.write_char(')')?;
        },
        AST::Indexer(x) => {
            writer.write_char('[')?;
            serialize_inner(x, options, writer, indentation)?;
            writer.write_char(']')?;
        },
        AST::PropertyPath(x) => {
            for (index, item) in x.iter().enumerate() {
                if index > 0 {
                    writer.write_char('.')?;
                    // TODO: optional
                }
                
                serialize_inner(&item.property, options, writer, indentation)?;
            }
        },
        AST::Block(x) => {
            writer.write_char('{')?;
            for line in x {
                write_newline_and_indentation(options, writer, indentation + 1)?;
                serialize_inner(line, options, writer, indentation + 1)?;

                if !matches!(line, AST::Conditional { condition: _, if_body: _, else_body: _ }) && !matches!(line, AST::WhileLoop { condition: _, body: _ }) && !matches!(line, AST::Function { name: Some(_), args: _, body: _, is_arrow_function: false }) {
                    writer.write_char(';')?;
                }
            }
            write_newline_and_indentation(options, writer, indentation)?;
            writer.write_char('}')?;
        },
        AST::Conditional { condition, if_body, else_body } => {
            writer.write_str("if")?;

            if options.decorative_spaces {
                writer.write_char(' ')?;
            }

            writer.write_char('(')?;
            serialize_inner(condition, options, writer, indentation)?;
            writer.write_char(')')?;

            // if options.decorative_spaces {
                writer.write_char(' ')?;
            // }

            if !matches!(if_body.as_ref(), AST::Block(_)) {
                write_newline_and_indentation(options, writer, indentation + 1)?;
                serialize_inner(if_body, options, writer, indentation + 1)?;
            } else {
                serialize_inner(if_body, options, writer, indentation)?;
            }

            if let Some(else_body) = else_body {
                writer.write_str("else")?;

                // if options.decorative_spaces {
                    writer.write_char(' ')?;
                // }
    
                if !matches!(else_body.as_ref(), AST::Block(_)) && !matches!(else_body.as_ref(), AST::Conditional { condition: _, if_body: _, else_body: _ }) {
                    write_newline_and_indentation(options, writer, indentation + 1)?;
                    serialize_inner(else_body, options, writer, indentation + 1)?;
                } else {
                    serialize_inner(else_body, options, writer, indentation)?;
                }

            }
        },
        AST::WhileLoop { condition, body } => {
            writer.write_str("while")?;

            if options.decorative_spaces {
                writer.write_char(' ')?;
            }

            writer.write_char('(')?;
            serialize_inner(condition, options, writer, indentation)?;
            writer.write_char(')')?;

            // if options.decorative_spaces {
                writer.write_char(' ')?;
            // }

            if !matches!(body.as_ref(), AST::Block(_)) {
                write_newline_and_indentation(options, writer, indentation + 1)?;
                serialize_inner(body, options, writer, indentation + 1)?;
            } else {
                serialize_inner(body, options, writer, indentation)?;
            }
        },
        AST::UnaryOperation { operator, expr, side } => {
            match side {
                OperatorSide::Left => {
                    writer.write_str(operator)?;
                    serialize_inner(expr, options, writer, indentation)?;
                },
                OperatorSide::Right => {
                    serialize_inner(expr, options, writer, indentation)?;
                    writer.write_str(operator)?;
                },
            }
        },
        AST::BinaryOperation { operator, left, right } => {
            serialize_inner(left, options, writer, indentation)?;

            if options.decorative_spaces {
                writer.write_char(' ')?;
            }

            writer.write_str(operator)?;

            if options.decorative_spaces {
                writer.write_char(' ')?;
            }

            serialize_inner(right, options, writer, indentation)?;
        },
        AST::VariableDeclaration { kind, identifier, expression } => {
            writer.write_str(kind.to_keyword())?;

            writer.write_char(' ')?;

            serialize_inner(identifier, options, writer, indentation)?;

            if let Some(expression) = expression {
                if options.decorative_spaces {
                    writer.write_char(' ')?;
                }

                writer.write_char('=')?;

                if options.decorative_spaces {
                    writer.write_char(' ')?;
                }
                
                serialize_inner(expression, options, writer, indentation)?;
            }
        },
        AST::ReturnStatement(x) => {
            writer.write_str("return")?;

            if let Some(x) = x {
                writer.write_char(' ')?;
                serialize_inner(x, options, writer, indentation + 1)?;
            }
        },
        AST::Parenthesized(x) => {
            writer.write_char('(')?;
            serialize_inner(x, options, writer, indentation)?;
            writer.write_char(')')?;
        },
    }

    Ok(())
}

fn write_comma_separated<W: std::fmt::Write>(items: &Vec<AST>, options: &SerializerOptions, writer: &mut W, indentation: u16) -> Result<(), std::fmt::Error> {
    for (index, item) in items.iter().enumerate() {
        if index > 0 {
            writer.write_char(',')?;
            if options.decorative_spaces {
                writer.write_char(' ')?;
            }
        }

        serialize_inner(item, options, writer, indentation + 1)?;
    }

    Ok(())
}

fn write_newline_and_indentation<W: std::fmt::Write>(options: &SerializerOptions, writer: &mut W, indentation: u16) -> Result<(), std::fmt::Error> {

    match options.indentation {
        Indentation::Spaces(spaces) => {
            writer.write_char('\n')?;

            for _ in 0..(spaces * indentation) {
                writer.write_char(' ')?;
            }
        },
        Indentation::Tabs => {
            writer.write_char('\n')?;

            for _ in 0..indentation {
                writer.write_char('\t')?;
            }
        },
        Indentation::None => {},
    }

    Ok(())
}

#[test]
fn serializer_test_1() {
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
    }
    
    fibonacci(10);";

    let ast = parse(code).unwrap();

    println!("{}", serialize(&ast, &SerializerOptions::DEFAULT).unwrap());
    println!("{}", serialize(&ast, &SerializerOptions::MINIFY).unwrap());
}