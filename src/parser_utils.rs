
#[derive(Debug,PartialEq)]
pub struct ParseError {
    pub msg: String,
    pub line: usize,
    pub column: usize,
}

impl ParseError {
    pub fn new<S: Into<String>>(code: &str, index: usize, msg: S) -> Self {
        let (line, column) = index_to_line_column(code, index);

        return ParseError { 
            msg: msg.into(), 
            line,
            column
        };
    }
}

fn index_to_line_column(code: &str, index: usize) -> (usize, usize) {
    let mut line = 1;
    let mut column = 1;

    for (_, ch) in code.char_indices().take_while(|(i, _)| *i < index) {
        if ch == '\n' {
            line += 1;
            column = 1;
        } else {
            column += 1;
        }
    }

    return (line, column);
}


pub fn consume_whitespace(code: &str, index: &mut usize, stop_at_newline: bool) {
    if let Some(length) = code[*index..]
            .char_indices()
            .take_while(|(_, ch)| ch.is_whitespace() && (!stop_at_newline || *ch != '\n'))
            .last()
            .map(|(i, ch)| i + ch.len_utf8()) {
        *index += length;
    }
}

pub fn try_eat(code: &str, index: &mut usize, expected: &'static str) -> Result<&'static str, ParseError> {
    let original_index = *index;
    consume_whitespace(code, index, false);
    
    let rest = &code[*index..];
    if expected.len() <= rest.len() && expected.chars().zip(rest.chars()).all(|(a, b)| a == b) {
        *index += expected.len();
        Ok(expected)
    } else {
        *index = original_index;
        Err(ParseError::new(code, *index, format!("Expected '{}'", expected)))
    }
}

pub fn try_eat_while<'a, F: Fn(char) -> bool>(code: &'a str, index: &mut usize, pred: F) -> Result<&'a str, ParseError> {
    let original_index = *index;
    consume_whitespace(code, index, false);

    let length = &code[*index..]
        .char_indices()
        .take_while(|(_, c)| pred(*c))
        .last()
        .map(|(i, _)| i);

    if let Some(length) = length {
        let end = *index + length+1;
        let matched = &code[*index..end];
        *index = end;
        Ok(matched)
    } else {
        *index = original_index;
        Err(ParseError::new(code, *index, "Expected segment matching predicate"))
    }
}


#[cfg(test)]
mod tests {
    use super::{try_eat, try_eat_while};

    #[test]
    fn test_try_eat_1() {
        let code = "foo";
        let mut index = 0;
        assert!(try_eat(code, &mut index, "foo").is_ok());
        assert_eq!(index, code.len());
    }
    
    #[test]
    fn test_try_eat_2() {
        let code = "foo";
        let mut index = 0;
        assert!(try_eat(code, &mut index, "bar").is_err());
        assert_eq!(index, 0);
    }
    
    #[test]
    fn test_try_eat_3() {
        let code = "foo";
        let mut index = 0;
        assert!(try_eat(code, &mut index, "oo").is_err());
        assert_eq!(index, 0);
    }
    
    #[test]
    fn test_try_eat_4() {
        let code = "aƟb";
        let mut index = 0;
        assert!(try_eat(code, &mut index, "aƟb").is_ok());
        assert_eq!(index, code.len());
    }
    
    #[test]
    fn test_try_eat_5() {
        let code = "aaƟb";
        let mut index = 0;
        assert!(try_eat(code, &mut index, "aƟb").is_err());
        assert_eq!(index, 0);
    }



    fn numeric(ch: char) -> bool {
        ch.is_numeric()
    }

    fn alphabetic(ch: char) -> bool {
        ch.is_alphabetic()
    }

    #[test]
    fn test_try_eat_while_1() {
        let code = "abc123";
        let mut index = 0;
        assert!(try_eat_while(code, &mut index, numeric).is_err());
        assert_eq!(index, 0);
    }

    #[test]
    fn test_try_eat_while_2() {
        let code = "abc123";
        let mut index = 0;
        assert_eq!(try_eat_while(code, &mut index, alphabetic), Ok("abc"));
        assert_eq!(index, 3);
    }

    #[test]
    fn test_try_eat_while_3() {
        let code = "abc123";
        let mut index = 3;
        assert_eq!(try_eat_while(code, &mut index, numeric), Ok("123"));
        assert_eq!(index, 6);
    }

    #[test]
    fn test_try_eat_while_4() {
        let code = "abc123 def";
        let mut index = 3;
        assert_eq!(try_eat_while(code, &mut index, numeric), Ok("123"));
        assert_eq!(index, 6);
    }
}