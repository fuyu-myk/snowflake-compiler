use snowflake_common::text::span::TextSpan;
use snowflake_common::token::{Token, TokenKind};

#[derive(Debug, PartialEq)]
enum NumberResult {
    Integer(i64, Option<String>),
    Float(f64, Option<String>),
    Malformed,
}

pub struct Lexer<'a> {
    input: &'a str,
    current_pos: usize,
}

impl <'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Self { input, current_pos: 0 }
    }

    pub fn next_token(&mut self) -> Option<Token> {
        // To recognise end of token stream
        if self.current_pos == self.input.len() {
            let eof_char: char = '\0';

            self.current_pos += 1;

            return Some(Token::new(
                TokenKind::Eof,
                TextSpan::new(0, 0, eof_char.to_string())
            ));
        }


        let c = self.current_char();
        
        return c.map(|c| {
            let start: usize = self.current_pos;
            let mut kind = TokenKind::Bad; // If there is a token that we cannot lext

            if Self::is_number_start(&c) {
                let number_result = self.consume_number();
                kind = match number_result {
                    NumberResult::Integer(number, suffix) => {
                        match suffix.as_deref() {
                            Some("usize") => TokenKind::Usize(number as usize),
                            Some("u32") | Some("u64") => TokenKind::Usize(number as usize), // temp
                            None => TokenKind::Number(number),
                            _ => {
                                // todo: error reporting for unsupported suffixes
                                TokenKind::Number(number)
                            }
                        }
                    },
                    NumberResult::Float(float_val, _suffix) => {
                        // For now, ignore float suffixes, but you could handle "f", "d", etc.
                        TokenKind::Float(float_val)
                    },
                    NumberResult::Malformed => TokenKind::Bad,
                };
            } else if c == '"' {
                self.consume();
                let string_value = self.consume_string_literal();
                self.consume();
                kind = TokenKind::String(string_value);
            } else if Self::is_whitespace(&c) {
                self.consume();
                kind = TokenKind::Whitespace;
            } else if Self::is_identifier_start(&c) {
                let identifier = self.consume_identifier();

                kind = match identifier.as_str() {
                    "let" => TokenKind::Let,
                    "if" => TokenKind::If,
                    "else" => TokenKind::Else,
                    "true" => TokenKind::True,
                    "false" => TokenKind::False,
                    "while" => TokenKind::While,
                    "break" => TokenKind::Break,
                    "continue" => TokenKind::Continue,
                    "fx" => TokenKind::Function,
                    "return" => TokenKind::Return,
                    _ => TokenKind::Identifier,
                }
            } else {
                kind = self.consume_punctuation();
            }

            let end: usize = self.current_pos;
            let literal: String = self.input[start..end].to_string();
            let span = TextSpan::new(start, end, literal);
            
            Token::new(kind, span)
        });
    }

    fn consume_number(&mut self) -> NumberResult {
        let start_pos = self.current_pos;
        let mut has_decimal = false;
        let mut has_exponent = false;
        
        // Consume integer part
        while let Some(c) = self.current_char() {
            if c.is_digit(10) {
                self.consume().unwrap();
            } else {
                break;
            }
        }
        
        // Check for decimal point
        if let Some('.') = self.current_char() {
            // Look ahead to ensure it's not a method call (e.g., "123.method()")
            if let Some(next_char) = self.peek_char() {
                if next_char.is_digit(10) {
                    has_decimal = true;
                    self.consume().unwrap();
                    
                    while let Some(c) = self.current_char() {
                        if c.is_digit(10) {
                            self.consume().unwrap();
                        } else {
                            break;
                        }
                    }
                }
            }
        }
        
        // Check for exponent (e or E)
        if let Some(c) = self.current_char() {
            if c == 'e' || c == 'E' {
                has_exponent = true;
                self.consume().unwrap();
                
                if let Some(sign) = self.current_char() {
                    if sign == '+' || sign == '-' {
                        self.consume().unwrap();
                    }
                }
                
                let mut has_exponent_digits = false;
                while let Some(c) = self.current_char() {
                    if c.is_digit(10) {
                        has_exponent_digits = true;
                        self.consume().unwrap();
                    } else {
                        break;
                    }
                }
                
                if !has_exponent_digits {
                    return NumberResult::Malformed;
                }
            }
        }
        
        // Check for suffix (like "f", "d", "usize", "u32", etc.)
        let mut suffix = String::new();
        while let Some(c) = self.current_char() {
            if c.is_alphabetic() {
                suffix.push(c);
                self.consume().unwrap();
            } else {
                break;
            }
        }
        
        let number_str = &self.input[start_pos..self.current_pos - suffix.len()];
        let suffix_option = if suffix.is_empty() { None } else { Some(suffix) };
        
        if has_decimal || has_exponent {
            // Parse as floating point
            match number_str.parse::<f64>() {
                Ok(float_val) => NumberResult::Float(float_val, suffix_option),
                Err(_) => NumberResult::Malformed,
            }
        } else {
            // Parse as integer
            match number_str.parse::<i64>() {
                Ok(int_val) => NumberResult::Integer(int_val, suffix_option),
                Err(_) => NumberResult::Malformed,
            }
        }
    }

    fn consume_string_literal(&mut self) -> String {
        let mut string_value = String::new();
        while let Some(c) = self.current_char() {
            if c == '"' {
                break;
            }
            if c == '\\' {
                // Handle escape sequences
                self.consume();
                if let Some(escaped_char) = self.current_char() {
                    match escaped_char {
                        'n' => string_value.push('\n'),
                        't' => string_value.push('\t'),
                        'r' => string_value.push('\r'),
                        '\\' => string_value.push('\\'),
                        '"' => string_value.push('"'),
                        _ => {
                            // For unrecognized escape sequences, just include both characters
                            string_value.push('\\');
                            string_value.push(escaped_char);
                        }
                    }
                    self.consume();
                }
            } else {
                string_value.push(c);
                self.consume();
            }
        }
        string_value
    }

    fn consume_punctuation(&mut self) -> TokenKind {
        let c = self.consume().unwrap();

        match c {
            '+' => self.potential_multi_char_operator('+'),
            '-' => self.potential_multi_char_operator('-'),
            '*' => self.potential_multi_char_operator('*'),
            '/' => self.potential_multi_char_operator('/'),
            '%' => self.potential_multi_char_operator('%'),
            '(' => TokenKind::LeftParen,
            ')' => TokenKind::RightParen,
            '=' => self.potential_multi_char_operator('='),
            '&' => self.potential_multi_char_operator('&'),
            '|' => self.potential_multi_char_operator('|'),
            '^' => self.potential_multi_char_operator('^'),
            '~' => TokenKind::Tilde,
            '<' => self.potential_multi_char_operator('<'),
            '>' => self.potential_multi_char_operator('>'),
            '!' => self.potential_multi_char_operator('!'),
            '{' => TokenKind::OpenBrace,
            '}' => TokenKind::CloseBrace,
            '[' => TokenKind::OpenBracket,
            ']' => TokenKind::CloseBracket,
            ',' => TokenKind::Comma,
            ':' => TokenKind::Colon,
            ';' => TokenKind::SemiColon,
            '"' => TokenKind::DoubleQuote,
            _ => TokenKind::Bad,
        }
    }

    fn potential_multi_char_operator(&mut self, first_char: char) -> TokenKind {
        match first_char {
            '+' => {
                match self.current_char() {
                    Some('=') => {
                        self.consume();
                        TokenKind::PlusAs
                    },
                    _ => TokenKind::Plus,
                }
            },
            '-' => {
                match self.current_char() {
                    Some('=') => {
                        self.consume();
                        TokenKind::MinusAs
                    },
                    Some('>') => {
                        self.consume();
                        TokenKind::Arrow
                    },
                    _ => TokenKind::Minus,
                }
            }
            '*' => {
                match self.current_char() {
                    Some('*') => {
                        self.consume();
                        TokenKind::DoubleAsterisk
                    },
                    Some('=') => {
                        self.consume();
                        TokenKind::AsteriskAs
                    },
                    _ => TokenKind::Asterisk,
                }
            },
            '/' => {
                match self.current_char() {
                    Some('=') => {
                        self.consume();
                        TokenKind::SlashAs
                    },
                    Some('/') => {
                        self.consume();
                        self.consume_line_comment();
                        TokenKind::LineComment
                    }
                    Some('*') => {
                        self.consume();
                        self.consume_block_comment();
                        TokenKind::BlockComment
                    },
                    _ => TokenKind::Slash,
                }
            },
            '%' => {
                match self.current_char() {
                    Some('=') => {
                        self.consume();
                        TokenKind::ModuloAs
                    },
                    _ => TokenKind::Modulo,
                }
            },
            '&' => {
                match self.current_char() {
                    Some('=') => {
                        self.consume();
                        TokenKind::AmpersandAs
                    },
                    _ => TokenKind::Ampersand,
                }
            },
            '|' => {
                match self.current_char() {
                    Some('=') => {
                        self.consume();
                        TokenKind::PipeAs
                    },
                    _ => TokenKind::Pipe,
                }
            },
            '^' => {
                match self.current_char() {
                    Some('=') => {
                        self.consume();
                        TokenKind::CaretAs
                    },
                    _ => TokenKind::Caret,
                }
            },
            '>' => {
                match self.current_char() {
                    Some('=') => {
                        self.consume();
                        TokenKind::GreaterThanOrEqual
                    },
                    Some('>') => {
                        self.consume();
                        match self.current_char() {
                            Some('=') => {
                                self.consume();
                                TokenKind::ShiftRightAs
                            },
                            _ => TokenKind::ShiftRight,
                        }
                    },
                    _ => TokenKind::GreaterThan,
                }
            },
            '<' => {
                match self.current_char() {
                    Some('=') => {
                        self.consume();
                        TokenKind::LessThanOrEqual
                    },
                    Some('<') => {
                        self.consume();
                        match self.current_char() {
                            Some('=') => {
                                self.consume();
                                TokenKind::ShiftLeftAs
                            },
                            _ => TokenKind::ShiftLeft,
                        }
                    },
                    _ => TokenKind::LessThan,
                }
            },
            '=' => {
                match self.current_char() {
                    Some('=') => {
                        self.consume();
                        TokenKind::EqualsEquals
                    },
                    _ => TokenKind::Equals,
                }
            },
            '!' => {
                match self.current_char() {
                    Some('=') => {
                        self.consume();
                        TokenKind::NotEquals
                    },
                    _ => TokenKind::Bad,
                }
            },
            _ => TokenKind::Bad,
        }
    }

    fn consume_block_comment(&mut self) {
        while let Some(c) = self.current_char() {
            if c == '*' {
                self.consume();
                if let Some(next_char) = self.current_char() {
                    if next_char == '/' {
                        self.consume();
                        break;
                    }
                }
            } else {
                self.consume();
            }
        }
    }

    fn consume_line_comment(&mut self) {
        while let Some(c) = self.current_char() {
            if c == '\n' {
                self.consume();
                break;
            } else {
                self.consume();
            }
        }
    }

    fn consume_identifier(&mut self) -> String {
        let mut identifier = String::new();

        while let Some(c) = self.current_char() {
            if Self::is_identifier_continue(&c) {
                self.consume().unwrap();
                identifier.push(c);
            } else {
                break;
            }
        }
        identifier
    }

    fn is_whitespace(c: &char) -> bool {
        c.is_whitespace()
    }

    fn is_number_start(c: &char) -> bool {
        c.is_digit(10)
    }

    fn current_char(&self) -> Option<char> {
        self.input.chars().nth(self.current_pos)
    }

    fn peek_char(&self) -> Option<char> {
        self.input.chars().nth(self.current_pos + 1)
    }

    fn consume(&mut self) -> Option<char> {
        if self.current_pos >= self.input.len() {
            return None;
        }
        
        let c = self.current_char();
        self.current_pos += 1;

        c
    }

    fn is_identifier_start(c: &char) -> bool {
        c.is_alphabetic() || *c == '_'
    }

    fn is_identifier_continue(c: &char) -> bool {
        c.is_alphanumeric() || *c == '_'
    }
}