use std::fmt::{Display, Formatter};

use crate::text::span::TextSpan;


#[derive(Debug, PartialEq, Clone)]
pub enum TokenKind {
    // literals
    Number(i64),
    Usize(usize),
    String(String),

    // classic arithmetic operators
    Plus,
    PlusAs, // +=
    Minus,
    MinusAs, // -=
    Asterisk,
    AsteriskAs, // *=
    Slash,
    SlashAs, // /=
    Modulo,
    ModuloAs, // %=
    Equals,
    DoubleAsterisk, // ** for power

    // bitwise operators
    Ampersand, // & for bitwise and
    AmpersandAs, // &=
    Pipe, // | for bitwise or
    PipeAs, // |=
    Caret, // ^ for bitwise xor
    CaretAs, // ^=
    Tilde, // ~ for bitwise not
    ShiftLeft, // << for left shift
    ShiftLeftAs, // <<=
    ShiftRight, // >> for right shift
    ShiftRightAs, // >>=

    // relational operators
    LessThan, // < for less than
    GreaterThan, // > for greater than
    LessThanOrEqual, // <= for less than or equal
    GreaterThanOrEqual, // >= for greater than or equal
    EqualsEquals, // == for equality
    NotEquals, // != for inequality

    // keywords
    Let,
    If, 
    Else,
    True,
    False,
    While,
    Break,
    Continue,
    Function,
    Return,

    // separators
    LeftParen,
    RightParen,
    OpenBrace,
    CloseBrace,
    OpenBracket,
    CloseBracket,
    Comma,
    Colon,
    Arrow,
    SemiColon,
    DoubleQuote,

    // other
    Whitespace,
    Identifier,
    Bad,
    Eof,
}

impl TokenKind {
    /// Returns the non-assignment variant of an assignment operator token
    pub fn to_non_assignment(&self) -> Option<TokenKind> {
        match self {
            TokenKind::PlusAs => Some(TokenKind::Plus),
            TokenKind::MinusAs => Some(TokenKind::Minus),
            TokenKind::AsteriskAs => Some(TokenKind::Asterisk),
            TokenKind::SlashAs => Some(TokenKind::Slash),
            TokenKind::ModuloAs => Some(TokenKind::Modulo),
            TokenKind::AmpersandAs => Some(TokenKind::Ampersand),
            TokenKind::PipeAs => Some(TokenKind::Pipe),
            TokenKind::CaretAs => Some(TokenKind::Caret),
            TokenKind::ShiftLeftAs => Some(TokenKind::ShiftLeft),
            TokenKind::ShiftRightAs => Some(TokenKind::ShiftRight),
            _ => None,
        }
    }
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            // literals
            TokenKind::Number(_) => write!(f, "Number"),
            TokenKind::Usize(_) => write!(f, "Usize"),
            TokenKind::String(_) => write!(f, "String"),

            // classic arithmetic operators
            TokenKind::Plus => write!(f, "+"),
            TokenKind::PlusAs => write!(f, "+="),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::MinusAs => write!(f, "-="),
            TokenKind::Asterisk => write!(f, "*"),
            TokenKind::AsteriskAs => write!(f, "*="),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::SlashAs => write!(f, "/="),
            TokenKind::Modulo => write!(f, "%"),
            TokenKind::ModuloAs => write!(f, "%="),
            TokenKind::Equals => write!(f, "="),
            TokenKind::DoubleAsterisk => write!(f, "**"),

            // bitwise operators
            TokenKind::Ampersand => write!(f, "&"),
            TokenKind::AmpersandAs => write!(f, "&="),
            TokenKind::Pipe => write!(f, "|"),
            TokenKind::PipeAs => write!(f, "|="),
            TokenKind::Caret => write!(f, "^"),
            TokenKind::CaretAs => write!(f, "^="),
            TokenKind::Tilde => write!(f, "~"),
            TokenKind::ShiftLeft => write!(f, "<<"),
            TokenKind::ShiftLeftAs => write!(f, "<<="),
            TokenKind::ShiftRight => write!(f, ">>"),
            TokenKind::ShiftRightAs => write!(f, ">>="),

            // relational operators
            TokenKind::LessThan => write!(f, "<"),
            TokenKind::GreaterThan => write!(f, ">"),
            TokenKind::LessThanOrEqual => write!(f, "<="),
            TokenKind::GreaterThanOrEqual => write!(f, ">="),
            TokenKind::EqualsEquals => write!(f, "=="),
            TokenKind::NotEquals => write!(f, "!="),

            // keywords
            TokenKind::Let => write!(f, "Let"),
            TokenKind::If => write!(f, "If"),
            TokenKind::Else => write!(f, "Else"),
            TokenKind::True => write!(f, "True"),
            TokenKind::False => write!(f, "False"),
            TokenKind::While => write!(f, "While"),
            TokenKind::Break => write!(f, "Break"),
            TokenKind::Continue => write!(f, "Continue"),
            TokenKind::Function => write!(f, "Function"),
            TokenKind::Return => write!(f, "Return"),

            // separators
            TokenKind::LeftParen => write!(f, "("),
            TokenKind::RightParen => write!(f, ")"),
            TokenKind::OpenBrace => write!(f, "{{"),
            TokenKind::CloseBrace => write!(f, "}}"),
            TokenKind::OpenBracket => write!(f, "["),
            TokenKind::CloseBracket => write!(f, "]"),
            TokenKind::Comma => write!(f, "Comma"),
            TokenKind::Colon => write!(f, "Colon"),
            TokenKind::Arrow => write!(f, "Arrow"),
            TokenKind::SemiColon => write!(f, "Semicolon"),
            TokenKind::DoubleQuote => write!(f, "\""),

            // other
            TokenKind::Whitespace => write!(f, "Whitespace"),
            TokenKind::Identifier => write!(f, "Identifier"),
            TokenKind::Bad => write!(f, "Bad"),
            TokenKind::Eof => write!(f, "Eof"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Token {
    pub(crate) kind: TokenKind,
    pub(crate) span: TextSpan,
}

impl Token {
    pub fn new(kind: TokenKind, span: TextSpan) -> Self {
        Self { kind, span }
    }
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
                let (number, suffix) = self.consume_number();
                kind = match suffix.as_deref() {
                    Some("usize") => TokenKind::Usize(number as usize),
                    Some("u32") | Some("u64") => TokenKind::Usize(number as usize), // temp
                    None => TokenKind::Number(number),
                    _ => {
                        // todo: error reporting for unsupported suffixes
                        TokenKind::Number(number)
                    }
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

    fn consume_number(&mut self) -> (i64, Option<String>) {
        let mut number: i64 = 0;
        
        // Consume numeral
        while let Some(c) = self.current_char() {
            if c.is_digit(10) {
                self.consume().unwrap();
                number = number * 10 + c.to_digit(10).unwrap() as i64;
            } else {
                break;
            }
        }
        
        // Check for suffix (like "usize", "u32", etc.)
        let mut suffix = String::new();
        while let Some(c) = self.current_char() {
            if c.is_alphabetic() {
                suffix.push(c);
                self.consume().unwrap();
            } else {
                break;
            }
        }
        
        let suffix_option = if suffix.is_empty() { None } else { Some(suffix) };
        (number, suffix_option)
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