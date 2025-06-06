use std::fmt::{Display, Formatter};


#[derive(Debug, PartialEq, Clone)]
pub enum TokenKind {
    Number(i64),
    Plus,
    Minus,
    Asterisk,
    Slash,
    LeftParen,
    RightParen,
    Whitespace,
    Let,
    Identifier,
    Equals,
    Bad,
    Eof,
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenKind::Number(_) => write!(f, "Number"),
            TokenKind::Plus => write!(f, "+"),
            TokenKind::Minus => write!(f, "-"),
            TokenKind::Asterisk => write!(f, "*"),
            TokenKind::Slash => write!(f, "/"),
            TokenKind::LeftParen => write!(f, "("),
            TokenKind::RightParen => write!(f, ")"),
            TokenKind::Whitespace => write!(f, "Whitespace"),
            TokenKind::Let => write!(f, "Let"),
            TokenKind::Identifier => write!(f, "Identifier"),
            TokenKind::Equals => write!(f, "="),
            TokenKind::Bad => write!(f, "Bad"),
            TokenKind::Eof => write!(f, "Eof"),
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TextSpan {
    pub(crate) start: usize,
    pub(crate) end: usize,
    pub(crate) literal: String,
}

impl TextSpan {
    pub fn new(start: usize, end: usize, literal: String) -> Self {
        Self { start, end, literal }
    }

    pub fn length(&self) -> usize {
        self.end - self.start
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
                let number: i64 = self.consume_number();
                kind = TokenKind::Number(number);
            } else if Self::is_whitespace(&c) { // Handling whitespaces, else it'd be 'Bad token'
                self.consume();
                kind = TokenKind::Whitespace;
            } else if Self::is_identifier_start(&c) {
                let identifier = self.consume_identifier();

                kind = match identifier.as_str() {
                    "let" => TokenKind::Let,
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

    fn consume_number(&mut self) -> i64 {
        let mut number: i64 = 0;
        while let Some(c) = self.current_char() {
            if c.is_digit(10) {
                self.consume().unwrap();
                number = number * 10 + c.to_digit(10).unwrap() as i64;
            } else {
                break;
            }
        }
        number
    }

    fn consume_punctuation(&mut self) -> TokenKind {
        let c = self.consume().unwrap();

        match c {
            '+' => TokenKind::Plus,
            '-' => TokenKind::Minus,
            '*' => TokenKind::Asterisk,
            '/' => TokenKind::Slash,
            '(' => TokenKind::LeftParen,
            ')' => TokenKind::RightParen,
            '=' => TokenKind::Equals,
            _ => TokenKind::Bad,
        }
    }

    fn consume_identifier(&mut self) -> String {
        let mut identifier = String::new();

        while let Some(c) = self.current_char() {
            if Self::is_identifier_start(&c) {
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
        c.is_alphabetic()
    }
}