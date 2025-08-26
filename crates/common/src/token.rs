use std::fmt::{Display, Formatter};

use crate::text::span::TextSpan;


#[derive(Debug, PartialEq, Clone)]
pub enum TokenKind {
    // literals
    Number(i64),
    Float(f64),
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
    Mutable,

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
    Period,

    // comments (handled by lexer, not tokenized)
    LineComment, // // for single line comments
    BlockComment, // /* ... */ for multi-line comments

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
            TokenKind::Float(_) => write!(f, "Float"),
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
            TokenKind::Mutable => write!(f, "Mutable"),

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
            TokenKind::Period => write!(f, "Period"),

            // comments
            TokenKind::LineComment => write!(f, "LineComment"),
            TokenKind::BlockComment => write!(f, "BlockComment"),

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
    pub kind: TokenKind,
    pub span: TextSpan,
}

impl Token {
    pub fn new(kind: TokenKind, span: TextSpan) -> Self {
        Self { kind, span }
    }
}