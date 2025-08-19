use snowflake_common::text::span::TextSpan;
use snowflake_common::token::{Token, TokenKind};

/// Helper function to create a test token
pub fn test_token(kind: TokenKind, literal: &str) -> Token {
    Token::new(kind, TextSpan::new(0, literal.len(), literal.to_string()))
}

/// Helper function to create a test span
pub fn test_span(literal: &str) -> TextSpan {
    TextSpan::new(0, literal.len(), literal.to_string())
}