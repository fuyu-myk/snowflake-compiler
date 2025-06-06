use crate::ast::{ASTStatement, ASTExpression, ASTBinaryOperator, ASTBinaryOperatorKind, ASTBinaryOperatorAssociativity};
use crate::ast::lexer::{Token, TokenKind};
use crate::diagnostics::DiagnosticsReportCell;
use std::cell::Cell;


pub struct Counter {
    value: Cell<usize>
}

impl Counter {
    pub fn new() -> Self {
        Self {
            value: Cell::new(0)
        }
    }

    pub fn increment(&self) {
        let current_value = self.value.get();
        self.value.set(current_value + 1);
    }

    pub fn get_value(&self) -> usize {
        self.value.get()
    }
}

pub struct Parser {
    tokens: Vec<Token>,
    current: Counter,
    diagnostics_report: DiagnosticsReportCell,
}

impl Parser {
    pub fn new(
        tokens: Vec<Token>,
        diagnostics_report: DiagnosticsReportCell,
    ) -> Self {
        Self { 
            tokens: tokens.iter().filter(
                |token| token.kind != TokenKind::Whitespace
            ).map(|token| token.clone()).collect(), // filter whitespaces
            current: Counter::new(),
            diagnostics_report,
        }
    }

    pub fn next_statement(&mut self) -> Option<ASTStatement> {
        if self.is_at_end() {
            return None;
        }

        Some(self.parse_statement())
    }

    fn is_at_end(&self) -> bool {
        self.current().kind == TokenKind::Eof
    }

    fn parse_statement(&mut self) -> ASTStatement {
        match self.current().kind {
            TokenKind::Let => {
                self.parse_let_statement()
            },
            _ => {
                self.parse_expression_statement()
            }
        }
    }

    fn parse_let_statement(&mut self) -> ASTStatement {
        self.consume_and_check(TokenKind::Let); // check 'let'
        let identifier = self.consume_and_check(TokenKind::Identifier).clone(); // check variable
        self.consume_and_check(TokenKind::Equals); // check '='

        let expr = self.parse_expression();
        return ASTStatement::let_statement(identifier, expr);
    }

    fn parse_expression_statement(&mut self) -> ASTStatement {
        let expr = self.parse_expression();
        return ASTStatement::expression(expr);
    }

    fn parse_expression(&mut self) -> ASTExpression {
        return self.parse_binary_expression(0); // start w/ 0 precedence; no operators
    }

    fn parse_binary_expression(&mut self, precedence: u8) -> ASTExpression {
        let mut left = self.parse_primary_expression(); // parsing pri exp (only no.s for now)

        /*
         * parse pri exp, check if there are operators of higher precedence
         *  if no, return pri exp
         *  if yes, return another binary exp for higher precedence operation
         */
        while let Some(operator) = self.parse_binary_operator() { // try parsing bin operator
            self.consume();

            let operator_precedence = operator.precedence();
            if operator_precedence < precedence { // precedence checks (w/ current)
                break;
            }

            let right = self.parse_binary_expression(operator_precedence);
            left = ASTExpression::binary(operator, left, right);
        }

        return left;
    }

    fn parse_binary_operator(&mut self) -> Option<ASTBinaryOperator> {
        let token = self.current();

        let kind = match token.kind {
            TokenKind::Plus => {
                Some(ASTBinaryOperatorKind::Plus)
            },
            TokenKind::Minus => {
                Some(ASTBinaryOperatorKind::Minus)
            },
            TokenKind::Asterisk => {
                Some(ASTBinaryOperatorKind::Multiply)
            },
            TokenKind::Slash => {
                Some(ASTBinaryOperatorKind::Divide)
            },
            _ => None
        };
        return kind.map(|kind| ASTBinaryOperator::new(kind, token.clone()));
    }

    fn parse_primary_expression(&mut self) -> ASTExpression { // for string literals, numbers, function calls
        let token = self.consume();

        return match token.kind {
            TokenKind::Number(number) => {
                ASTExpression::number(number)
            },
            TokenKind::LeftParen => {
                let expr = self.parse_expression(); // because another exp in paren
                let token = self.consume_and_check(TokenKind::RightParen);
                
                ASTExpression::parenthesised(expr)
            },
            TokenKind::Identifier => {
                ASTExpression::identifier(token.clone())
            },
            _ => {
                self.diagnostics_report.borrow_mut().report_expected_expression(token);
                ASTExpression::error(token.span.clone())
            }
        }
    }

    fn current(&self) -> &Token {
        self.peek(0)
    }

    fn peek(&self, offset: isize) -> &Token {
        let mut index = (self.current.get_value() as isize + offset) as usize;

        if index >= self.tokens.len() {
            index = self.tokens.len() - 1;
        }

        self.tokens.get(index).unwrap()
    }

    fn consume(&self) -> &Token {
        self.current.increment();
        self.peek(-1)
    }

    fn consume_and_check(&self, kind: TokenKind) -> &Token {
        let token = self.consume();

        if token.kind != kind {
            self.diagnostics_report.borrow_mut().report_unexpected_token(
                &kind,
                token,
            );
        }

        token
    }
}