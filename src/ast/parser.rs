use crate::ast::{ASTBinaryOperator, ASTBinaryOperatorKind, ASTElseStatement, ASTExpression, ASTStatement, ASTUnaryOperator, ASTUnaryOperatorKind, Ast, FxDeclarationParams};
use crate::ast::lexer::{Token, TokenKind};
use crate::diagnostics::DiagnosticsReportCell;
use std::cell::Cell;


#[derive(Debug, Clone)]
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

pub struct Parser<'a> {
    tokens: Vec<Token>,
    current: Counter,
    diagnostics_report: DiagnosticsReportCell,
    ast: &'a mut Ast,
}

impl <'a> Parser<'a> {
    pub fn new(
        tokens: Vec<Token>,
        diagnostics_report: DiagnosticsReportCell,
        ast: &'a mut Ast
    ) -> Self {
        Self { 
            tokens: tokens.iter().filter(
                |token| token.kind != TokenKind::Whitespace
            ).map(|token| token.clone()).collect(), // filter whitespaces
            current: Counter::new(),
            diagnostics_report,
            ast,
        }
    }

    pub fn parse(&mut self) {
        while let Some(statement) = self.next_statement().map(|statement| statement.id) {
            self.ast.mark_top_level_statement(statement);
        }
    }

    pub fn next_statement(&mut self) -> Option<&ASTStatement> {
        if self.is_at_end() {
            return None;
        }

        Some(self.parse_statement())
    }

    fn is_at_end(&self) -> bool {
        self.current().kind == TokenKind::Eof
    }

    fn parse_statement(&mut self) -> &ASTStatement {
        match self.current().kind {
            TokenKind::Let => {
                self.parse_let_statement()
            }
            TokenKind::If => {
                self.parse_if_statement()
            }
            TokenKind::OpenBrace => {
                self.parse_block_statement()
            }
            TokenKind::While => {
                self.parse_while_statement()
            }
            TokenKind::Function => {
                self.parse_function_declaration()
            }
            TokenKind::Return => {
                self.parse_return_statement()
            }
            _ => {
                self.parse_expression_statement()
            }
        }
    }

    fn parse_function_declaration(&mut self) -> &ASTStatement {
        self.consume_and_check(TokenKind::Function); // consume 'fx'
        let identifier = self.consume_and_check(TokenKind::Identifier).clone(); // fx name

        // parse params (optional)
        let parameters = self.parse_optional_param_list();

        // parse body
        let body = self.parse_statement().id;
        self.ast.func_decl_statement(identifier, parameters, body)
    }

    fn parse_optional_param_list(&mut self) -> Vec<FxDeclarationParams> {
        if self.current().kind != TokenKind::LeftParen {
            return Vec::new();
        }

        self.consume_and_check(TokenKind::LeftParen);
        let mut parameters = Vec::new();
        while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
            parameters.push(FxDeclarationParams { 
                identifier: self.consume_and_check(TokenKind::Identifier).clone()
            });

            if self.current().kind == TokenKind::Comma {
                self.consume_and_check(TokenKind::Comma);
            }
        }

        self.consume_and_check(TokenKind::RightParen);
        parameters
    }

    fn parse_return_statement(&mut self) -> &ASTStatement {
        let return_keyword = self.consume_and_check(TokenKind::Return).clone();
        let expression = self.parse_expression().id;
        // todo: allow ecmpty return statements

        self.ast.return_statement(return_keyword, Some(expression))
    }

    fn parse_while_statement(&mut self) -> &ASTStatement {
        let while_keyword = self.consume_and_check(TokenKind::While).clone();
        let condition_expr = self.parse_expression().id;
        let body = self.parse_statement().id;

        self.ast.while_statement(while_keyword, condition_expr, body)
    }

    fn parse_block_statement(&mut self) -> &ASTStatement {
        self.consume_and_check(TokenKind::OpenBrace);
        let mut statements = Vec::new();

        while self.current().kind != TokenKind::CloseBrace && !self.is_at_end() {
            statements.push(self.parse_statement().id);
        }

        self.consume_and_check(TokenKind::CloseBrace);
        self.ast.block_statement(statements)
    }

    fn parse_if_statement(&mut self) -> &ASTStatement {
        let if_keyword = self.consume_and_check(TokenKind::If).clone(); // checks for 'if'
        let condition_expr = self.parse_expression().id; // parsing condition expression
        let then = self.parse_statement().id; // parsing 'then' statement
        let else_statement = self.parse_optional_else_statement(); // if there is an 'else' statement, parse it

        self.ast.if_statement(if_keyword, condition_expr, then, else_statement)
    }

    fn parse_optional_else_statement(&mut self) -> Option<ASTElseStatement> {
        if self.current().kind == TokenKind::Else {
            let else_keyword = self.consume_and_check(TokenKind::Else).clone(); // checks for 'else'
            let else_statement = self.parse_statement().id; // parsing 'else' statement
            return Some(ASTElseStatement::new(else_keyword, else_statement));
        }

        None
    }

    fn parse_let_statement(&mut self) -> &ASTStatement {
        self.consume_and_check(TokenKind::Let); // check 'let'
        let identifier = self.consume_and_check(TokenKind::Identifier).clone(); // check variable
        self.consume_and_check(TokenKind::Equals); // check '='

        let expr = self.parse_expression().id;
        self.ast.let_statement(identifier, expr)
    }

    fn parse_expression_statement(&mut self) -> &ASTStatement {
        let expr = self.parse_expression().id;
        self.ast.expression_statement(expr)
    }

    fn parse_expression(&mut self) -> &ASTExpression {
        return self.parse_assignment_expression();
    }

    fn parse_assignment_expression(&mut self) -> &ASTExpression {
        if self.current().kind == TokenKind::Identifier {
            if self.peek(1).kind == TokenKind::Equals {
                let identifier = self.consume_and_check(TokenKind::Identifier).clone();
                self.consume_and_check(TokenKind::Equals);
                let expr = self.parse_expression().id;

                return self.ast.assignment_expression(identifier, expr);
            }
        }
        return self.parse_binary_expression(0);
    }

    fn parse_binary_expression(&mut self, precedence: u8) -> &ASTExpression {
        let mut left = self.parse_unary_expression().id; // parsing pri exp (only no.s for now)

        /*
         * parse pri exp, check if there are operators of higher precedence
         *  if no, return pri exp
         *  if yes, return another binary exp for higher precedence operation
         */
        while let Some(operator) = self.parse_binary_operator() { // try parsing bin operator
            let operator_precedence = operator.precedence();
            if operator_precedence < precedence { // precedence checks (w/ current)
                break;
            }

            self.consume();

            let right = self.parse_binary_expression(operator_precedence).id;
            left = self.ast.binary_expression(operator, left, right).id;
        }

        let left = self.ast.query_expression(&left);
        return left;
    }

    fn parse_unary_expression(&mut self) -> &ASTExpression {
        if let Some(operator) = self.parse_unary_operator() {
            self.consume(); // consume unary operator token
            let operand = self.parse_unary_expression().id; // parse next unary expression
            return self.ast.unary_expression(operator, operand);
        }

        self.parse_primary_expression()
    }

    fn parse_unary_operator(&mut self) -> Option<ASTUnaryOperator> {
        let token = self.current();

        let kind = match token.kind {
            TokenKind::Minus => {
                Some(ASTUnaryOperatorKind::Negation)
            },
            TokenKind::Tilde => {
                Some(ASTUnaryOperatorKind::BitwiseNot)
            },
            _ => {
                None
            }
        };

        return kind.map(|kind| ASTUnaryOperator::new(kind, token.clone()));
    }

    fn parse_binary_operator(&mut self) -> Option<ASTBinaryOperator> {
        let token = self.current();

        let kind = match token.kind {
            // arithmetic operators
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
            TokenKind::DoubleAsterisk => {
                Some(ASTBinaryOperatorKind::Power)
            },
            // bitwise operators
            TokenKind::Ampersand => {
                Some(ASTBinaryOperatorKind::BitwiseAnd)
            },
            TokenKind::Pipe => {
                Some(ASTBinaryOperatorKind::BitwiseOr)
            },
            TokenKind::Caret => {
                Some(ASTBinaryOperatorKind::BitwiseXor)
            },
            // relational operators
            TokenKind::EqualsEquals => {
                Some(ASTBinaryOperatorKind::Equals)
            },
            TokenKind::NotEquals => {
                Some(ASTBinaryOperatorKind::NotEquals)
            },
            TokenKind::LessThan => {
                Some(ASTBinaryOperatorKind::LessThan)
            },
            TokenKind::GreaterThan => {
                Some(ASTBinaryOperatorKind::GreaterThan)
            },
            TokenKind::LessThanOrEqual => {
                Some(ASTBinaryOperatorKind::LessThanOrEqual)
            },
            TokenKind::GreaterThanOrEqual => {
                Some(ASTBinaryOperatorKind::GreaterThanOrEqual)
            },
            _ => None
        };
        return kind.map(|kind| ASTBinaryOperator::new(kind, token.clone()));
    }

    fn parse_primary_expression(&mut self) -> &ASTExpression { // for string literals, numbers, function calls
        let token = self.consume().clone();

        return match token.kind {
            TokenKind::Number(number) => {
                self.ast.number_expression(token, number)
            },
            TokenKind::LeftParen => {
                let expr = self.parse_expression().id; // because another exp in paren
                self.consume_and_check(TokenKind::RightParen);
                
                self.ast.parenthesised_expression(expr)
            },
            TokenKind::Identifier => {
                if self.current().kind == TokenKind::LeftParen {
                    self.parse_call_expression(token.clone())
                } else {
                    self.ast.variable_expression(token.clone())
                }
            },
            TokenKind::True | TokenKind::False => {
                let value = token.kind == TokenKind::True;
                self.ast.boolean_expression(token.clone(), value)
            }
            _ => {
                self.diagnostics_report.borrow_mut().report_expected_expression(&token);
                self.ast.error_expression(token.span.clone())
            }
        }
    }

    fn parse_call_expression(&mut self, identifier: Token) -> &ASTExpression {
        self.consume_and_check(TokenKind::LeftParen);
        let mut arguments = Vec::new();

        while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
            arguments.push(self.parse_expression().id);

            if self.current().kind != TokenKind::RightParen {
                self.consume_and_check(TokenKind::Comma);
            }
        }

        self.consume_and_check(TokenKind::RightParen);
        return self.ast.call_expression(identifier.clone(), arguments);
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