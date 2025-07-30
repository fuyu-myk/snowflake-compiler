use crate::ast::{Ast, BinaryOp, BinaryOpAssociativity, BinaryOpKind, Body, ElseBranch, Expression, ExpressionId, FxDeclarationParams, FxReturnType, Item, ItemKind, Statement, StatementId, StaticTypeAnnotation, UnaryOp, UnaryOpKind};
use crate::ast::lexer::{Token, TokenKind};
use crate::compilation_unit::{resolve_type_from_string, GlobalScope};
use crate::diagnostics::DiagnosticsReportCell;
use crate::typings::Type;
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
    global_scope: &'a mut GlobalScope
}

impl <'a> Parser<'a> {
    pub fn new(
        tokens: Vec<Token>,
        diagnostics_report: DiagnosticsReportCell,
        ast: &'a mut Ast,
        global_scope: &'a mut GlobalScope,
    ) -> Self {
        Self { 
            tokens: tokens.iter()
                .filter(|token| token.kind != TokenKind::Whitespace)
                .map(|token| token.clone()).collect(), // filter whitespaces
            current: Counter::new(),
            diagnostics_report,
            ast,
            global_scope,
        }
    }

    pub fn parse(&mut self) {
        while let Some(_) = self.next_item().map(|statement| statement.id) {

        }
    }

    pub fn next_item(&mut self) -> Option<&Item> {
        if self.is_at_end() {
            return None;
        }

        Some(self.parse_item())
    }

    fn is_at_end(&self) -> bool {
        self.current().kind == TokenKind::Eof
    }

    fn parse_statement(&mut self) -> StatementId {
        let statement = match self.current().kind {
            TokenKind::Let => self.parse_let_statement().id,
            TokenKind::While => self.parse_while_statement().id,
            TokenKind::Return => self.parse_return_statement().id,
            _ => self.parse_expression_statement().id,
        };

        self.consume_if(TokenKind::SemiColon);
        statement
    }

    fn parse_item(&mut self) -> &Item {
        return match &self.current().kind {
            TokenKind::Function => self.parse_fx_item(),
            _ => {
                let id = self.parse_statement();
                self.ast.item_from_kind(ItemKind::Statement(id))
            }
        };
    }

    fn parse_body(&mut self) -> Body {
        let open_brace = self.consume_and_check(TokenKind::OpenBrace).clone();
        let mut body = Vec::new();
        while self.current().kind != TokenKind::CloseBrace && !self.is_at_end() {
            body.push(self.parse_statement());
        }
        let close_brace = self.consume_and_check(TokenKind::CloseBrace).clone();

        Body::new(open_brace, body, close_brace)
    }

    fn parse_fx_item(&mut self) -> &Item {
        // fx keyword & identifier
        let fx_keyword = self.consume_and_check(TokenKind::Function).clone();
        let identifier = self.consume_and_check(TokenKind::Identifier).clone();
        
        // parse params (optional)
        let parameters = self.parse_optional_param_list();

        // params as idx
        let params_idx = parameters.iter().map(|parameter| {
            let ty = resolve_type_from_string(&self.diagnostics_report, &parameter.type_annotation.type_name);
            self.global_scope.declare_variable(&parameter.identifier.span.literal, ty, false, false)
        }).collect();

        // parse body
        let return_type = self.parse_optional_return_type();
        let open_brace = self.consume_and_check(TokenKind::OpenBrace).clone();
        let mut body = Vec::new();
        while self.current().kind != TokenKind::CloseBrace && !self.is_at_end() {
            body.push(self.parse_statement());
        }
        let close_brace = self.consume_and_check(TokenKind::CloseBrace).clone();

        let body = Body::new(open_brace, body.clone(), close_brace);
        let fx_idx_result = self.global_scope.create_function(
            identifier.span.literal.clone(),
            body.clone(),
            params_idx,
            return_type.clone().map(|return_type| resolve_type_from_string(&self.diagnostics_report, &return_type.type_name)).unwrap_or(Type::Void)
        );

        let fx_idx = match fx_idx_result {
            Ok(created_fx_idx) => created_fx_idx,
            Err(existing_fx_idx) => {
                self.diagnostics_report.borrow_mut().report_function_already_declared(&identifier);
                existing_fx_idx
            }
        };

        self.ast.func_item(fx_keyword, identifier, parameters, body, return_type, fx_idx)
    }

    fn parse_optional_return_type(&mut self) -> Option<FxReturnType> {
        if self.current().kind == TokenKind::Arrow {
            let arrow = self.consume_and_check(TokenKind::Arrow).clone();
            let type_name = self.consume_and_check(TokenKind::Identifier).clone();

            return Some(FxReturnType::new(arrow, type_name));
        }
        return None;
    }

    fn parse_optional_param_list(&mut self) -> Vec<FxDeclarationParams> {
        if self.current().kind != TokenKind::LeftParen {
            return Vec::new();
        }

        self.consume_and_check(TokenKind::LeftParen);
        let mut parameters = Vec::new();
        while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
            parameters.push(FxDeclarationParams {
                identifier: self.consume_and_check(TokenKind::Identifier).clone(),
                type_annotation: self.parse_type_annotation(),
            });

            if self.current().kind == TokenKind::Comma {
                self.consume_and_check(TokenKind::Comma);
            }
        }

        self.consume_and_check(TokenKind::RightParen);
        parameters
    }

    fn parse_return_statement(&mut self) -> &Statement {
        let return_keyword = self.consume_and_check(TokenKind::Return).clone();
        
        let expression = if self.current().kind == TokenKind::SemiColon || 
                           self.current().kind == TokenKind::CloseBrace ||
                           self.is_at_end() {
            None
        } else {
            Some(self.parse_expression())
        };

        self.ast.return_statement(return_keyword, expression)
    }

    fn parse_while_statement(&mut self) -> &Statement {
        let while_keyword = self.consume_and_check(TokenKind::While).clone();
        let condition_expr = self.parse_expression();
        let body = self.parse_body();

        self.ast.while_statement(while_keyword, condition_expr, body)
    }

    fn parse_block_expression(&mut self, left_brace: Token) -> &Expression {
        let mut statements = Vec::new();

        while self.current().kind != TokenKind::CloseBrace && !self.is_at_end() {
            statements.push(self.parse_statement());
        }

        let right_brace = self.consume_and_check(TokenKind::CloseBrace).clone();
        self.ast.block_expression(left_brace, statements, right_brace)
    }

    fn parse_if_expression(&mut self, if_keyword: Token) -> &Expression {
        let condition_expr = self.parse_expression(); // parsing condition expression
        let then = self.parse_body(); // parsing 'then' statement
        let else_statement = self.parse_optional_else_statement(); // if there is an 'else' statement, parse it

        self.ast.if_expression(if_keyword, condition_expr, then, else_statement)
    }

    fn parse_optional_else_statement(&mut self) -> Option<ElseBranch> {
        if self.current().kind == TokenKind::Else {
            let else_keyword = self.consume_and_check(TokenKind::Else).clone(); // checks for 'else'
            let else_expression = self.parse_body(); // parsing 'else' statement
            return Some(ElseBranch::new(else_keyword, else_expression));
        }

        None
    }

    fn parse_let_statement(&mut self) -> &Statement {
        self.consume_and_check(TokenKind::Let); // check 'let'
        let identifier = self.consume_and_check(TokenKind::Identifier).clone(); // check variable
        let optional_type_annotation = self.parse_optional_type_annotation(); // check static type; e.g. a: int = ...
        self.consume_and_check(TokenKind::Equals); // check '='

        let expr = self.parse_expression();

        self.ast.let_statement(identifier, expr, optional_type_annotation)
    }

    fn parse_optional_type_annotation(&mut self) -> Option<StaticTypeAnnotation> {
        if self.current().kind == TokenKind::Colon {
            return Some(self.parse_type_annotation());
        }
        return None;
    }

    fn parse_type_annotation(&mut self) -> StaticTypeAnnotation {
        let colon = self.consume_and_check(TokenKind::Colon).clone();
        let type_name = self.consume_and_check(TokenKind::Identifier).clone();

        return StaticTypeAnnotation::new(colon, type_name);
    }

    fn parse_expression_statement(&mut self) -> &Statement {
        let expr = self.parse_expression();
        self.ast.expression_statement(expr)
    }

    fn parse_expression(&mut self) -> ExpressionId {
        return self.parse_assignment_expression();
    }

    fn parse_assignment_expression(&mut self) -> ExpressionId {
        if self.current().kind == TokenKind::Identifier {
            if self.peek(1).kind == TokenKind::Equals {
                let identifier = self.consume_and_check(TokenKind::Identifier).clone();
                let equals = self.consume_and_check(TokenKind::Equals).clone();
                let expr = self.parse_expression();

                return self.ast.assignment_expression(identifier, equals, expr).id;
            }
        }
        return self.parse_binary_expression();
    }

    fn parse_binary_expression(&mut self) -> ExpressionId {
        let left = self.parse_unary_expression(); // parsing pri exp (only no.s for now)
        self.parse_binary_expression_recurse(left, 0)
    }

    fn parse_binary_expression_recurse(&mut self, mut left: ExpressionId, precedence: u8) -> ExpressionId {
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

            let mut right = self.parse_unary_expression();

            while let Some(inner_operator) = self.parse_binary_operator() {
                let greater_precedence = inner_operator.precedence() > operator.precedence();
                let equal_precedence = inner_operator.precedence() == operator.precedence();

                if !greater_precedence && !(equal_precedence && inner_operator.associativity() == BinaryOpAssociativity::Right) {
                    break;
                }

                right = self.parse_binary_expression_recurse(right, std::cmp::max(operator.precedence(), inner_operator.precedence()));
            }

            left = self.ast.binary_expression(operator, left, right).id;
        }

        left
    }

    fn parse_unary_expression(&mut self) -> ExpressionId {
        if let Some(operator) = self.parse_unary_operator() {
            self.consume(); // consume unary operator token
            let operand = self.parse_unary_expression(); // parse next unary expression
            return self.ast.unary_expression(operator, operand).id;
        }

        self.parse_primary_expression()
    }

    fn parse_unary_operator(&mut self) -> Option<UnaryOp> {
        let token = self.current();

        let kind = match token.kind {
            TokenKind::Minus => Some(UnaryOpKind::Negation),
            TokenKind::Tilde => Some(UnaryOpKind::BitwiseNot),
            _ => None,
        };

        return kind.map(|kind| UnaryOp::new(kind, token.clone()));
    }

    fn parse_binary_operator(&mut self) -> Option<BinaryOp> {
        let token = self.current();

        let kind = match token.kind {
            // arithmetic operators
            TokenKind::Plus => Some(BinaryOpKind::Plus),
            TokenKind::Minus => Some(BinaryOpKind::Minus),
            TokenKind::Asterisk => Some(BinaryOpKind::Multiply),
            TokenKind::Slash => Some(BinaryOpKind::Divide),
            TokenKind::DoubleAsterisk => Some(BinaryOpKind::Power),

            // bitwise operators
            TokenKind::Ampersand => Some(BinaryOpKind::BitwiseAnd),
            TokenKind::Pipe => Some(BinaryOpKind::BitwiseOr),
            TokenKind::Caret => Some(BinaryOpKind::BitwiseXor),
            TokenKind::ShiftLeft => Some(BinaryOpKind::ShiftLeft),
            TokenKind::ShiftRight => Some(BinaryOpKind::ShiftRight),

            // relational operators
            TokenKind::EqualsEquals => Some(BinaryOpKind::Equals),
            TokenKind::NotEquals => Some(BinaryOpKind::NotEquals),
            TokenKind::LessThan => Some(BinaryOpKind::LessThan),
            TokenKind::GreaterThan => Some(BinaryOpKind::GreaterThan),
            TokenKind::LessThanOrEqual => Some(BinaryOpKind::LessThanOrEqual),
            TokenKind::GreaterThanOrEqual => Some(BinaryOpKind::GreaterThanOrEqual),
            _ => None,
        };
        return kind.map(|kind| BinaryOp::new(kind, token.clone()));
    }

    fn parse_primary_expression(&mut self) -> ExpressionId { // for string literals, numbers, function calls
        let token = self.consume().clone();

        return match token.kind {
            TokenKind::Number(number) => self.ast.number_expression(token, number),
            TokenKind::LeftParen => {
                let left_paren = token;
                let expr = self.parse_expression(); // because another exp in paren
                let right_paren = self.consume_and_check(TokenKind::RightParen).clone();
                
                self.ast.parenthesised_expression(left_paren, expr, right_paren)
            },
            TokenKind::Identifier => {
                if matches!(self.current().kind, TokenKind::LeftParen) {
                    return self.parse_call_expression(token);
                }
                self.ast.variable_expression(token)
            },
            TokenKind::True | TokenKind::False => {
                let value = token.kind == TokenKind::True;
                self.ast.boolean_expression(token.clone(), value)
            }
            TokenKind::If => self.parse_if_expression(token),
            TokenKind::OpenBrace => self.parse_block_expression(token),
            _ => {
                self.diagnostics_report.borrow_mut().report_expected_expression(&token);
                self.ast.error_expression(token.span)
            }
        }.id;
    }

    fn parse_call_expression(&mut self, identifier: Token) -> ExpressionId {
        let left_paren = self.consume_and_check(TokenKind::LeftParen).clone();
        let mut arguments = Vec::new();

        while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
            arguments.push(self.parse_expression());

            if self.current().kind != TokenKind::RightParen {
                self.consume_and_check(TokenKind::Comma);
            }
        }

        let right_paren = self.consume_and_check(TokenKind::RightParen).clone();
        return self.ast.call_expression(identifier, left_paren, arguments, right_paren).id;
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

    fn consume_if(&self, kind: TokenKind) -> Option<&Token> {
        if self.current().kind == kind {
            Some(self.consume())
        } else {
            None
        }
    }
}