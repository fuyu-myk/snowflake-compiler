use crate::ast::{AssignmentOpKind, Ast, BinaryOp, BinaryOpAssociativity, BinaryOpKind, Body, ElseBranch, Expression, ExpressionId, ExpressionKind, FxReturnType, GenericParam, GenericParamKind, Generics, Item, ItemKind, Statement, StatementId, StaticTypeAnnotation, TypeKind, UnaryOp, UnaryOpKind, Pattern, BindingMode, Mutability};
use snowflake_common::text::span::TextSpan;
use snowflake_common::token::{Token, TokenKind};
use crate::compilation_unit::{resolve_type_from_string, resolve_type_kind, GlobalScope};
use snowflake_common::diagnostics::DiagnosticsReportCell;
use snowflake_common::typings::Type;
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
        self.consume_if(TokenKind::LineComment);
        self.consume_if(TokenKind::BlockComment);
        
        let statement = match self.current().kind {
            TokenKind::Let => self.parse_let_statement().id,
            TokenKind::Const => self.parse_const_statement().id,
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
            TokenKind::Const => self.parse_const_item(),
            _ => {
                let id = self.parse_statement();
                let span = self.ast.query_statement(id).span(self.ast);
                self.ast.item_from_kind(ItemKind::Statement(id), span)
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
        let generics = self.parse_optional_param_list();

        // parse body
        let return_type = self.parse_optional_return_type();
        let open_brace = self.consume_and_check(TokenKind::OpenBrace).clone();
        let mut body = Vec::new();
        while self.current().kind != TokenKind::CloseBrace && !self.is_at_end() {
            body.push(self.parse_statement());
        }
        let close_brace = self.consume_and_check(TokenKind::CloseBrace).clone();

        let body = Body::new(open_brace, body.clone(), close_brace);
        let resolved_return_type = return_type.clone().map(
            |return_type| resolve_type_kind(&self.diagnostics_report, &return_type.ty)
        ).unwrap_or(Type::Void);

        let fx_idx_result = self.global_scope.create_function(
            identifier.span.literal.clone(),
            body.clone(),
            generics.get_param_indices(),
            resolved_return_type,
        );

        let fx_idx = match fx_idx_result {
            Ok(created_fx_idx) => created_fx_idx,
            Err(existing_fx_idx) => {
                self.diagnostics_report.borrow_mut().report_function_already_declared(&identifier);
                existing_fx_idx
            }
        };

        self.ast.func_item(fx_keyword, identifier, generics, body, return_type, fx_idx)
    }

    fn parse_const_item(&mut self) -> &Item {
        self.consume_and_check(TokenKind::Const);
        let identifier = self.consume_and_check(TokenKind::Identifier).clone();
        let type_annotation = self.parse_optional_type_annotation();
        
        if type_annotation.is_none() {
            self.diagnostics_report.borrow_mut().report_const_missing_type(&identifier);
        }
        
        self.consume_and_check(TokenKind::Equals);
        let expr = self.parse_expression();
        self.consume_and_check(TokenKind::SemiColon);

        self.ast.constant_item(
            identifier.clone(), 
            Generics::empty(identifier.span.clone()),
            type_annotation.unwrap_or(
                StaticTypeAnnotation::new_simple(
                    Token {
                        kind: TokenKind::Colon,
                        span: TextSpan::default(),
                    },
                    Token {
                        kind: TokenKind::Identifier,
                        span: TextSpan::default(),
                    }
                )
            ),
            Some(Box::new(expr))
        )
    }

    fn parse_optional_return_type(&mut self) -> Option<FxReturnType> {
        if self.current().kind == TokenKind::Arrow {
            let arrow = self.consume_and_check(TokenKind::Arrow).clone();

            if self.current().kind == TokenKind::OpenBracket {
                // Array or slice return type
                let open_bracket = self.consume_and_check(TokenKind::OpenBracket).clone();
                let element_type = self.parse_type_kind();
                
                if self.current().kind == TokenKind::SemiColon {
                    // Array type
                    let semicolon = self.consume_and_check(TokenKind::SemiColon).clone();
                    // TODO: check if problematic 
                    let length = self.consume().clone(); // Length token (could be number or identifier)
                    let close_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
                    
                    return Some(FxReturnType::new(
                        arrow, 
                        vec![open_bracket.clone(), semicolon.clone(), length.clone(), close_bracket.clone()],
                        TypeKind::Array {
                            open_bracket,
                            element_type: Box::new(element_type),
                            semicolon,
                            length,
                            close_bracket,
                        }
                    ));
                } else {
                    // Slice type
                    let close_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
                    
                    return Some(FxReturnType::new(
                        arrow, 
                        vec![open_bracket.clone(), close_bracket.clone()],
                        TypeKind::Slice {
                            open_bracket,
                            element_type: Box::new(element_type),
                            close_bracket,
                        }
                    ));
                }
            } else if self.current().kind == TokenKind::LeftParen {
                // Tuple type
                let open_paren = self.consume_and_check(TokenKind::LeftParen).clone();
                let mut element_types = Vec::new();

                while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
                    element_types.push(Box::new(self.parse_type_kind()));

                    if self.current().kind != TokenKind::RightParen {
                        self.consume_and_check(TokenKind::Comma);
                    }
                }

                let close_paren = self.consume_and_check(TokenKind::RightParen).clone();

                return Some(FxReturnType::new(
                    arrow,
                    vec![open_paren.clone(), close_paren.clone()],
                    TypeKind::Tuple { open_paren, element_types, close_paren },
                ));
            } else {
                let type_name = vec![self.consume_and_check(TokenKind::Identifier).clone()];

                if let Some(type_token) = type_name.first() {
                    let type_kind = TypeKind::Simple { type_name: type_token.clone() };
                    return Some(FxReturnType::new(arrow, type_name, type_kind));
                }
            }
        }

        return None;
    }

    fn parse_optional_param_list(&mut self) -> Generics {
        if self.current().kind != TokenKind::LeftParen {
            return Generics::empty(TextSpan::default());
        }

        let left_paren = self.consume_and_check(TokenKind::LeftParen).clone();
        let mut generic_params = Vec::new();
        let mut all_spans = vec![left_paren.span.clone()];
        
        while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
            let identifier = self.consume_and_check(TokenKind::Identifier).clone();
            let type_annotation = self.parse_type_annotation();
            
            all_spans.push(identifier.span.clone());
            all_spans.extend(type_annotation.collect_spans());
            
            let ty = match &type_annotation.type_kind {
                TypeKind::Simple { type_name } => resolve_type_from_string(&self.diagnostics_report, type_name),
                _ => resolve_type_kind(&self.diagnostics_report, &type_annotation.type_kind)
            };
            
            let var_idx = self.global_scope.declare_variable(&identifier.span.literal, ty, false, false);
            
            let generic_param = GenericParam::new(
                var_idx,
                identifier.clone(),
                GenericParamKind::Type {
                    ty: Box::new(type_annotation.type_kind.clone()),
                    span: TextSpan::combine(type_annotation.collect_spans()),
                },
                Some(type_annotation.colon.clone()),
            );
            
            generic_params.push(generic_param);

            if self.current().kind == TokenKind::Comma {
                self.consume_and_check(TokenKind::Comma);
            }
        }

        let right_paren = self.consume_and_check(TokenKind::RightParen).clone();
        all_spans.push(right_paren.span.clone());
        
        let combined_span = if all_spans.is_empty() {
            TextSpan::default()
        } else {
            TextSpan::combine(all_spans)
        };
        
        Generics::new(generic_params, combined_span)
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

        self.ast.return_statement(&self.ast.clone(), return_keyword, expression)
    }

    fn parse_while_statement(&mut self) -> &Statement {
        let while_keyword = self.consume_and_check(TokenKind::While).clone();
        let condition_expr = self.parse_condition_expression();
        let body = self.parse_body();

        self.ast.while_statement(&self.ast.clone(), while_keyword, condition_expr, body)
    }

    fn parse_let_statement(&mut self) -> &Statement {
        self.consume_and_check(TokenKind::Let); // check 'let'
        let pattern = self.parse_pattern();
        
        let optional_type_annotation = self.parse_optional_type_annotation(); // check static type; e.g. a: int = ...
        self.consume_and_check(TokenKind::Equals); // check '='

        let expr = self.parse_expression();

        self.ast.let_statement_with_pattern(&self.ast.clone(), pattern, expr, optional_type_annotation)
    }

    fn parse_const_statement(&mut self) -> &Statement {
        self.consume_and_check(TokenKind::Const);
        let identifier = self.consume_and_check(TokenKind::Identifier).clone();
        
        let optional_type_annotation = self.parse_optional_type_annotation();
        if optional_type_annotation.is_none() {
            self.diagnostics_report.borrow_mut().report_const_missing_type(&identifier);
        }
        self.consume_and_check(TokenKind::Equals);

        let expr = self.parse_expression();

        self.ast.const_statement(&self.ast.clone(), identifier, expr, optional_type_annotation.unwrap_or(StaticTypeAnnotation::new_simple(
            Token {
                kind: TokenKind::Colon,
                span: TextSpan::default(),
            },
            Token {
                kind: TokenKind::Identifier,
                span: TextSpan::default(),
            }
        )))
    }

    fn parse_optional_type_annotation(&mut self) -> Option<StaticTypeAnnotation> {
        if self.current().kind == TokenKind::Colon {
            return Some(self.parse_type_annotation());
        }
        return None;
    }

    fn parse_type_annotation(&mut self) -> StaticTypeAnnotation {
        let colon = self.consume_and_check(TokenKind::Colon).clone();

        if self.current().kind == TokenKind::OpenBracket {
            return self.parse_array_or_slice_ty(colon);
        } else if self.current().kind == TokenKind::LeftParen {
            // Tuple type
            let open_paren = self.consume_and_check(TokenKind::LeftParen).clone();
            let mut element_types = Vec::new();

            while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
                element_types.push(self.parse_type_kind());

                if self.current().kind != TokenKind::RightParen {
                    self.consume_and_check(TokenKind::Comma);
                }
            }

            let close_paren = self.consume_and_check(TokenKind::RightParen).clone();
            return StaticTypeAnnotation::new_tuple(colon, open_paren, element_types, close_paren);
        } else {
            let type_name = self.consume_and_check(TokenKind::Identifier).clone();
            return StaticTypeAnnotation::new_simple(colon, type_name);
        }
    }

    fn parse_array_or_slice_ty(&mut self, colon: Token) -> StaticTypeAnnotation {
        let open_bracket = self.consume_and_check(TokenKind::OpenBracket).clone();
        let element_type = self.parse_type_kind();
        
        if self.current().kind == TokenKind::SemiColon {
            // Array type
            let semicolon = self.consume_and_check(TokenKind::SemiColon).clone();
            let length = self.consume().clone(); // Length token (could be number or identifier)
            let close_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
            
            return StaticTypeAnnotation::new_array(
                colon,
                open_bracket,
                element_type,
                semicolon,
                length,
                close_bracket
            );
        } else {
            // Slice type
            let close_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
            return StaticTypeAnnotation::new_slice(colon, open_bracket, element_type, close_bracket);
        }
    }

    fn parse_type_kind(&mut self) -> TypeKind {
        if self.current().kind == TokenKind::OpenBracket {
            // Nested array/slice type
            let open_bracket = self.consume_and_check(TokenKind::OpenBracket).clone();
            let element_type = self.parse_type_kind();
            
            if self.current().kind == TokenKind::SemiColon {
                // Array type
                let semicolon = self.consume_and_check(TokenKind::SemiColon).clone();
                let length = self.consume().clone(); // Length token
                let close_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
                
                return TypeKind::Array {
                    open_bracket,
                    element_type: Box::new(element_type),
                    semicolon,
                    length,
                    close_bracket,
                };
            } else {
                // Slice type
                let close_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
                return TypeKind::Slice {
                    open_bracket,
                    element_type: Box::new(element_type),
                    close_bracket,
                };
            }
        } else if self.current().kind == TokenKind::LeftParen {
            // Tuple type
            let open_paren = self.consume_and_check(TokenKind::LeftParen).clone();
            let mut element_types = Vec::new();

            while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
                element_types.push(Box::new(self.parse_type_kind()));

                if self.current().kind != TokenKind::RightParen {
                    self.consume_and_check(TokenKind::Comma);
                }
            }

            let close_paren = self.consume_and_check(TokenKind::RightParen).clone();
            return TypeKind::Tuple { open_paren, element_types, close_paren };
        } else {
            // Simple type
            let type_name = self.consume_and_check(TokenKind::Identifier).clone();
            return TypeKind::Simple { type_name };
        }
    }

    fn parse_expression_statement(&mut self) -> &Statement {
        let expr = self.parse_expression();
        self.ast.expression_statement(&self.ast.clone(), expr)
    }

    fn parse_condition_expression(&mut self) -> ExpressionId {
        //self.consume_and_check(TokenKind::LeftParen);
        let condition = self.parse_expression();
        //self.consume_and_check(TokenKind::RightParen);
        condition
    }

    fn parse_expression(&mut self) -> ExpressionId {
        return self.parse_assignment_expression();
    }

    fn parse_assignment_expression(&mut self) -> ExpressionId {
        let left_expr = self.parse_binary_expression();
        
        if self.current().kind == TokenKind::Equals {
            let equals = self.consume_and_check(TokenKind::Equals).clone();
            let right_expr = self.parse_assignment_expression(); // Right-recursive for right-associativity
            
            return self.ast.assignment_expression(left_expr, equals, right_expr).id;
        }
        
        left_expr
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

            left = self.ast.binary_expression(operator, left, right, false).id;
        }

        while let Some(assignment_op) = self.parse_assignment_operator() {
            let assignment_token = self.consume().clone();

            // Create compound binary expression instead of desugaring
            // This allows type checker to validate operands and generate proper errors
            let right = self.parse_binary_expression();
            
            left = self.ast.compound_binary_expression(assignment_op, assignment_token, left, right).id;
        }

        left
    }

    /// Parse assignment operators separately from binary operators
    fn parse_assignment_operator(&mut self) -> Option<AssignmentOpKind> {
        let token = self.current();

        match token.kind {
            TokenKind::PlusAs => Some(AssignmentOpKind::PlusAs),
            TokenKind::MinusAs => Some(AssignmentOpKind::MinusAs),
            TokenKind::AsteriskAs => Some(AssignmentOpKind::MultiplyAs),
            TokenKind::SlashAs => Some(AssignmentOpKind::DivideAs),
            TokenKind::ModuloAs => Some(AssignmentOpKind::ModuloAs),
            TokenKind::AmpersandAs => Some(AssignmentOpKind::BitwiseAndAs),
            TokenKind::PipeAs => Some(AssignmentOpKind::BitwiseOrAs),
            TokenKind::CaretAs => Some(AssignmentOpKind::BitwiseXorAs),
            TokenKind::ShiftLeftAs => Some(AssignmentOpKind::ShiftLeftAs),
            TokenKind::ShiftRightAs => Some(AssignmentOpKind::ShiftRightAs),
            _ => None,
        }
    }

    fn parse_unary_expression(&mut self) -> ExpressionId {
        if let Some(operator) = self.parse_unary_operator() {
            self.consume(); // consume unary operator token
            let operand = self.parse_unary_expression(); // parse next unary expression
            return self.ast.unary_expression(operator, operand).id;
        }

        self.parse_postfix_expression()
    }

    fn parse_postfix_expression(&mut self) -> ExpressionId {
        let mut expr = self.parse_primary_expression();

        loop {
            match self.current().kind {
                TokenKind::LeftParen => {
                    // Function call
                    let expr_kind = &self.ast.query_expression(expr).kind;
                    if let ExpressionKind::Variable(var_expr) = expr_kind {
                        let identifier = var_expr.identifier.clone();
                        expr = self.parse_call_expression(identifier);
                    } else {
                        // Not a simple identifier, can't call
                        break;
                    }
                }
                TokenKind::OpenBracket => {
                    // Array indexing
                    let open_bracket = self.consume().clone();
                    let index = self.parse_index_expression();
                    let close_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
                    expr = self.ast.index_expression(expr, open_bracket, index, close_bracket).id;
                }
                TokenKind::Period => {
                    // Tuple indexing
                    // TODO: match arms for future method or struct field access
                    let period = self.consume().clone();
                    let index = self.parse_primary_expression();
                    expr = self.ast.tuple_index_expression(expr, period, index).id;
                }
                _ => break,
            }
        }

        expr
    }

    fn parse_index_expression(&mut self) -> ExpressionId {
        let token = self.current().clone();
        
        match token.kind {
            TokenKind::Usize(value) => {
                self.consume();
                self.ast.usize_expression(token, value).id
            },
            TokenKind::Number(value) => {
                self.consume();
                self.ast.number_expression(token, value).id
            },
            TokenKind::Identifier => {
                self.parse_primary_expression()
            },
            TokenKind::LeftParen => {
                self.parse_primary_expression()
            },
            _ => {
                self.parse_assignment_expression()
            }
        }
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
            TokenKind::Modulo => Some(BinaryOpKind::Modulo),
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

    fn parse_array_expression(&mut self, type_decl: Token, left_brace: Token) -> &Expression {
        let mut elements = Vec::new();
        let mut commas = Vec::new();

        while self.current().kind != TokenKind::CloseBracket && !self.is_at_end() {
            elements.push(self.parse_expression());

            if self.current().kind != TokenKind::CloseBracket {
                let comma = self.consume_and_check(TokenKind::Comma).clone();
                commas.push(comma);
            }
        }

        let right_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
        self.ast.array_expression(type_decl, left_brace, elements, commas, right_bracket)
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
        let condition_expr = self.parse_condition_expression(); // parsing condition expression
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

    fn parse_primary_expression(&mut self) -> ExpressionId { // for string literals, numbers, function calls
        let token = self.consume().clone();

        return match &token.kind {
            TokenKind::Number(number) => self.ast.number_expression(token.clone(), *number),
            TokenKind::Float(number) => self.ast.float_expression(token.clone(), *number),
            TokenKind::Usize(number) => self.ast.usize_expression(token.clone(), *number),
            TokenKind::String(value) => self.ast.string_expression(token.clone(), value.clone()),
            TokenKind::LeftParen => {
                let left_paren = token.clone();
                let first_expr = self.parse_expression();
                
                // Check if this is a tuple (has comma) or parenthesized expression
                if self.current().kind == TokenKind::Comma {
                    // Tuple expr
                    let mut elements = vec![first_expr];
                    
                    while self.current().kind == TokenKind::Comma && !self.is_at_end() {
                        self.consume_and_check(TokenKind::Comma);
                        if self.current().kind != TokenKind::RightParen {
                            elements.push(self.parse_expression());
                        } else {
                            break; // Handle trailing comma
                        }
                    }
                    
                    let right_paren = self.consume_and_check(TokenKind::RightParen).clone();
                    self.ast.tuple_expression(left_paren, elements, right_paren)
                } else {
                    // Parenthesised expr
                    let right_paren = self.consume_and_check(TokenKind::RightParen).clone();
                    self.ast.parenthesised_expression(left_paren, first_expr, right_paren)
                }
            },
            TokenKind::Identifier => {
                if matches!(self.current().kind, TokenKind::LeftParen) {
                    return self.parse_call_expression(token.clone());
                }
                self.ast.variable_expression(token.clone())
            },
            TokenKind::True | TokenKind::False => {
                let value = token.kind == TokenKind::True;
                self.ast.boolean_expression(token.clone(), value)
            }
            TokenKind::If => self.parse_if_expression(token.clone()),
            TokenKind::OpenBrace => self.parse_block_expression(token.clone()),
            TokenKind::OpenBracket => {
                let type_decl = self.peek(-6).clone();
                self.parse_array_expression(type_decl, token.clone())
            }
            TokenKind::Break => self.ast.break_expression(token.clone()),
            TokenKind::Continue => self.ast.continue_expression(token.clone()),
            _ => {
                self.diagnostics_report.borrow_mut().report_expected_expression(&token);
                self.ast.error_expression(token.span)
            }
        }.id;
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

    // Pattern parsing methods
    
    /// Parse a pattern with optional mutability
    /// Handles: `mut identifier`, `identifier`, `(pattern, pattern)`, etc.
    fn parse_pattern(&mut self) -> Pattern {
        let start_span = self.current().span.clone();
        
        match self.current().kind {
            TokenKind::Mutable => {
                self.parse_binding_pattern_with_mut()
            }
            TokenKind::Identifier => {
                self.parse_identifier_pattern()
            }
            TokenKind::LeftParen => {
                self.parse_tuple_pattern()
            }
            _ => {
                self.diagnostics_report.borrow_mut().report_unexpected_token(&TokenKind::Identifier, &self.current());
                let token = self.current().clone();
                self.ast.error_pattern(start_span, token)
            }
        }
    }

    /// Parse a binding pattern that starts with `mut`
    /// Handles: `mut identifier`
    fn parse_binding_pattern_with_mut(&mut self) -> Pattern {
        self.consume_and_check(TokenKind::Mutable); // consume 'mut' token
        let identifier = self.consume_and_check(TokenKind::Identifier).clone();
        
        let binding_mode = BindingMode(Mutability::Mutable);
        self.ast.identifier_pattern(binding_mode, identifier)
    }

    /// Parse an identifier pattern (immutable binding)
    /// Handles: `identifier`
    fn parse_identifier_pattern(&mut self) -> Pattern {
        let identifier = self.consume_and_check(TokenKind::Identifier).clone();
        let binding_mode = BindingMode(Mutability::Immutable);
        
        self.ast.identifier_pattern(binding_mode, identifier)
    }

    /// Parse a tuple pattern
    /// Handles: `(pattern1, pattern2, ...)`
    fn parse_tuple_pattern(&mut self) -> Pattern {
        let left_paren = self.consume_and_check(TokenKind::LeftParen).clone();
        let mut patterns = Vec::new();
        
        while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
            patterns.push(Box::new(self.parse_pattern()));
            
            if self.current().kind != TokenKind::RightParen {
                self.consume_and_check(TokenKind::Comma);
            }
        }
        
        let right_paren = self.consume_and_check(TokenKind::RightParen).clone();
        let span = snowflake_common::text::span::TextSpan::combine_refs(&[&left_paren.span, &right_paren.span]);
        
        self.ast.tuple_pattern(patterns, span, left_paren)
    }

    fn consume_and_check(&self, kind: TokenKind) -> &Token {
        let token = self.consume();

        if token.kind != kind {
            self.diagnostics_report.borrow_mut().report_unexpected_token(
                &kind,
                &token,
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