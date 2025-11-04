use crate::ast::{AssignmentOpKind, AssociatedItem, Ast, AstType, BinaryOp, BinaryOpAssociativity, BinaryOpKind, BindingMode, BlockExpression, ElseBranch, ExprField, ExprIndex, Expression, ExpressionKind, FieldDefinition, FxReturnType, GenericParam, GenericParamKind, Generics, Item, ItemIndex, ItemKind, Mutability, Path, PathSegment, Pattern, PatternKind, SelfParam, Statement, StatementKind, StaticTypeAnnotation, StmtIndex, UnaryOp, UnaryOpKind, Variant, VariantData};
use snowflake_common::text::span::TextSpan;
use snowflake_common::token::{Token, TokenKind};
use snowflake_common::{bug_report, Idx};
use crate::compilation_unit::{GlobalScope};
use snowflake_common::diagnostics::DiagnosticsReportCell;
use snowflake_common::typings::TypeKind;
use std::cell::Cell;
use std::vec;


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
    global_scope: &'a mut GlobalScope,
    function_depth: usize,
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
                .filter(|token| {
                    token.kind != TokenKind::Whitespace && 
                    token.kind != TokenKind::LineComment && 
                    token.kind != TokenKind::BlockComment
                })
                .map(|token| token.clone()).collect(), // filter whitespaces and comments
            current: Counter::new(),
            diagnostics_report,
            ast,
            global_scope,
            function_depth: 0,
        }
    }

    pub fn parse(&mut self) {
        while let Some(_) = self.next_item().map(|item| item.id) {

        }
    }

    pub fn next_item(&mut self) -> Option<&Item<ItemKind>> {
        if self.is_at_end() {
            return None;
        }

        match self.parse_item() {
            Ok(item) => Some(item),
            Err(_) => None,
        }
    }

    fn is_at_end(&self) -> bool {
        self.current().kind == TokenKind::Eof
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

    fn parse_statement(&mut self) -> StmtIndex {
        let statement = match self.current().kind {
            TokenKind::Let => {
                let stmt = self.parse_let_statement().id;
                self.consume_and_check(TokenKind::SemiColon);
                return stmt;
            }
            TokenKind::Const => {
                let stmt = self.parse_const_statement().id;
                self.consume_and_check(TokenKind::SemiColon);
                return stmt;
            }
            TokenKind::Function => {
                let item = match self.parse_fx_item(false) {
                    Ok(fx_item) => fx_item,
                    Err(_) => bug_report!("Expected function item, got associated item"),
                };
                let item_id = item.id;
                let span = item.span.clone();
                self.ast.statement_from_kind(StatementKind::Item(item_id), span).id
            }
            TokenKind::Struct => {
                let item = self.parse_struct_item();
                let item_id = item.id;
                let span = item.span.clone();
                self.ast.statement_from_kind(StatementKind::Item(item_id), span).id
            }
            _ => {
                let expr = self.parse_expression();
                let has_semicolon = self.current().kind == TokenKind::SemiColon;

                if has_semicolon {
                    self.consume();
                    self.ast.statement_from_kind(
                        StatementKind::SemiExpression(expr),
                        self.ast.query_expression(expr).span(&self.ast),
                    ).id
                } else {
                    self.ast.statement_from_kind(
                        StatementKind::Expression(expr),
                        self.ast.query_expression(expr).span(&self.ast),
                    ).id
                }
            }
        };

        statement
    }

    fn parse_item(&mut self) -> Result<&Item<ItemKind>, ()> {
        return match &self.current().kind {
            TokenKind::Function => match self.parse_fx_item(false) {
                Ok(fx_item) => Ok(fx_item),
                Err(_) => bug_report!("Expected function item, got associated item"),
            },
            TokenKind::Const => match self.parse_const_item(false) {
                Ok(const_item) => Ok(const_item),
                Err(_) => bug_report!("Expected constant item, got associated item"),
            }
            TokenKind::Struct => Ok(self.parse_struct_item()),
            TokenKind::Enum => Ok(self.parse_enum_item()),
            TokenKind::Impl => Ok(self.parse_impl_item()),
            _ => {
                Err(self.diagnostics_report.borrow_mut().report_expected_item(self.current()))
            }
        };
    }

    fn parse_body(&mut self) -> BlockExpression {
        let open_brace = self.consume_and_check(TokenKind::OpenBrace).clone();
        let mut body = Vec::new();
        let mut spans = vec![open_brace.span.clone()];

        while self.current().kind != TokenKind::CloseBrace && !self.is_at_end() {
            body.push(self.parse_statement());

            if self.current().kind == TokenKind::CloseBrace {
                break;
            }
        }

        for statement in body.iter() {
            let stmt_span = self.ast.query_statement(*statement).span.clone();
            spans.push(stmt_span);
        }

        let close_brace = self.consume_and_check(TokenKind::CloseBrace).clone();
        spans.push(close_brace.span.clone());
        
        let span = TextSpan::combine(spans);

        BlockExpression::new(open_brace, body, close_brace, span)
    }

    fn parse_fx_item(&mut self, is_associated: bool) -> Result<&Item<ItemKind>, &AssociatedItem> {
        let mut spans = vec![];

        // fx keyword & identifier
        let fx_keyword = self.consume_and_check(TokenKind::Function).clone();
        let identifier = self.consume_and_check(TokenKind::Identifier).clone();
        
        // parse params (optional)
        let (generics, self_param) = self.parse_optional_param_list();

        let return_type = self.parse_optional_return_type();

        // parse body
        self.function_depth += 1;

        let body = self.parse_body();
        spans.push(body.span.clone());

        self.function_depth -= 1;

        let resolved_return_type = return_type.clone().map(
            |return_type| {
                match &return_type.ty {
                    AstType::Simple { type_name } => TypeKind::from_token(type_name),
                    _ => TypeKind::Void // Will be properly resolved in the resolution phase
                }
            }
        ).unwrap_or(TypeKind::Void);

        let fx_idx = if is_associated {
            // Placeholder, will be registered during resolution phase
            ItemIndex::unreachable()
        } else {
            let fx_idx_result = self.global_scope.create_function(
                identifier.span.literal.clone(),
                body.clone(),
                generics.get_param_indices(),
                resolved_return_type,
            );

            match fx_idx_result {
                Ok(created_fx_idx) => created_fx_idx,
                Err(existing_fx_idx) => {
                    self.diagnostics_report.borrow_mut().report_function_already_declared(&identifier);
                    existing_fx_idx
                }
            }
        };

        if is_associated {
            return Err(self.ast.assoc_func_item(fx_keyword, identifier, generics, self_param, body, return_type, fx_idx))
        }

        Ok(self.ast.func_item(fx_keyword, identifier, generics, self_param, body, return_type, fx_idx))
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
                    let length = self.consume().clone(); // Length token (could be number or identifier)
                    let close_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
                    
                    return Some(FxReturnType::new(
                        arrow, 
                        vec![open_bracket.clone(), semicolon.clone(), length.clone(), close_bracket.clone()],
                        AstType::Array {
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
                        AstType::Slice {
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
                    AstType::Tuple { open_paren, element_types, close_paren },
                ));
            } else {
                // Accept either Identifier or SelfType for type names
                let type_token = if self.current().kind == TokenKind::SelfType {
                    self.consume_and_check(TokenKind::SelfType).clone()
                } else {
                    self.consume_and_check(TokenKind::Identifier).clone()
                };
                let type_name = vec![type_token.clone()];

                let type_kind = AstType::Simple { type_name: type_token };
                return Some(FxReturnType::new(arrow, type_name, type_kind));
            }
        }

        return None;
    }

    fn parse_optional_param_list(&mut self) -> (Generics, Option<SelfParam>) {
        if self.current().kind != TokenKind::LeftParen {
            return (Generics::empty(TextSpan::default()), None);
        }

        let left_paren = self.consume_and_check(TokenKind::LeftParen).clone();
        let mut generic_params = Vec::new();
        let mut all_spans = vec![left_paren.span.clone()];
        let mut self_param = None;
        
        // Check for self parameter first
        if self.current().kind == TokenKind::Mutable && self.peek(1).kind == TokenKind::SelfValue {
            self.consume_and_check(TokenKind::Mutable);
            let self_token = self.consume_and_check(TokenKind::SelfValue).clone();
            self_param = Some(SelfParam {
                mutability: Mutability::Mutable,
                token: self_token,
            });
            
            if self.current().kind == TokenKind::Comma {
                self.consume_and_check(TokenKind::Comma);
            }
        } else if self.current().kind == TokenKind::SelfValue {
            let self_token = self.consume_and_check(TokenKind::SelfValue).clone();
            self_param = Some(SelfParam {
                mutability: Mutability::Immutable,
                token: self_token,
            });
            
            if self.current().kind == TokenKind::Comma {
                self.consume_and_check(TokenKind::Comma);
            }
        }
        
        while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
            let identifier = self.consume_and_check(TokenKind::Identifier).clone();
            let type_annotation = self.parse_type_annotation();
            
            all_spans.push(identifier.span.clone());
            all_spans.extend(type_annotation.collect_spans());
            
            let ty = match &type_annotation.type_kind {
                AstType::Simple { type_name } => TypeKind::from_token(type_name),
                _ => TypeKind::Void,
            };
            
            let var_idx = self.global_scope.declare_variable(
                &Path {
                    span: identifier.span.clone(),
                    segments: vec![
                        PathSegment {
                            identifier: identifier.clone(),
                            arguments: None,
                        }
                    ],
                    tokens: vec![identifier.clone()],
                },
                ty,
                false,
                false,
            );
            
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
        
        (Generics::new(generic_params, combined_span), self_param)
    }

    fn parse_const_item(&mut self, is_associated: bool) -> Result<&Item<ItemKind>, &AssociatedItem> {
        self.consume_and_check(TokenKind::Const);
        let identifier = self.consume_and_check(TokenKind::Identifier).clone();
        let type_annotation = self.parse_optional_type_annotation();
        
        if type_annotation.is_none() {
            self.diagnostics_report.borrow_mut().report_const_missing_type(&identifier);
        }
        
        self.consume_and_check(TokenKind::Equals);
        let expr = self.parse_expression();
        self.consume_and_check(TokenKind::SemiColon);

        let ident = Pattern {
            id: StmtIndex::new(0),
            kind: PatternKind::Identifier(BindingMode(Mutability::Immutable), identifier.clone()),
            span: identifier.span.clone(),
            token: identifier.clone(),
        };

        let type_annot = type_annotation.unwrap_or(
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
        );

        if is_associated {
            return Err(self.ast.assoc_constant_item(ident, Generics::empty(identifier.span.clone()), type_annot, Some(Box::new(expr))));
        }

        Ok(self.ast.constant_item(ident, Generics::empty(identifier.span.clone()), type_annot, Some(Box::new(expr))))
    }

    fn parse_struct_item(&mut self) -> &Item<ItemKind> {
        self.consume_and_check(TokenKind::Struct);
        let identifier = self.consume_and_check(TokenKind::Identifier).clone();

        let generics = if self.current().kind == TokenKind::LessThan {
            self.parse_generic_params()
        } else {
            Generics::new(Vec::new(), TextSpan::default())
        };

        let variant_data = if self.current().kind == TokenKind::OpenBrace {
            self.parse_struct_variant_data()
        } else if self.current().kind == TokenKind::LeftParen {
            let data = self.parse_tuple_variant_data();
            self.consume_and_check(TokenKind::SemiColon);
            data
        } else {
            self.consume_and_check(TokenKind::SemiColon);
            VariantData::Unit
        };
        
        let is_local = self.function_depth > 0;
        
        self.ast.struct_item_local(identifier, generics, variant_data, is_local)
    }

    /// Parse generic parameters like `<T, U>`
    fn parse_generic_params(&mut self) -> Generics {
        self.consume_and_check(TokenKind::LessThan);
        let mut generic_params = Vec::new();
        let mut all_spans = Vec::new();

        if self.current().kind != TokenKind::GreaterThan {
            loop {
                let identifier = self.consume_and_check(TokenKind::Identifier).clone();
                all_spans.push(identifier.span.clone());

                // TODO: Add support for bounds like T: Clone
                let var_idx = self.global_scope.declare_variable(
                    &Path {
                        span: identifier.span.clone(),
                        segments: vec![
                            PathSegment {
                                identifier: identifier.clone(),
                                arguments: None,
                            }
                        ],
                        tokens: vec![identifier.clone()],
                    }, 
                    TypeKind::Unresolved, // Use Unresolved for generic type parameters for now
                    false, 
                    false
                );

                let generic_param = GenericParam::new(
                    var_idx,
                    identifier.clone(),
                    GenericParamKind::Type {
                        ty: Box::new(AstType::Simple { 
                            type_name: Token::new(TokenKind::Identifier, TextSpan::default())
                        }),
                        span: TextSpan::default(),
                    },
                    None,
                );
                generic_params.push(generic_param);

                if self.current().kind == TokenKind::Comma {
                    let comma_token = self.consume_and_check(TokenKind::Comma);
                    all_spans.push(comma_token.span.clone());
                } else {
                    break;
                }
            }
        }

        let close_token = self.consume_and_check(TokenKind::GreaterThan);
        all_spans.push(close_token.span.clone());

        Generics::new(generic_params, TextSpan::combine(all_spans))
    }

    /// Parse fields like `{ field1: type1, field2: type2 }`
    fn parse_struct_variant_data(&mut self) -> VariantData {
        self.consume_and_check(TokenKind::OpenBrace);
        let mut fields = Vec::new();

        while self.current().kind != TokenKind::CloseBrace && !self.is_at_end() {
            let field_name = self.consume_and_check(TokenKind::Identifier).clone();
            let type_annotation = self.parse_type_annotation();

            let field_def = FieldDefinition::new(
                Some(field_name),
                Box::new(type_annotation.type_kind.clone()),
            );
            fields.push(field_def);

            if self.current().kind == TokenKind::Comma {
                self.consume_and_check(TokenKind::Comma);
            } else if self.current().kind != TokenKind::CloseBrace {
                self.diagnostics_report.borrow_mut().report_unexpected_token_two(
                    &TokenKind::Comma,
                    &TokenKind::CloseBrace,
                    &self.current()
                );
            }
        }

        self.consume_and_check(TokenKind::CloseBrace);
        VariantData::Struct { fields }
    }

    fn parse_tuple_variant_data(&mut self) -> VariantData {
        self.consume_and_check(TokenKind::LeftParen);
        let mut field_defs = Vec::new();

        while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
            let ty = self.parse_type_kind();
            let field_def = FieldDefinition::new(
                None,
                Box::new(ty),
            );
            field_defs.push(field_def);

            if self.current().kind == TokenKind::Comma {
                self.consume_and_check(TokenKind::Comma);
            } else {
                break;
            }
        }

        self.consume_and_check(TokenKind::RightParen);
        VariantData::Tuple(field_defs)
    }

    fn parse_enum_item(&mut self) -> &Item<ItemKind> {
        self.consume_and_check(TokenKind::Enum);
        let identifier = self.consume_and_check(TokenKind::Identifier).clone();

        let generics = if self.current().kind == TokenKind::LessThan {
            self.parse_generic_params()
        } else {
            Generics::new(Vec::new(), TextSpan::default())
        };

        let variants = self.parse_variants();


        if self.function_depth > 0 {
            self.diagnostics_report.borrow_mut().report_enum_in_function(&identifier);
        }

        self.ast.enum_item(identifier, generics, variants)
    }

    fn parse_variants(&mut self) -> Vec<Variant> {
        let mut variants = Vec::new();
        self.consume_and_check(TokenKind::OpenBrace);

        while self.current().kind != TokenKind::CloseBrace && !self.is_at_end() {
            let variant_name = self.consume_and_check(TokenKind::Identifier).clone();
            let variant_data = if self.current().kind == TokenKind::OpenBrace {
                self.parse_struct_variant_data()
            } else if self.current().kind == TokenKind::LeftParen {
                self.parse_tuple_variant_data()
            } else {
                VariantData::Unit
            };

            variants.push(
                Variant {
                    identifier: variant_name,
                    data: variant_data
                }
            );

            if self.current().kind == TokenKind::Comma {
                self.consume_and_check(TokenKind::Comma);
            } else if self.current().kind != TokenKind::CloseBrace {
                self.diagnostics_report.borrow_mut().report_unexpected_token_two(
                    &TokenKind::Comma,
                    &TokenKind::CloseBrace,
                    &self.current()
                );
            }
        }
        
        self.consume_and_check(TokenKind::CloseBrace);

        variants
    }

    fn parse_impl_item(&mut self) -> &Item<ItemKind> {
        let mut generic_after_impl = false;
        let mut generic_after_type_name = false;

        self.consume_and_check(TokenKind::Impl);

        let generics_impl = if self.current().kind == TokenKind::LessThan {
            generic_after_impl = true;
            self.parse_generic_params()
        } else {
            Generics::new(Vec::new(), TextSpan::default())
        };

        let type_name = self.consume_and_check(TokenKind::Identifier).clone();

        let generics = if generic_after_impl {
            generic_after_type_name = true;
            self.parse_generic_params()
        } else {
            Generics::new(Vec::new(), TextSpan::default())
        };

        if (generic_after_impl && !generic_after_type_name) || (!generic_after_impl && generic_after_type_name) {
            let generics_span = if generic_after_impl {
                generics_impl.span
            } else {
                generics.span.clone()
            };

            self.diagnostics_report.borrow_mut().report_missing_impl_generics(
                generic_after_impl,
                generic_after_type_name,
                &generics_span,
                &type_name.span.literal,
            );
        }

        let type_path = self.parse_path(type_name.clone());
        self.consume_and_check(TokenKind::OpenBrace);
        let mut items = Vec::new();

        while self.current().kind != TokenKind::CloseBrace && !self.is_at_end() {
            let item = if self.current().kind == TokenKind::Function {
                self.parse_fx_item(true)
            } else if self.current().kind == TokenKind::Const {
                self.parse_const_item(true)
            } else {
                self.diagnostics_report.borrow_mut().report_expected_item(self.current());
                break;
            };

            let item_unwrapped = match item {
                Ok(_) => bug_report!("Expected associated item, got non-associated item"),
                Err(assoc_item) => assoc_item,
            };

            items.push(item_unwrapped.clone());
        }

        self.consume_and_check(TokenKind::CloseBrace);
        self.ast.impl_item(type_path, generics, items)
    }

    fn parse_let_statement(&mut self) -> &Statement {
        self.consume_and_check(TokenKind::Let); // check 'let'
        let pattern = self.parse_pattern();
        
        let optional_type_annotation = self.parse_optional_type_annotation(); // check static type; e.g. a: int = ...
        self.consume_and_check(TokenKind::Equals); // check '='

        let expr = self.parse_expression();

        self.ast.let_statement(&self.ast.clone(), pattern, expr, optional_type_annotation)
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

    fn parse_type_kind(&mut self) -> AstType {
        if self.current().kind == TokenKind::OpenBracket {
            // Nested array/slice type
            let open_bracket = self.consume_and_check(TokenKind::OpenBracket).clone();
            let element_type = self.parse_type_kind();
            
            if self.current().kind == TokenKind::SemiColon {
                // Array type
                let semicolon = self.consume_and_check(TokenKind::SemiColon).clone();
                let length = self.consume().clone(); // Length token
                let close_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
                
                return AstType::Array {
                    open_bracket,
                    element_type: Box::new(element_type),
                    semicolon,
                    length,
                    close_bracket,
                };
            } else {
                // Slice type
                let close_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
                return AstType::Slice {
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
            return AstType::Tuple { open_paren, element_types, close_paren };
        } else {
            // Simple type
            let type_name = self.consume_and_check(TokenKind::Identifier).clone();
            return AstType::Simple { type_name };
        }
    }

    fn parse_condition_expression(&mut self) -> ExprIndex {
        self.parse_expression_in_context(false)
    }

    fn parse_expression(&mut self) -> ExprIndex {
        return self.parse_expression_in_context(true);
    }

    fn parse_expression_in_context(&mut self, allow_struct_expr: bool) -> ExprIndex {
        return self.parse_assignment_expression_in_context(allow_struct_expr);
    }

    fn parse_assignment_expression_in_context(&mut self, allow_struct_expr: bool) -> ExprIndex {
        let left_expr = self.parse_binary_expression(allow_struct_expr);
        
        if self.current().kind == TokenKind::Equals {
            let equals = self.consume_and_check(TokenKind::Equals).clone();
            let right_expr = self.parse_assignment_expression_in_context(allow_struct_expr); // Right-recursive for right-associativity
            
            return self.ast.assignment_expression(left_expr, equals, right_expr).id;
        }
        
        left_expr
    }

    fn parse_binary_expression(&mut self, allow_struct_expr: bool) -> ExprIndex {
        let left = self.parse_unary_expression(allow_struct_expr);
        self.parse_binary_expression_recurse(left, 0, allow_struct_expr)
    }

    fn parse_binary_expression_recurse(&mut self, mut left: ExprIndex, precedence: u8, allow_struct_expr: bool) -> ExprIndex {
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

            let mut right = self.parse_unary_expression(allow_struct_expr);

            while let Some(inner_operator) = self.parse_binary_operator() {
                let greater_precedence = inner_operator.precedence() > operator.precedence();
                let equal_precedence = inner_operator.precedence() == operator.precedence();

                if !greater_precedence && !(equal_precedence && inner_operator.associativity() == BinaryOpAssociativity::Right) {
                    break;
                }

                right = self.parse_binary_expression_recurse(
                    right,
                    std::cmp::max(operator.precedence(),
                    inner_operator.precedence()),
                    allow_struct_expr
                );
            }

            left = self.ast.binary_expression(operator, left, right, false).id;
        }

        while let Some(assignment_op) = self.parse_assignment_operator() {
            let assignment_token = self.consume().clone();

            // Create compound binary expression instead of desugaring
            // This allows type checker to validate operands and generate proper errors
            let right = self.parse_binary_expression(allow_struct_expr);
            
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

    fn parse_unary_expression(&mut self, allow_struct_expr: bool) -> ExprIndex {
        if let Some(operator) = self.parse_unary_operator() {
            self.consume(); // consume unary operator token
            let operand = self.parse_unary_expression(allow_struct_expr); // parse next unary expression
            return self.ast.unary_expression(operator, operand).id;
        }

        self.parse_postfix_expression(allow_struct_expr)
    }

    fn parse_postfix_expression(&mut self, allow_struct_expr: bool) -> ExprIndex {
        let mut expr = self.parse_primary_expression_in_context(allow_struct_expr);

        loop {
            match self.current().kind {
                TokenKind::OpenBracket => {
                    // Array indexing
                    let open_bracket = self.consume().clone();
                    let index = self.parse_index_expression();
                    let close_bracket = self.consume_and_check(TokenKind::CloseBracket).clone();
                    expr = self.ast.index_expression(expr, open_bracket, index, close_bracket).id;
                }
                TokenKind::Period => {
                    let period = self.consume().clone();
                    
                    // Check if this is a method call (identifier followed by '(')
                    if self.current().kind == TokenKind::Identifier && 
                       self.peek(1).kind == TokenKind::LeftParen {
                        let method_name = self.consume_and_check(TokenKind::Identifier).clone();
                        let left_paren = self.consume_and_check(TokenKind::LeftParen).clone();
                        
                        let mut arguments = Vec::new();
                        
                        while self.current().kind != TokenKind::RightParen && !self.is_at_end() {
                            arguments.push(self.parse_expression());
                            if self.current().kind == TokenKind::Comma {
                                self.consume_and_check(TokenKind::Comma);
                            }
                        }
                        
                        let right_paren = self.consume_and_check(TokenKind::RightParen).clone();
                        
                        expr = self.ast.method_call_expression(
                            expr, 
                            period,
                            method_name, 
                            left_paren, 
                            arguments, 
                            right_paren
                        ).id;
                    } else {
                        // Field access
                        let index = self.parse_primary_expression();
                        expr = self.ast.field_expression(expr, period, index).id;
                    }
                }
                _ => break,
            }
        }

        expr
    }

    fn parse_index_expression(&mut self) -> ExprIndex {
        self.parse_expression()
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

            // logical operators
            TokenKind::AmpersandAmpersand => Some(BinaryOpKind::LogicalAnd),
            TokenKind::PipePipe => Some(BinaryOpKind::LogicalOr),
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

            if self.current().kind == TokenKind::CloseBrace {
                break;
            }
        }

        let right_brace = self.consume_and_check(TokenKind::CloseBrace).clone();
        self.ast.block_expression(left_brace, statements, right_brace)
    }

    fn parse_while_expression(&mut self, while_keyword: Token) -> &Expression {
        let condition_expr = self.parse_condition_expression();
        let body = self.parse_body();

        self.ast.while_expression(&self.ast.clone(), while_keyword, condition_expr, body)
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

    fn parse_call_expression(&mut self, identifier: Path) -> ExprIndex {
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

    fn parse_return_expression(&mut self, return_keyword: Token) -> &Expression {
        let expression = if self.current().kind == TokenKind::SemiColon || 
                           self.current().kind == TokenKind::CloseBrace ||
                           self.is_at_end() {
            None
        } else {
            Some(self.parse_expression())
        };

        self.ast.return_expression(&self.ast.clone(), return_keyword, expression)
    }

    fn parse_struct_expression(&mut self, path: Path) -> ExprIndex {
        let left_brace = self.consume_and_check(TokenKind::OpenBrace).clone();
        let mut fields = Vec::new();
        let mut rest = None;

        while self.current().kind != TokenKind::CloseBrace && !self.is_at_end() {
            let field = self.parse_expression();
            let field_expr = self.ast.query_expression(field);

            let field_token = match &field_expr.kind {
                ExpressionKind::Path(path_expr) => {
                    path_expr.path.tokens.last().unwrap().clone()
                }
                _ => {
                    //self.diagnostics_report.borrow_mut().report_expected_identifier(&self.current());
                    Token::new(TokenKind::Identifier, TextSpan::default())
                }
            };

            if self.current().kind != TokenKind::CloseBrace {
                if let Some(_colon) = self.consume_if(TokenKind::Colon) {
                    let value = self.parse_expression();
                    let expr = self.ast.query_expression(value);
                    fields.push(ExprField { identifier: field_token, expr: expr.clone(), is_shorthand: false });
                } else {
                    fields.push(ExprField { identifier: field_token, expr: field_expr.clone(), is_shorthand: true });
                }
                
                if self.current().kind != TokenKind::CloseBrace {
                    self.consume_and_check(TokenKind::Comma);
                }
            }

            if self.current().kind == TokenKind::DoublePeriod {
                rest = Some(self.consume_and_check(TokenKind::DoublePeriod).clone());
            }
        }

        let right_brace = self.consume_and_check(TokenKind::CloseBrace).clone();

        self.ast.struct_expression(path, fields, rest, left_brace, right_brace).id
    }

    fn parse_path(&mut self, base_ident: Token) -> Path {
        let mut segments = vec![PathSegment { identifier: base_ident.clone(), arguments: None }];
        let mut tokens = vec![base_ident];

        while self.current().kind == TokenKind::DoubleColon {
            let sep = self.consume().clone(); // consume '::'
            tokens.push(sep);

            let seg = self.consume_and_check(TokenKind::Identifier);
            segments.push(PathSegment { identifier: seg.clone(), arguments: None });
            tokens.push(seg.clone());
        }

        let span = TextSpan::combine(tokens.iter().map(|t| t.span.clone()).collect());

        Path {
            span,
            segments,
            tokens,
        }
    }

    fn parse_primary_expression(&mut self) -> ExprIndex { // for string literals, numbers, function calls
        self.parse_primary_expression_in_context(true)
    }

    fn parse_primary_expression_in_context(&mut self, allow_struct_expr: bool) -> ExprIndex { // for string literals, numbers, function calls
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
            TokenKind::Identifier | TokenKind::SelfType | TokenKind::SelfValue => {
                let identifier = token.clone();
                let path = self.parse_path(identifier);

                if matches!(self.current().kind, TokenKind::LeftParen) {
                    return self.parse_call_expression(path.clone());
                } else if allow_struct_expr && matches!(self.current().kind, TokenKind::OpenBrace) {
                    return self.parse_struct_expression(path);
                }

                self.ast.path_expression(path.segments, path.tokens)
            },
            TokenKind::Return => self.parse_return_expression(token.clone()),
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
            TokenKind::While => self.parse_while_expression(token.clone()),
            TokenKind::Break => self.ast.break_expression(token.clone()),
            TokenKind::Continue => self.ast.continue_expression(token.clone()),
            _ => {
                self.diagnostics_report.borrow_mut().report_expected_expression(&token);
                self.ast.error_expression(token.span)
            }
        }.id;
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