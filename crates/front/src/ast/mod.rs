use std::{fmt::{Display, Formatter}, ops::Deref};

use crate::compilation_unit::{VariableIndex};
use snowflake_common::{bug_report, token::{Token, TokenKind}};
use snowflake_common::{text::span::TextSpan, typings::Type, idx, Idx, IndexVec};
use visitor::ASTVisitor;
use printer::ASTPrinter;

pub mod lexer;
pub mod parser;
pub mod eval;
pub mod visitor;
pub mod printer;


idx!(StmtIndex);
idx!(ExprIndex);
idx!(ItemIndex);

#[derive(Debug, Clone)]
pub struct Ast {
    pub statements: IndexVec<StmtIndex, Statement>,
    pub expressions: IndexVec<ExprIndex, Expression>,
    pub items: IndexVec<ItemIndex, Item>
}

impl Ast {
    pub fn new() -> Self {
        Self {
            statements: IndexVec::new(),
            expressions: IndexVec::new(),
            items: IndexVec::new(),
        }
    }

    pub fn query_statement(&self, stmt_id: StmtIndex) -> &Statement {
        &self.statements[stmt_id]
    }

    pub fn query_expression(&self, expr_id: ExprIndex) -> &Expression {
        &self.expressions[expr_id]
    }

    pub fn query_item(&self, item_id: ItemIndex) -> &Item {
        &self.items[item_id]
    }

    pub fn query_statement_mut(&mut self, stmt_id: StmtIndex) -> &mut Statement {
        &mut self.statements[stmt_id]
    }
    
    pub fn query_expression_mut(&mut self, expr_id: ExprIndex) -> &mut Expression {
        &mut self.expressions[expr_id]
    }

    pub fn query_item_mut(&mut self, item_id: ItemIndex) -> &mut Item {
        &mut self.items[item_id]
    }

    pub fn set_variable(&mut self, expr_id: ExprIndex, variable_index: VariableIndex) {
        let expression = self.query_expression_mut(expr_id);

        match &mut expression.kind {
            ExpressionKind::Assignment(assign_expr) => {
                assign_expr.variable_index = variable_index;
            }
            ExpressionKind::Variable(var_expr) => {
                var_expr.variable_index = variable_index;
            }
            _ => unreachable!("Unable to set variable of non-variable expression"),
        }
    }

    pub fn set_variable_for_statement(&mut self, statement_id: &StmtIndex, variable_index: VariableIndex) {
        let statement = self.query_statement_mut(*statement_id);

        match &mut statement.kind {
            StatementKind::Let(var_declaration) => {
                var_declaration.variable_index = variable_index;
            }
            StatementKind::Const(const_declaration) => {
                const_declaration.variable_index = variable_index;
            }
            _ => unreachable!("Unable to set variable of non-variable statement")
        }
    }

    pub fn set_function(&mut self, expr_id: ExprIndex, fx_idx: ItemIndex) {
        let expr = self.query_expression_mut(expr_id);
        match &mut expr.kind {
            ExpressionKind::Call(call_expr) => {
                call_expr.fx_idx = fx_idx;
            }
            _ => unreachable!("Unable to set function of non-call expression"),
        }
    }

    pub fn set_type(&mut self, expr_id: ExprIndex, ty: Type) {
        let expr = &mut self.expressions[expr_id];
        expr.ty = ty;
    }

    // Statement
    fn statement_from_kind(&mut self, kind: StatementKind, span: TextSpan) -> &Statement {
        let statement = Statement::new(kind, StmtIndex::new(0), span);
        let id = self.statements.push(statement);

        self.statements[id].id = id;
        
        if let StatementKind::Let(let_stmt) = &mut self.statements[id].kind {
            let_stmt.pattern.id = id;
        }
        
        &self.statements[id]
    }

    pub fn expression_statement(&mut self, ast: &Ast, expr_id: ExprIndex) -> &Statement {
        let span = self.query_expression(expr_id).span(ast);
        self.statement_from_kind(StatementKind::Expression(expr_id), span)
    }

    pub fn let_statement(
        &mut self, ast: &Ast, identifier: Token, initialiser: ExprIndex, type_annotation: Option<StaticTypeAnnotation>
    ) -> &Statement {
        let mut spans = Vec::new();
        
        spans.push(identifier.span.clone());
        spans.push(self.query_expression(initialiser).span(ast));
        
        if let Some(ref annotation) = type_annotation {
            spans.extend(annotation.collect_spans());
        }
        
        let span_refs: Vec<&TextSpan> = spans.iter().collect();
        let span = TextSpan::combine_refs(&span_refs);

        let pattern = Pattern {
            id: StmtIndex::new(0), // Will be set after statement creation
            kind: PatternKind::Identifier(BindingMode(Mutability::Immutable), identifier.clone()),
            span: identifier.span.clone(),
            token: identifier.clone(),
        };

        self.statement_from_kind(
            StatementKind::Let(LetStatement { 
                identifier: identifier.clone(), 
                pattern,
                initialiser, 
                type_annotation, 
                variable_index: VariableIndex::new(0) 
            }),
            span,
        )
    }

    // Pattern
    pub fn identifier_pattern(
        &mut self, 
        binding_mode: BindingMode, 
        identifier: Token
    ) -> Pattern {
        let span = identifier.span.clone();
        let pattern = Pattern {
            id: StmtIndex::new(0), // Will be set when pattern is used in statement
            kind: PatternKind::Identifier(binding_mode, identifier.clone()),
            span,
            token: identifier,
        };
        pattern
    }

    pub fn tuple_pattern(
        &mut self,
        patterns: Vec<Box<Pattern>>,
        span: TextSpan,
        token: Token
    ) -> Pattern {
        Pattern {
            id: StmtIndex::new(0), // Will be set when pattern is used in statement
            kind: PatternKind::Tuple(patterns),
            span,
            token,
        }
    }

    pub fn error_pattern(
        &mut self,
        span: TextSpan,
        token: Token
    ) -> Pattern {
        Pattern {
            id: StmtIndex::new(0), // Will be set when pattern is used in statement
            kind: PatternKind::Err,
            span,
            token,
        }
    }

    // Update let_statement to accept a Pattern and set its ID
    pub fn let_statement_with_pattern(
        &mut self, 
        ast: &Ast, 
        mut pattern: Pattern, 
        initialiser: ExprIndex, 
        type_annotation: Option<StaticTypeAnnotation>
    ) -> &Statement {
        let mut spans = Vec::new();
        
        spans.push(pattern.span.clone());
        spans.push(self.query_expression(initialiser).span(ast));
        
        if let Some(ref annotation) = type_annotation {
            spans.extend(annotation.collect_spans());
        }
        
        let span_refs: Vec<&TextSpan> = spans.iter().collect();
        let span = TextSpan::combine_refs(&span_refs);

        let identifier = match &pattern.kind {
            PatternKind::Identifier(_, token) => token.clone(),
            _ => pattern.token.clone()
        };

        let statement = Statement::new(
            StatementKind::Let(LetStatement { 
                identifier, 
                pattern: pattern.clone(),
                initialiser, 
                type_annotation, 
                variable_index: VariableIndex::new(0) 
            }),
            StmtIndex::new(0),
            span
        );
        
        let statement_id = self.statements.push(statement);
        self.statements[statement_id].id = statement_id;
        pattern.id = statement_id;
        
        if let StatementKind::Let(let_stmt) = &mut self.statements[statement_id].kind {
            let_stmt.pattern.id = statement_id;
        }
        
        &self.statements[statement_id]
    }

    pub fn const_statement(
        &mut self, 
        ast: &Ast, 
        identifier: Token, 
        initialiser: ExprIndex, 
        type_annotation: StaticTypeAnnotation
    ) -> &Statement {
        let mut spans = Vec::new();
        
        spans.push(identifier.span.clone());
        spans.push(self.query_expression(initialiser).span(ast));

        spans.extend(type_annotation.collect_spans());

        let span_refs: Vec<&TextSpan> = spans.iter().collect();
        let span = TextSpan::combine_refs(&span_refs);

        self.statement_from_kind(
            StatementKind::Const(ConstStatement { 
                identifier, 
                expr: initialiser, 
                type_annotation, 
                variable_index: VariableIndex::new(0) 
            }),
            span,
        )
    }

    pub fn if_expression(
        &mut self, if_keyword: Token, condition: ExprIndex, then_branch: Body, else_statement: Option<ElseBranch>
    ) -> &Expression {
        let mut span_refs = vec![&if_keyword.span];
        let condition_span = self.query_expression(condition).span(self);
        span_refs.push(&condition_span);
        let then_span = then_branch.span(self);
        span_refs.push(&then_span);
        
        let else_spans: Vec<TextSpan> = if let Some(ref else_branch) = else_statement {
            let else_span = else_branch.body.span(self);
            vec![else_branch.else_keyword.span.clone(), else_span]
        } else {
            vec![]
        };
        
        for span in &else_spans {
            span_refs.push(span);
        }
        
        let span = TextSpan::combine_refs(&span_refs);
        self.expression_from_kind(ExpressionKind::If(IfExpression { if_keyword, condition, then_branch, else_branch: else_statement }), span)
    }

    pub fn block_expression(&mut self, left_brace: Token, statements: Vec<StmtIndex>, right_brace: Token) -> &Expression {
        let mut span_refs = vec![&left_brace.span];
        
        let statement_spans: Vec<TextSpan> = statements.iter()
            .map(|stmt_id| self.query_statement(*stmt_id).span(self))
            .collect();
        
        for span in &statement_spans {
            span_refs.push(span);
        }
        
        span_refs.push(&right_brace.span);
        
        let span = TextSpan::combine_refs(&span_refs);
        self.expression_from_kind(ExpressionKind::Block(BlockExpression { left_brace, statements, right_brace }), span)
    }

    pub fn while_statement(&mut self, ast: &Ast, while_keyword: Token, condition: ExprIndex, body: Body) -> &Statement {
        let condition_span = self.query_expression(condition).span(ast);
        let body_span = body.span(ast);
        let span_refs = vec![&while_keyword.span, &condition_span, &body_span];
        let span = TextSpan::combine_refs(&span_refs);
        
        self.statement_from_kind(
            StatementKind::While(WhileStatement { while_keyword, condition, body }),
            span
        )
    }

    pub fn return_statement(&mut self, _ast: &Ast, return_keyword: Token, return_value: Option<ExprIndex>) -> &Statement {
        let mut span_refs = vec![&return_keyword.span];
        
        let return_value_span = if let Some(expr_id) = return_value {
            Some(self.query_expression(expr_id).span(_ast))
        } else {
            None
        };
        
        if let Some(ref span) = return_value_span {
            span_refs.push(span);
        }
        
        let span = TextSpan::combine_refs(&span_refs);
        
        self.statement_from_kind(
            StatementKind::Return(ReturnStatement { return_keyword, return_value }),
            span
        )
    }

    // Expression
    pub fn expression_from_kind(&mut self, kind: ExpressionKind, span: TextSpan) -> &Expression {
        let expression = Expression::new(kind, ExprIndex::new(0), Type::Unresolved, span);
        let expr_id = self.expressions.push(expression);

        self.expressions[expr_id].id = expr_id;
        &self.expressions[expr_id]
    }

    pub fn number_expression(&mut self, token: Token, number: i64) -> &Expression {
        let span = token.span.clone();
        self.expression_from_kind(ExpressionKind::Number(NumberExpression { token, number }), span)
    }

    pub fn float_expression(&mut self, token: Token, number: f64) -> &Expression {
        let span = token.span.clone();
        self.expression_from_kind(ExpressionKind::Float(FloatExpression { token, number }), span)
    }

    pub fn usize_expression(&mut self, token: Token, number: usize) -> &Expression {
        let span = token.span.clone();
        self.expression_from_kind(ExpressionKind::Usize(UsizeExpression { token, number }), span)
    }

    pub fn string_expression(&mut self, token: Token, value: String) -> &Expression {
        let span = token.span.clone();
        self.expression_from_kind(ExpressionKind::String(StringExpression { token, string: value }), span)
    }

    pub fn binary_expression(&mut self, operator: BinaryOp, left: ExprIndex, right: ExprIndex, from_compound: bool) -> &Expression {
        let left_span = self.query_expression(left).span(self);
        let right_span = self.query_expression(right).span(self);
        let span_refs = vec![&left_span, &operator.token.span, &right_span];
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(ExpressionKind::Binary(BinaryExpression { left, operator, right, from_compound }), span)
    }

    pub fn compound_binary_expression(
        &mut self, operator: AssignmentOpKind, operator_token: Token, left: ExprIndex, right: ExprIndex
    ) -> &Expression {
        let left_span = self.query_expression(left).span(self);
        let right_span = self.query_expression(right).span(self);
        let span_refs = vec![&left_span, &operator_token.span, &right_span];
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(
            ExpressionKind::CompoundBinary(CompoundBinaryExpression { left, operator, operator_token, right }),
            span
        )
    }

    pub fn unary_expression(&mut self, operator: UnaryOp, operand: ExprIndex) -> &Expression {
        let operand_span = self.query_expression(operand).span(self);
        let span_refs = vec![&operator.token.span, &operand_span];
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(ExpressionKind::Unary(UnaryExpression { operator, operand }), span)
    }

    pub fn parenthesised_expression(&mut self, left_paren:Token, expression: ExprIndex, right_paren: Token) -> &Expression {
        let expr_span = self.query_expression(expression).span(self);
        let span_refs = vec![&left_paren.span, &expr_span, &right_paren.span];
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(ExpressionKind::Parenthesised(ParenExpression { left_paren, expression, right_paren }), span)
    }

    pub fn variable_expression(&mut self, identifier: Token) -> &Expression {
        let span = identifier.span.clone();
        self.expression_from_kind(ExpressionKind::Variable(VarExpression { identifier, variable_index: VariableIndex::new(0) }), span)
    }

    pub fn assignment_expression(&mut self, left_hand_side: ExprIndex, equals: Token, expression: ExprIndex) -> &Expression {
        let lhs_span = self.query_expression(left_hand_side).span(self);
        let expr_span = self.query_expression(expression).span(self);
        let span_refs = vec![&lhs_span, &equals.span, &expr_span];
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(
            ExpressionKind::Assignment(AssignExpression { lhs: left_hand_side, equals, expression, variable_index: VariableIndex::new(0) }),
            span
        )
    }

    pub fn boolean_expression(&mut self, token: Token, value: bool) -> &Expression {
        let span = token.span.clone();
        self.expression_from_kind(ExpressionKind::Boolean(BoolExpression { value, token }), span)
    }

    pub fn call_expression(&mut self, callee: Token, left_paren: Token, arguments: Vec<ExprIndex>, right_paren: Token) -> &Expression {
        let mut span_refs = vec![&callee.span, &left_paren.span];
        
        let arg_spans: Vec<TextSpan> = arguments.iter()
            .map(|arg_id| self.query_expression(*arg_id).span(self))
            .collect();
        
        for span in &arg_spans {
            span_refs.push(span);
        }
        
        span_refs.push(&right_paren.span);
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(
            ExpressionKind::Call(CallExpression { callee, left_paren, arguments, right_paren, fx_idx: ItemIndex::unreachable() }),
            span
        )
    }

    pub fn break_expression(&mut self, break_keyword: Token) -> &Expression {
        let span = break_keyword.span.clone();
        self.expression_from_kind(ExpressionKind::Break(BreakExpression { break_keyword }), span)
    }

    pub fn continue_expression(&mut self, continue_keyword: Token) -> &Expression {
        let span = continue_keyword.span.clone();
        self.expression_from_kind(ExpressionKind::Continue(ContinueExpression { continue_keyword }), span)
    }

    pub fn array_expression(
        &mut self, type_decl: Token, open_square_bracket: Token, elements: Vec<ExprIndex>, commas: Vec<Token>, close_square_bracket: Token
    ) -> &Expression {
        let mut span_refs = vec![&type_decl.span, &open_square_bracket.span];
        
        let element_spans: Vec<TextSpan> = elements.iter()
            .map(|elem_id| self.query_expression(*elem_id).span(self))
            .collect();
        
        for (i, span) in element_spans.iter().enumerate() {
            span_refs.push(span);
            if i < commas.len() {
                span_refs.push(&commas[i].span);
            }
        }
        
        span_refs.push(&close_square_bracket.span);
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(
            ExpressionKind::Array(ArrayExpression { type_decl, open_square_bracket, elements, commas, close_square_bracket }),
            span
        )
    }

    pub fn index_expression(&mut self, object: ExprIndex, open_square_bracket: Token, index: ExprIndex, close_square_bracket: Token) -> &Expression {
        let object_span = self.query_expression(object).span(self);
        let index_span = self.query_expression(index).span(self);
        let span_refs = vec![&object_span, &open_square_bracket.span, &index_span, &close_square_bracket.span];
        let span = TextSpan::combine_refs(&span_refs);
        
        let array_index = ArrayIndex {
            open_square_bracket,
            idx_no: index,
            close_square_bracket,
        };
        
        self.expression_from_kind(
            ExpressionKind::IndexExpression(IndexExpression { object, index: array_index }),
            span
        )
    }

    pub fn tuple_expression(&mut self, open_paren: Token, elements: Vec<ExprIndex>, close_paren: Token) -> &Expression {
        let mut span_refs = vec![&open_paren.span];
        
        let element_spans: Vec<TextSpan> = elements.iter()
            .map(|element_id| self.query_expression(*element_id).span(self))
            .collect();
        
        for span in &element_spans {
            span_refs.push(span);
        }
        
        span_refs.push(&close_paren.span);
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(
            ExpressionKind::Tuple(TupleExpression { open_paren, elements, close_paren }),
            span
        )
    }

    pub fn field_expression(&mut self, object: ExprIndex, period: Token, index: ExprIndex) -> &Expression {
        let object_span = self.query_expression(object).span(self);
        let index_span = self.query_expression(index).span(self);
        let span_refs = vec![&object_span, &period.span, &index_span];
        let span = TextSpan::combine_refs(&span_refs);
        
        let field = FieldName {
            period,
            idx_no: index,
        };
        
        self.expression_from_kind(
            ExpressionKind::FieldExpression(FieldExpression { object, field }),
            span
        )
    }

    pub fn struct_expression(
        &mut self,
        identifier: Token,
        fields: Vec<ExprField>,
        rest_token: Option<Token>,
        left_brace: Token,
        right_brace: Token
    ) -> &Expression {
        let rest = if let Some(rest_token) = rest_token.clone() {
            match &rest_token.kind {
                TokenKind::DoublePeriod => {
                    StructRest::Rest(rest_token.span)
                }
                _ => bug_report!("Unexpected token kind for struct rest"),
            }
        } else {
            StructRest::None
        };

        let mut all_spans = vec![identifier.span.clone(), left_brace.span.clone()];
        for field_idx in fields.iter() {
            if field_idx.is_shorthand {
                all_spans.push(field_idx.identifier.span.clone());
            } else {
                all_spans.push(field_idx.identifier.span.clone());
                all_spans.push(field_idx.expr.span(self));
            }
        }

        if let Some(ref rest_tok) = rest_token {
            all_spans.push(rest_tok.span.clone());
        }

        all_spans.push(right_brace.span.clone());

        self.expression_from_kind(
            ExpressionKind::Struct(StructExpression { identifier: identifier.clone(), fields, rest }),
            TextSpan::combine(all_spans)
        )
    }

    pub fn error_expression(&mut self, span: TextSpan) -> &Expression {
        let span_clone = span.clone();
        self.expression_from_kind(ExpressionKind::Error(span), span_clone)
    }

    // Item
    pub fn item_from_kind(&mut self, kind: ItemKind, span: TextSpan) -> &Item {
        let item = Item::new(kind, ItemIndex::new(0), span);
        let id = self.items.push(item);
        self.items[id].id = id;

        &self.items[id]
    }
    
    pub fn item_from_kind_local(&mut self, kind: ItemKind, span: TextSpan, is_local: bool) -> &Item {
        let item = if is_local {
            Item::new_local(kind, ItemIndex::new(0), span)
        } else {
            Item::new(kind, ItemIndex::new(0), span)
        };
        let id = self.items.push(item);
        self.items[id].id = id;

        &self.items[id]
    }

    pub fn struct_item(
        &mut self,
        identifier: Token,
        generics: Generics,
        variant_data: VariantData,
    ) -> &Item {
        let all_spans = vec![identifier.span.clone(), generics.span.clone()];

        self.item_from_kind(ItemKind::Struct(identifier, generics, variant_data), TextSpan::combine(all_spans))
    }
    
    pub fn struct_item_local(
        &mut self,
        identifier: Token,
        generics: Generics,
        variant_data: VariantData,
        is_local: bool,
    ) -> &Item {
        let all_spans = vec![identifier.span.clone(), generics.span.clone()];

        self.item_from_kind_local(ItemKind::Struct(identifier, generics, variant_data), TextSpan::combine(all_spans), is_local)
    }

    pub fn constant_item(
        &mut self,
        identifier: Token,
        generics: Generics,
        type_annotation: StaticTypeAnnotation,
        expr: Option<Box<ExprIndex>>,
    ) -> &Item {
        let mut all_spans = vec![identifier.span.clone(), generics.span.clone()];

        all_spans.extend(type_annotation.collect_spans());

        if let Some(ref expr) = expr {
            all_spans.push(self.query_expression(**expr).span(self));
        }

        let constant_item = ConstantItem {
            identifier,
            generics,
            type_annotation,
            expr,
        };

        self.item_from_kind(ItemKind::Const(Box::new(constant_item)), TextSpan::combine(all_spans))
    }

    pub fn func_item(
        &mut self,
        fx_keyword: Token,
        identifier: Token,
        generics: Generics,
        body: Body,
        return_type: Option<FxReturnType>,
        index: ItemIndex
    ) -> &Item {
        let mut all_spans = vec![
            fx_keyword.span.clone(),
            identifier.span.clone(),
            generics.span.clone(),
            body.span(self),
        ];
        
        if let Some(ref rt) = return_type {
            all_spans.push(rt.arrow.span.clone());
            let type_spans: Vec<TextSpan> = rt.type_tokens.iter().map(|token| token.span.clone()).collect();
            all_spans.push(TextSpan::combine(type_spans));
        }
        
        let span = TextSpan::combine(all_spans);

        self.item_from_kind(ItemKind::Function(FxDeclaration { fx_keyword, identifier, generics, body, return_type, index }), span)
    }

    pub fn visit(&mut self, visitor: &mut dyn ASTVisitor) {
        for item in self.items.clone().iter() {
            visitor.visit_item(self, item.id);
        }
    }

    pub fn visualise(&mut self) -> () {
        let mut printer = ASTPrinter::new();
        self.visit(&mut printer);
        println!("{}", printer.result);
    }
}

#[derive(Debug, Clone)]
pub struct Item {
    pub kind: ItemKind,
    pub id: ItemIndex,
    pub span: TextSpan,
    pub is_local: bool,
}

impl Item {
    pub fn new(kind: ItemKind, id: ItemIndex, span: TextSpan) -> Self {
        Self { kind, id, span, is_local: false }
    }
    
    pub fn new_local(kind: ItemKind, id: ItemIndex, span: TextSpan) -> Self {
        Self { kind, id, span, is_local: true }
    }
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    Function(FxDeclaration),
    Const(Box<ConstantItem>),
    Struct(Token, Generics, VariantData),
}

#[derive(Debug, Clone)]
pub struct ConstantItem {
    pub identifier: Token,
    pub generics: Generics,
    pub type_annotation: StaticTypeAnnotation,
    pub expr: Option<Box<ExprIndex>>,
}

#[derive(Debug, Clone)]
pub struct FxReturnType {
    pub arrow: Token,
    pub type_tokens: Vec<Token>,
    pub ty: TypeKind,
}

impl FxReturnType {
    pub fn new(arrow: Token, type_tokens: Vec<Token>, ty: TypeKind) -> Self {
        Self { arrow, type_tokens, ty }
    }
}

#[derive(Debug, Clone)]
pub struct FxDeclaration {
    pub fx_keyword: Token,
    pub identifier: Token,
    pub generics: Generics,
    pub body: Body,
    pub return_type: Option<FxReturnType>,
    pub index: ItemIndex,
}

#[derive(Debug, Clone)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub span: TextSpan,
}

impl Generics {
    pub fn new(params: Vec<GenericParam>, span: TextSpan) -> Self {
        Self { params, span }
    }

    pub fn empty(span: TextSpan) -> Self {
        Self { params: Vec::new(), span }
    }

    pub fn is_empty(&self) -> bool {
        self.params.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &GenericParam> {
        self.params.iter()
    }

    /// Get parameter indices from generics (useful for function parameters)
    pub fn get_param_indices(&self) -> Vec<VariableIndex> {
        self.params.iter().map(|param| param.idx).collect()
    }
}

#[derive(Debug, Clone)]
pub struct GenericParam {
    pub idx: VariableIndex,
    pub identifier: Token,
    pub kind: GenericParamKind,
    pub colon_token: Option<Token>,
}

impl GenericParam {
    pub fn new(idx: VariableIndex, identifier: Token, kind: GenericParamKind, colon_token: Option<Token>) -> Self {
        Self { idx, identifier, kind, colon_token }
    }
}

#[derive(Debug, Clone)]
pub enum GenericParamKind {
    Const {
        ty: Box<TypeKind>,
        span: TextSpan,
        expr: Box<Expression>,
    },
    Type {
        ty: Box<TypeKind>,
        span: TextSpan,
    }
}

#[derive(Debug, Clone)]
pub enum VariantData {
    Struct {
        fields: Vec<FieldDefinition>,
    }
}

#[derive(Debug, Clone)]
pub struct FieldDefinition {
    pub identifier: Option<Token>,
    pub ty: Box<TypeKind>,
}

impl FieldDefinition {
    pub fn new(identifier: Option<Token>, ty: Box<TypeKind>) -> Self {
        Self { identifier, ty }
    }
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    Expression(ExprIndex),
    Let(LetStatement),
    While(WhileStatement),
    Return(ReturnStatement),
    Const(ConstStatement),
    Item(ItemIndex),
}

#[derive(Debug, Clone)]
pub struct Body {
    pub open_brace: Token,
    pub statements: Vec<StmtIndex>,
    pub close_brace: Token,
}

impl Body {
    pub fn new(open_brace: Token, statements: Vec<StmtIndex>, close_brace: Token) -> Self {
        Self { open_brace, statements, close_brace }
    }

    pub fn iter(&self) -> impl Iterator<Item = &StmtIndex> {
        self.statements.iter()
    }

    pub fn span(&self, ast: &Ast) -> TextSpan {
        TextSpan::combine(
            self.statements.iter().map(|statement| ast.query_statement(*statement).span(ast)
            ).collect::<Vec<TextSpan>>()
        )
    }

    pub fn last_statement_type(&self, ast: &Ast) -> Option<Type> {
        match self.statements.last() {
            Some(statement) => {
                let statement = ast.query_statement(*statement);
                match &statement.kind {
                    StatementKind::Expression(expr_id) => Some(ast.query_expression(*expr_id).ty.clone()),
                    _ => None,
                }
            }
            None => None,
        }
    }

    pub fn type_or_void(&self, ast: &Ast) -> Type {
        self.last_statement_type(ast).unwrap_or(Type::Void)
    }
}

impl Deref for Body {
    type Target = Vec<StmtIndex>;

    fn deref(&self) -> &Self::Target {
        &self.statements
    }
}

#[derive(Debug, Clone)]
pub struct ReturnStatement {
    pub return_keyword: Token,
    pub return_value: Option<ExprIndex>,
}

#[derive(Debug, Clone)]
pub struct StaticTypeAnnotation {
    pub colon: Token,
    pub type_kind: TypeKind,
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    /// Simple types like `int`, `float`, etc.
    Simple {
        type_name: Token,
    },
    /// Array types like `[int; 5]` or `[[int; 3]; 2]`
    Array {
        open_bracket: Token,
        element_type: Box<TypeKind>,
        semicolon: Token,
        length: Token,
        close_bracket: Token,
    },
    /// Slice types
    // TODO
    Slice {
        open_bracket: Token,
        element_type: Box<TypeKind>,
        close_bracket: Token,
    },
    /// Tuple types like `(int, string)`
    Tuple {
        open_paren: Token,
        element_types: Vec<Box<TypeKind>>,
        close_paren: Token,
    }
}

impl StaticTypeAnnotation {
    pub fn new_simple(colon: Token, type_name: Token) -> Self {
        Self { 
            colon, 
            type_kind: TypeKind::Simple { type_name }
        }
    }

    pub fn new_array(
        colon: Token,
        open_bracket: Token,
        element_type: TypeKind,
        semicolon: Token,
        length: Token,
        close_bracket: Token
    ) -> Self {
        Self {
            colon,
            type_kind: TypeKind::Array {
                open_bracket,
                element_type: Box::new(element_type),
                semicolon,
                length,
                close_bracket,
            }
        }
    }

    pub fn new_slice(
        colon: Token,
        open_bracket: Token,
        element_type: TypeKind,
        close_bracket: Token
    ) -> Self {
        Self {
            colon,
            type_kind: TypeKind::Slice {
                open_bracket,
                element_type: Box::new(element_type),
                close_bracket,
            }
        }
    }

    pub fn new_tuple(
        colon: Token,
        open_paren: Token,
        element_types: Vec<TypeKind>,
        close_paren: Token
    ) -> Self {
        Self {
            colon,
            type_kind: TypeKind::Tuple {
                open_paren,
                element_types: element_types.into_iter().map(Box::new).collect(),
                close_paren,
            }
        }
    }

    /// Collect all text spans from this type annotation
    pub fn collect_spans(&self) -> Vec<TextSpan> {
        let mut spans = vec![self.colon.span.clone()];
        self.collect_type_kind_spans(&self.type_kind, &mut spans);
        spans
    }

    /// Collect spans from `TypeKind`
    fn collect_type_kind_spans(&self, type_kind: &TypeKind, spans: &mut Vec<TextSpan>) {
        match type_kind {
            TypeKind::Simple { type_name } => {
                spans.push(type_name.span.clone());
            }
            TypeKind::Array { open_bracket, element_type, semicolon, length, close_bracket } => {
                spans.push(open_bracket.span.clone());
                self.collect_type_kind_spans(element_type, spans);
                spans.push(semicolon.span.clone());
                spans.push(length.span.clone());
                spans.push(close_bracket.span.clone());
            }
            TypeKind::Slice { open_bracket, element_type, close_bracket } => {
                spans.push(open_bracket.span.clone());
                self.collect_type_kind_spans(element_type, spans);
                spans.push(close_bracket.span.clone());
            }
            TypeKind::Tuple { open_paren, element_types, close_paren } => {
                spans.push(open_paren.span.clone());
                for elem_type in element_types {
                    self.collect_type_kind_spans(elem_type, spans);
                }
                spans.push(close_paren.span.clone());
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct WhileStatement {
    pub while_keyword: Token,
    pub condition: ExprIndex,
    pub body: Body,
}

#[derive(Debug, Clone)]
pub struct LetStatement {
    pub identifier: Token,
    pub pattern: Pattern,
    pub initialiser: ExprIndex,
    pub type_annotation: Option<StaticTypeAnnotation>,
    pub variable_index: VariableIndex,
}

#[derive(Debug, Clone)]
pub struct ConstStatement {
    pub identifier: Token,
    pub expr: ExprIndex,
    pub type_annotation: StaticTypeAnnotation,
    pub variable_index: VariableIndex,
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub kind: StatementKind,
    pub id: StmtIndex,
    pub span: TextSpan,
}

impl Statement {
    pub fn new(kind: StatementKind, id: StmtIndex, span: TextSpan) -> Self {
        Statement { kind, id, span }
    }

    pub fn span(&self, ast: &Ast) -> TextSpan {
        match &self.kind {
            StatementKind::Expression(expr_id) => ast.query_expression(*expr_id).span(ast),
            StatementKind::Let(let_statement) => {
                let mut spans = vec![let_statement.identifier.span.clone()];
                if let Some(type_annotation) = &let_statement.type_annotation {
                    spans.push(type_annotation.colon.span.clone());
                    spans.extend(type_annotation.collect_spans());
                }

                TextSpan::combine(spans)
            }
            StatementKind::Const(const_statement) => {
                let mut spans = vec![const_statement.identifier.span.clone()];
                spans.push(const_statement.type_annotation.colon.span.clone());
                spans.extend(const_statement.type_annotation.collect_spans());

                TextSpan::combine(spans)
            }
            StatementKind::While(while_statement) => {
                let mut spans = vec![while_statement.while_keyword.span.clone()];
                spans.push(ast.query_expression(while_statement.condition).span(ast));
                spans.push(while_statement.body.span(ast));
                
                TextSpan::combine(spans)
            }
            StatementKind::Return(return_statement) => {
                let mut spans = vec![return_statement.return_keyword.span.clone()];
                if let Some(return_value) = &return_statement.return_value {
                    spans.push(ast.query_expression(*return_value).span(ast));
                }

                TextSpan::combine(spans)
            }
            StatementKind::Item(item_id) => ast.query_item(*item_id).span.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Pattern {
    pub id: StmtIndex,
    pub kind: PatternKind,
    pub span: TextSpan,
    pub token: Token,
}

#[derive(Debug, Clone)]
pub enum PatternKind {
    Wildcard, // TODO: future impl
    Identifier(BindingMode, Token),
    Tuple(Vec<Box<Pattern>>),
    Expression(Box<Expression>),
    Err,
}

#[derive(Debug, Clone)]
pub struct BindingMode(pub Mutability);

#[derive(Debug, Clone)]
pub enum Mutability {
    Mutable,
    Immutable,
}

#[derive(Debug, Clone)]
pub enum ExpressionKind {
    Number(NumberExpression),
    Float(FloatExpression),
    Usize(UsizeExpression),
    String(StringExpression),
    Binary(BinaryExpression),
    CompoundBinary(CompoundBinaryExpression),
    Unary(UnaryExpression),
    Parenthesised(ParenExpression),
    Variable(VarExpression),
    Assignment(AssignExpression),
    Boolean(BoolExpression),
    Call(CallExpression),
    If(IfExpression),
    Block(BlockExpression),
    Break(BreakExpression),
    Continue(ContinueExpression),
    Array(ArrayExpression),
    IndexExpression(IndexExpression),
    Tuple(TupleExpression),
    FieldExpression(FieldExpression),
    Struct(StructExpression),
    Error(TextSpan),
}

impl ExpressionKind {
    pub fn is_from_compound(&self) -> bool {
        match self {
            ExpressionKind::Binary(binary_expr) => binary_expr.from_compound,
            ExpressionKind::CompoundBinary(_) => false,
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct StructExpression {
    pub identifier: Token,
    pub fields: Vec<ExprField>,
    pub rest: StructRest,
}

#[derive(Debug, Clone)]
pub struct ExprField {
    pub identifier: Token,
    pub expr: Expression,
    pub is_shorthand: bool,
}

#[derive(Debug, Clone)]
pub enum StructRest {
    Rest(TextSpan), // ..
    None,
}

#[derive(Debug, Clone)]
pub struct FieldExpression {
    pub object: ExprIndex,
    pub field: FieldName,
}

#[derive(Debug, Clone)]
pub struct FieldName {
    pub period: Token,
    pub idx_no: ExprIndex,
}

#[derive(Debug, Clone)]
pub struct TupleExpression {
    pub open_paren: Token,
    pub elements: Vec<ExprIndex>,
    pub close_paren: Token,
}

#[derive(Debug, Clone)]
pub struct IndexExpression {
    pub object: ExprIndex,
    pub index: ArrayIndex,
}

#[derive(Debug, Clone)]
pub struct ArrayIndex {
    pub open_square_bracket: Token,
    pub idx_no: ExprIndex,
    pub close_square_bracket: Token,
}

#[derive(Debug, Clone)]
pub struct ArrayExpression {
    pub type_decl: Token,
    pub open_square_bracket: Token,
    pub elements: Vec<ExprIndex>,
    pub commas: Vec<Token>,
    pub close_square_bracket: Token,
}

#[derive(Debug, Clone)]
pub struct BreakExpression {
    pub break_keyword: Token,
}

#[derive(Debug, Clone)]
pub struct ContinueExpression {
    pub continue_keyword: Token,
}

#[derive(Debug, Clone)]
pub struct BlockExpression {
    pub left_brace: Token,
    pub statements: Vec<StmtIndex>,
    pub right_brace: Token,
}

impl BlockExpression {
    pub fn returning_expression(&self, ast: &Ast) -> Option<ExprIndex> {
        if let Some(last_statement) = self.statements.last() {
            let statement = ast.query_statement(*last_statement);

            if let StatementKind::Expression(expr_id) = &statement.kind {
                return Some(*expr_id);
            }
        }
        None
    }
}

#[derive(Debug, Clone)]
pub struct ElseBranch {
    pub else_keyword: Token,
    pub body: Body,
}

impl ElseBranch {
    pub fn new(else_keyword: Token, body: Body) -> Self {
        ElseBranch { else_keyword, body }
    }
}

#[derive(Debug, Clone)]
pub struct IfExpression {
    pub if_keyword: Token,
    pub condition: ExprIndex,
    pub then_branch: Body,
    pub else_branch: Option<ElseBranch>,
}

#[derive(Debug, Clone)]
pub struct CallExpression {
    pub callee: Token,
    pub left_paren: Token,
    pub arguments: Vec<ExprIndex>,
    pub right_paren: Token,
    pub fx_idx: ItemIndex,
}

impl CallExpression {
    pub fn fx_name(&self) -> &str {
        &self.callee.span.literal
    }
}

#[derive(Debug, Clone)]
pub struct BoolExpression {
    pub value: bool,
    pub token: Token,
}

#[derive(Debug, Clone)]
pub struct AssignExpression {
    pub lhs: ExprIndex,
    pub equals: Token,
    pub expression: ExprIndex,
    pub variable_index: VariableIndex,
}

#[derive(Debug, Copy, Clone)]
pub enum UnaryOpKind {
    Negation, // unary minus
    BitwiseNot, // ~
}

impl Display for UnaryOpKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        return match self {
            UnaryOpKind::Negation => write!(f, "-"),
            UnaryOpKind::BitwiseNot => write!(f, "~"),
        };
    }
}

#[derive(Debug, Clone)]
pub struct UnaryOp {
    pub kind: UnaryOpKind,
    pub token: Token,
}

impl UnaryOp {
    pub fn new(kind: UnaryOpKind, token: Token) -> Self {
        UnaryOp { kind, token }
    }
}

#[derive(Debug, Clone)]
pub struct UnaryExpression {
    pub operator: UnaryOp,
    pub operand: ExprIndex,
}

#[derive(Debug, Clone)]
pub struct VarExpression {
    pub identifier: Token,
    pub variable_index: VariableIndex,
}

impl VarExpression {
    pub fn identifier(&self) -> &str {
        &self.identifier.span.literal
    }
}

#[derive(Debug, Copy, Clone)]
pub enum BinaryOpKind {
    // arithmentic
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
    Power,

    // bitwise
    BitwiseAnd, // &
    BitwiseOr,  // |
    BitwiseXor, // ^
    ShiftLeft,  // <<
    ShiftRight, // >>

    // relational
    Equals,
    NotEquals,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
}

impl Display for BinaryOpKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        return match self {
            BinaryOpKind::Plus => write!(f, "+"),
            BinaryOpKind::Minus => write!(f, "-"),
            BinaryOpKind::Multiply => write!(f, "*"),
            BinaryOpKind::Divide => write!(f, "/"),
            BinaryOpKind::Power => write!(f, "**"),
            BinaryOpKind::Modulo => write!(f, "%"),
            BinaryOpKind::BitwiseAnd => write!(f, "&"),
            BinaryOpKind::BitwiseOr => write!(f, "|"),
            BinaryOpKind::BitwiseXor => write!(f, "^"),
            BinaryOpKind::ShiftLeft => write!(f, "<<"),
            BinaryOpKind::ShiftRight => write!(f, ">>"),
            BinaryOpKind::Equals => write!(f, "=="),
            BinaryOpKind::NotEquals => write!(f, "!="),
            BinaryOpKind::LessThan => write!(f, "<"),
            BinaryOpKind::GreaterThan => write!(f, ">"),
            BinaryOpKind::LessThanOrEqual => write!(f, "<="),
            BinaryOpKind::GreaterThanOrEqual => write!(f, ">="),
        };
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOpAssociativity {
    Left,
    Right,
}

#[derive(Debug, Clone)]
pub struct BinaryOp {
    pub kind: BinaryOpKind,
    pub token: Token,
}

impl BinaryOp {
    pub fn new(kind: BinaryOpKind, token: Token) -> Self {
        BinaryOp { kind, token }
    }

    pub fn precedence(&self) -> u8 {
        match self.kind {
            // Arithmetic operators (highest precedence)
            BinaryOpKind::Power => 20,
            BinaryOpKind::Multiply => 19,
            BinaryOpKind::Divide => 19,
            BinaryOpKind::Modulo => 19,
            BinaryOpKind::Plus => 18,
            BinaryOpKind::Minus => 18,
            
            // Shift operators
            BinaryOpKind::ShiftLeft => 17,
            BinaryOpKind::ShiftRight => 17,
            
            // Relational operators
            BinaryOpKind::LessThan => 16,
            BinaryOpKind::GreaterThan => 16,
            BinaryOpKind::LessThanOrEqual => 16,
            BinaryOpKind::GreaterThanOrEqual => 16,
            
            // Equality operators
            BinaryOpKind::Equals => 15,
            BinaryOpKind::NotEquals => 15,
            
            // Bitwise operators (lowest precedence)
            BinaryOpKind::BitwiseAnd => 14,
            BinaryOpKind::BitwiseXor => 13,
            BinaryOpKind::BitwiseOr => 12,
        }
    }

    pub fn associativity(&self) -> BinaryOpAssociativity {
        match self.kind {
            BinaryOpKind::Power => BinaryOpAssociativity::Right,
            _ => BinaryOpAssociativity::Left,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum AssignmentOpKind {
    PlusAs,      // +=
    MinusAs,     // -=
    MultiplyAs,  // *=
    DivideAs,    // /=
    ModuloAs,    // %=
    BitwiseAndAs,  // &=
    BitwiseOrAs,   // |=
    BitwiseXorAs,  // ^=
    ShiftLeftAs,   // <<=
    ShiftRightAs,  // >>=
}

#[derive(Debug, Clone)]
pub struct BinaryExpression {
    pub left: ExprIndex, // stored in heap instead of stack
    pub operator: BinaryOp,
    pub right: ExprIndex,
    pub from_compound: bool,
}

#[derive(Debug, Clone)]
pub struct CompoundBinaryExpression {
    pub left: ExprIndex,
    pub operator: AssignmentOpKind,
    pub operator_token: Token,
    pub right: ExprIndex,
}

#[derive(Debug, Clone)]
pub struct NumberExpression {
    pub token: Token,
    pub number: i64,
}

#[derive(Debug, Clone)]
pub struct FloatExpression {
    pub token: Token,
    pub number: f64,
}

#[derive(Debug, Clone)]
pub struct UsizeExpression {
    pub token: Token,
    pub number: usize,
}

#[derive(Debug, Clone)]
pub struct StringExpression {
    pub token: Token,
    pub string: String,
}

#[derive(Debug, Clone)]
pub struct ParenExpression {
    pub left_paren: Token,
    pub expression: ExprIndex,
    pub right_paren: Token,
}

#[derive(Debug, Clone)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub id: ExprIndex,
    pub ty: Type,
    pub span: TextSpan,
}

impl Expression {
    pub fn new(kind: ExpressionKind, id: ExprIndex, ty: Type, span: TextSpan) -> Self {
        Expression { kind, id, ty, span }
    }

    pub fn span(&self, ast: &Ast) -> TextSpan {
        match &self.kind {
            ExpressionKind::Number(expr) => expr.token.span.clone(),
            ExpressionKind::Float(expr) => expr.token.span.clone(),
            ExpressionKind::Usize(expr) => expr.token.span.clone(),
            ExpressionKind::String(expr) => expr.token.span.clone(),
            ExpressionKind::Binary(expr) => {
                let left = ast.query_expression(expr.left).span(ast);
                let operator = expr.operator.token.span.clone();
                let right = ast.query_expression(expr.right).span(ast);

                TextSpan::combine(vec![left, operator, right])
            },
            ExpressionKind::CompoundBinary(expr) => {
                let left = ast.query_expression(expr.left).span(ast);
                let right = ast.query_expression(expr.right).span(ast);

                TextSpan::combine(vec![left, right])
            },
            ExpressionKind::Unary(expr) => {
                let operator = expr.operator.token.span.clone();
                let operand = ast.query_expression(expr.operand).span(ast);

                TextSpan::combine(vec![operator, operand])
            },
            ExpressionKind::Parenthesised(expr) => {
                let open_paren = expr.left_paren.span.clone();
                let expression = ast.query_expression(expr.expression).span(ast);
                let close_paren = expr.right_paren.span.clone();

                TextSpan::combine(vec![open_paren, expression, close_paren])
            },
            ExpressionKind::Variable(expr) => expr.identifier.span.clone(),
            ExpressionKind::Assignment(expr) => {
                let lhs = ast.query_expression(expr.lhs).span(ast);
                let equals = expr.equals.span.clone();
                let expression = ast.query_expression(expr.expression).span(ast);

                TextSpan::combine(vec![lhs, equals, expression])
            },
            ExpressionKind::Boolean(expr) => expr.token.span.clone(),
            ExpressionKind::Call(expr) => {
                let callee_span = expr.callee.span.clone();
                let left_paren = expr.left_paren.span.clone();
                let right_paren = expr.right_paren.span.clone();
                let mut spans = vec![callee_span, left_paren, right_paren];

                for arg in &expr.arguments {
                    spans.push(ast.query_expression(*arg).span(ast));
                }

                TextSpan::combine(spans)
            },
            ExpressionKind::If(expr) => {
                let if_span = expr.if_keyword.span.clone();
                let condition = ast.query_expression(expr.condition).span(ast);
                let then_branch = expr.then_branch.span(ast);
                let mut spans = vec![if_span, condition, then_branch];

                if let Some(else_branch) = &expr.else_branch {
                    let else_span = else_branch.else_keyword.span.clone();
                    spans.push(else_span);
                    spans.push(else_branch.body.span(ast));
                }

                TextSpan::combine(spans)
            },
            ExpressionKind::Block(block_statement) => {
                let mut spans = vec![block_statement.left_brace.span.clone()];
                for statement in &block_statement.statements {
                    spans.push(ast.query_statement(*statement).span(ast));
                }

                spans.push(block_statement.right_brace.span.clone());
                TextSpan::combine(spans)
            },
            ExpressionKind::Break(break_expression) => break_expression.break_keyword.span.clone(),
            ExpressionKind::Continue(continue_expression) => continue_expression.continue_keyword.span.clone(),
            ExpressionKind::Array(array_expression) => {
                let mut spans = vec![array_expression.open_square_bracket.span.clone()];
                for (i, element) in array_expression.elements.iter().enumerate() {
                    spans.push(ast.query_expression(*element).span(ast));

                    if i < array_expression.commas.len() {
                        spans.push(array_expression.commas[i].span.clone());
                    }
                }
                spans.push(array_expression.close_square_bracket.span.clone());

                TextSpan::combine(spans)
            },
            ExpressionKind::IndexExpression(index_expression) => {
                let object_span = ast.query_expression(index_expression.object).span(ast);
                let spans = vec![
                    object_span,
                    index_expression.index.open_square_bracket.span.clone(),
                    ast.query_expression(index_expression.index.idx_no).span(ast),
                    index_expression.index.close_square_bracket.span.clone(),
                ];


                TextSpan::combine(spans)
            },
            ExpressionKind::Tuple(tuple_expression) => {
                let open_paren = tuple_expression.open_paren.span.clone();
                let close_paren = tuple_expression.close_paren.span.clone();
                let mut spans = vec![open_paren, close_paren];

                for element in &tuple_expression.elements {
                    spans.push(ast.query_expression(*element).span(ast));
                }

                TextSpan::combine(spans)
            },
            ExpressionKind::FieldExpression(tuple_index_expression) => {
                let tuple_span = ast.query_expression(tuple_index_expression.object).span(ast);
                let spans = vec![
                    tuple_span,
                    tuple_index_expression.field.period.span.clone(),
                    ast.query_expression(tuple_index_expression.field.idx_no).span(ast)
                ];

                TextSpan::combine(spans)
            },
            ExpressionKind::Struct(struct_expression) => {
                let mut spans = Vec::new();
                for field in &struct_expression.fields {
                    spans.push(field.identifier.span.clone());
                    spans.push(field.expr.span(ast));
                }

                match &struct_expression.rest {
                    StructRest::Rest(rest_span) => spans.push(rest_span.clone()),
                    StructRest::None => {}
                }

                TextSpan::combine(spans)
            },
            ExpressionKind::Error(span) => span.clone(),
        }
    }
}