use std::{fmt::{Display, Formatter}, ops::Deref};

use crate::compilation_unit::{FunctionIndex, VariableIndex};
use snowflake_common::token::Token;
use snowflake_common::{text::span::TextSpan, typings::Type, idx, Idx, IndexVec};
use visitor::ASTVisitor;
use printer::ASTPrinter;

pub mod lexer;
pub mod parser;
pub mod eval;
pub mod visitor;
pub mod printer;


idx!(StatementId);
idx!(ExpressionId);
idx!(ItemId);

#[derive(Debug, Clone)]
pub struct Ast {
    pub statements: IndexVec<StatementId, Statement>,
    pub expressions: IndexVec<ExpressionId, Expression>,
    pub items: IndexVec<ItemId, Item>
}

impl Ast {
    pub fn new() -> Self {
        Self {
            statements: IndexVec::new(),
            expressions: IndexVec::new(),
            items: IndexVec::new(),
        }
    }

    pub fn query_statement(&self, stmt_id: StatementId) -> &Statement {
        &self.statements[stmt_id]
    }

    pub fn query_expression(&self, expr_id: ExpressionId) -> &Expression {
        &self.expressions[expr_id]
    }

    pub fn query_item(&self, item_id: ItemId) -> &Item {
        &self.items[item_id]
    }

    pub fn query_statement_mut(&mut self, stmt_id: StatementId) -> &mut Statement {
        &mut self.statements[stmt_id]
    }
    
    pub fn query_expression_mut(&mut self, expr_id: ExpressionId) -> &mut Expression {
        &mut self.expressions[expr_id]
    }

    pub fn query_item_mut(&mut self, item_id: ItemId) -> &mut Item {
        &mut self.items[item_id]
    }

    pub fn set_variable(&mut self, expr_id: ExpressionId, variable_index: VariableIndex) {
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

    pub fn set_variable_for_statement(&mut self, statement_id: &StatementId, variable_index: VariableIndex) {
        let statement = self.query_statement_mut(*statement_id);

        match &mut statement.kind {
            StatementKind::Let(var_declaration) => {
                var_declaration.variable_index = variable_index;
            }
            _ => unreachable!("Unable to set variable of non-variable statement")
        }
    }

    pub fn set_function(&mut self, expr_id: ExpressionId, fx_idx: FunctionIndex) {
        let expr = self.query_expression_mut(expr_id);
        match &mut expr.kind {
            ExpressionKind::Call(call_expr) => {
                call_expr.fx_idx = fx_idx;
            }
            _ => unreachable!("Unable to set function of non-call expression"),
        }
    }

    pub fn set_type(&mut self, expr_id: ExpressionId, ty: Type) {
        let expr = &mut self.expressions[expr_id];
        expr.ty = ty;
    }

    // Statement
    fn statement_from_kind(&mut self, kind: StatementKind, span: TextSpan) -> &Statement {
        let statement = Statement::new(kind, StatementId::new(0), span);
        let id = self.statements.push(statement);

        self.statements[id].id = id;
        &self.statements[id]
    }

    pub fn expression_statement(&mut self, ast: &Ast, expr_id: ExpressionId) -> &Statement {
        let span = self.query_expression(expr_id).span(ast);
        self.statement_from_kind(StatementKind::Expression(expr_id), span)
    }

    pub fn let_statement(
        &mut self, ast: &Ast, identifier: Token, initialiser: ExpressionId, type_annotation: Option<StaticTypeAnnotation>
    ) -> &Statement {
        let mut spans = Vec::new();
        
        spans.push(identifier.span.clone());
        spans.push(self.query_expression(initialiser).span(ast));
        
        if let Some(ref annotation) = type_annotation {
            spans.extend(annotation.collect_spans());
        }
        
        let span_refs: Vec<&TextSpan> = spans.iter().collect();
        let span = TextSpan::combine_refs(&span_refs);

        self.statement_from_kind(
            StatementKind::Let(LetStatement { identifier, initialiser, type_annotation, variable_index: VariableIndex::new(0) }),
            span,
        )
    }

    pub fn if_expression(
        &mut self, if_keyword: Token, condition: ExpressionId, then_branch: Body, else_statement: Option<ElseBranch>
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

    pub fn block_expression(&mut self, left_brace: Token, statements: Vec<StatementId>, right_brace: Token) -> &Expression {
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

    pub fn while_statement(&mut self, ast: &Ast, while_keyword: Token, condition: ExpressionId, body: Body) -> &Statement {
        let condition_span = self.query_expression(condition).span(ast);
        let body_span = body.span(ast);
        let span_refs = vec![&while_keyword.span, &condition_span, &body_span];
        let span = TextSpan::combine_refs(&span_refs);
        
        self.statement_from_kind(
            StatementKind::While(WhileStatement { while_keyword, condition, body }),
            span
        )
    }

    pub fn return_statement(&mut self, _ast: &Ast, return_keyword: Token, return_value: Option<ExpressionId>) -> &Statement {
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
        let expression = Expression::new(kind, ExpressionId::new(0), Type::Unresolved, span);
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

    pub fn binary_expression(&mut self, operator: BinaryOp, left: ExpressionId, right: ExpressionId, from_compound: bool) -> &Expression {
        let left_span = self.query_expression(left).span(self);
        let right_span = self.query_expression(right).span(self);
        let span_refs = vec![&left_span, &operator.token.span, &right_span];
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(ExpressionKind::Binary(BinaryExpression { left, operator, right, from_compound }), span)
    }

    pub fn compound_binary_expression(
        &mut self, operator: AssignmentOpKind, operator_token: Token, left: ExpressionId, right: ExpressionId
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

    pub fn unary_expression(&mut self, operator: UnaryOp, operand: ExpressionId) -> &Expression {
        let operand_span = self.query_expression(operand).span(self);
        let span_refs = vec![&operator.token.span, &operand_span];
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(ExpressionKind::Unary(UnaryExpression { operator, operand }), span)
    }

    pub fn parenthesised_expression(&mut self, left_paren:Token, expression: ExpressionId, right_paren: Token) -> &Expression {
        let expr_span = self.query_expression(expression).span(self);
        let span_refs = vec![&left_paren.span, &expr_span, &right_paren.span];
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(ExpressionKind::Parenthesised(ParenExpression { left_paren, expression, right_paren }), span)
    }

    pub fn variable_expression(&mut self, identifier: Token) -> &Expression {
        let span = identifier.span.clone();
        self.expression_from_kind(ExpressionKind::Variable(VarExpression { identifier, variable_index: VariableIndex::new(0) }), span)
    }

    pub fn assignment_expression(&mut self, identifier: Token, equals: Token, expression: ExpressionId) -> &Expression {
        let expr_span = self.query_expression(expression).span(self);
        let span_refs = vec![&identifier.span, &equals.span, &expr_span];
        let span = TextSpan::combine_refs(&span_refs);
        
        self.expression_from_kind(
            ExpressionKind::Assignment(AssignExpression { identifier, equals, expression, variable_index: VariableIndex::new(0) }),
            span
        )
    }

    pub fn boolean_expression(&mut self, token: Token, value: bool) -> &Expression {
        let span = token.span.clone();
        self.expression_from_kind(ExpressionKind::Boolean(BoolExpression { value, token }), span)
    }

    pub fn call_expression(&mut self, callee: Token, left_paren: Token, arguments: Vec<ExpressionId>, right_paren: Token) -> &Expression {
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
            ExpressionKind::Call(CallExpression { callee, left_paren, arguments, right_paren, fx_idx: FunctionIndex::unreachable() }),
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
        &mut self, type_decl: Token, open_square_bracket: Token, elements: Vec<ExpressionId>, commas: Vec<Token>, close_square_bracket: Token
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

    pub fn index_expression(&mut self, object: ExpressionId, open_square_bracket: Token, index: ExpressionId, close_square_bracket: Token) -> &Expression {
        let object_span = self.query_expression(object).span(self);
        let index_span = self.query_expression(index).span(self);
        let span_refs = vec![&object_span, &open_square_bracket.span, &index_span, &close_square_bracket.span];
        let span = TextSpan::combine_refs(&span_refs);
        
        let array_index = ArrayIndex {
            open_square_bracket,
            index,
            close_square_bracket,
        };
        
        self.expression_from_kind(
            ExpressionKind::IndexExpression(IndexExpression { object, indexes: vec![array_index] }),
            span
        )
    }

    pub fn error_expression(&mut self, span: TextSpan) -> &Expression {
        let span_clone = span.clone();
        self.expression_from_kind(ExpressionKind::Error(span), span_clone)
    }

    // Item
    pub fn item_from_kind(&mut self, kind: ItemKind, span: TextSpan) -> &Item {
        let item = Item::new(kind, ItemId::new(0), span);
        let id = self.items.push(item);
        self.items[id].id = id;

        &self.items[id]
    }

    pub fn func_item(
        &mut self,
        fx_keyword: Token,
        identifier: Token,
        parameters: Vec<FxDeclarationParams>,
        body: Body,
        return_type: Option<FxReturnType>,
        index: FunctionIndex
    ) -> &Item {
        let mut param_span: Vec<TextSpan> = Vec::new();
        for param in &parameters {
            param_span.push(param.identifier.span.clone());
            param_span.extend(param.type_annotation.collect_spans());
        }
        
        let span = TextSpan::combine_refs(&[
            &fx_keyword.span,
            &identifier.span,
            &TextSpan::combine(param_span),
            &body.span(self),
            return_type.as_ref().map_or(&TextSpan::default(), |rt| &rt.arrow.span),
            return_type.as_ref().map_or(&TextSpan::default(), |rt| &rt.type_name.span)
        ]);

        self.item_from_kind(ItemKind::Function(FxDeclaration { fx_keyword, identifier, parameters, body, return_type, index }), span)
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
    pub id: ItemId,
    pub span: TextSpan,
}

impl Item {
    pub fn new(kind: ItemKind, id: ItemId, span: TextSpan) -> Self {
        Self { kind, id, span }
    }
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    Statement(StatementId),
    Function(FxDeclaration),
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    Expression(ExpressionId),
    Let(LetStatement),
    While(WhileStatement),
    Return(ReturnStatement),
}

#[derive(Debug, Clone)]
pub struct Body {
    pub open_brace: Token,
    pub statements: Vec<StatementId>,
    pub close_brace: Token,
}

impl Body {
    pub fn new(open_brace: Token, statements: Vec<StatementId>, close_brace: Token) -> Self {
        Self { open_brace, statements, close_brace }
    }

    pub fn iter(&self) -> impl Iterator<Item = &StatementId> {
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
    type Target = Vec<StatementId>;

    fn deref(&self) -> &Self::Target {
        &self.statements
    }
}

#[derive(Debug, Clone)]
pub struct ReturnStatement {
    pub return_keyword: Token,
    pub return_value: Option<ExpressionId>,
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
        }
    }
}

#[derive(Debug, Clone)]
pub struct FxDeclarationParams {
    pub identifier: Token,
    pub type_annotation: StaticTypeAnnotation,
}

#[derive(Debug, Clone)]
pub struct FxReturnType {
    pub arrow: Token,
    pub type_name: Token,
}

impl FxReturnType {
    pub fn new(arrow: Token, type_name: Token) -> Self {
        Self { arrow, type_name }
    }
}

#[derive(Debug, Clone)]
pub struct FxDeclaration {
    pub fx_keyword: Token,
    pub identifier: Token,
    pub parameters: Vec<FxDeclarationParams>,
    pub body: Body,
    pub return_type: Option<FxReturnType>,
    pub index: FunctionIndex,
}

#[derive(Debug, Clone)]
pub struct WhileStatement {
    pub while_keyword: Token,
    pub condition: ExpressionId,
    pub body: Body,
}

#[derive(Debug, Clone)]
pub struct LetStatement {
    pub identifier: Token,
    pub initialiser: ExpressionId,
    pub type_annotation: Option<StaticTypeAnnotation>,
    pub variable_index: VariableIndex,
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub kind: StatementKind,
    pub id: StatementId,
    pub span: TextSpan,
}

impl Statement {
    pub fn new(kind: StatementKind, id: StatementId, span: TextSpan) -> Self {
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
        }
    }
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
pub struct IndexExpression {
    pub object: ExpressionId,
    pub indexes: Vec<ArrayIndex>,
}

#[derive(Debug, Clone)]
pub struct ArrayIndex {
    pub open_square_bracket: Token,
    pub index: ExpressionId,
    pub close_square_bracket: Token,
}

#[derive(Debug, Clone)]
pub struct ArrayExpression {
    pub type_decl: Token,
    pub open_square_bracket: Token,
    pub elements: Vec<ExpressionId>,
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
    pub statements: Vec<StatementId>,
    pub right_brace: Token,
}

impl BlockExpression {
    pub fn returning_expression(&self, ast: &Ast) -> Option<ExpressionId> {
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
    pub condition: ExpressionId,
    pub then_branch: Body,
    pub else_branch: Option<ElseBranch>,
}

#[derive(Debug, Clone)]
pub struct CallExpression {
    pub callee: Token,
    pub left_paren: Token,
    pub arguments: Vec<ExpressionId>,
    pub right_paren: Token,
    pub fx_idx: FunctionIndex,
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
    pub identifier: Token, 
    pub equals: Token,
    pub expression: ExpressionId,
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
    pub operand: ExpressionId,
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
    pub left: ExpressionId, // stored in heap instead of stack
    pub operator: BinaryOp,
    pub right: ExpressionId,
    pub from_compound: bool,
}

#[derive(Debug, Clone)]
pub struct CompoundBinaryExpression {
    pub left: ExpressionId,
    pub operator: AssignmentOpKind,
    pub operator_token: Token,
    pub right: ExpressionId,
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
    pub expression: ExpressionId,
    pub right_paren: Token,
}

#[derive(Debug, Clone)]
pub struct Expression {
    pub kind: ExpressionKind,
    pub id: ExpressionId,
    pub ty: Type,
    pub span: TextSpan,
}

impl Expression {
    pub fn new(kind: ExpressionKind, id: ExpressionId, ty: Type, span: TextSpan) -> Self {
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
                let identifier = expr.identifier.span.clone();
                let equals = expr.equals.span.clone();
                let expression = ast.query_expression(expr.expression).span(ast);

                TextSpan::combine(vec![identifier, equals, expression])
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
                let mut spans = vec![object_span];
                
                for array_index in &index_expression.indexes {
                    spans.push(array_index.open_square_bracket.span.clone());
                    spans.push(ast.query_expression(array_index.index).span(ast));
                    spans.push(array_index.close_square_bracket.span.clone());
                }

                TextSpan::combine(spans)
            },
            ExpressionKind::Error(span) => span.clone(),
        }
    }
}