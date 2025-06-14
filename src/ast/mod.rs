use std::{collections::HashMap};

use crate::{ast::{lexer::Token, parser::Counter}, text::span::TextSpan, typings::Type};
use visitor::ASTVisitor;
use printer::ASTPrinter;

pub mod lexer;
pub mod parser;
pub mod eval;
pub mod visitor;
pub mod printer;


#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct StatementId {
    pub id: usize,
}

impl StatementId {
    pub fn new(id: usize) -> Self {
        StatementId { id }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct ExpressionId {
    pub id: usize,
}

impl ExpressionId {
    pub fn new(id: usize) -> Self {
        ExpressionId { id }
    }
}

#[derive(Debug, Clone)]
pub struct NodeIdGen {
    pub next_statement_id: Counter,
    pub next_expression_id: Counter,
}

impl NodeIdGen {
    pub fn new() -> Self {
        Self { next_statement_id: Counter::new(), next_expression_id: Counter::new() }
    }

    pub fn next_statement_id(&self) -> StatementId {
        let id = self.next_statement_id.get_value();
        self.next_statement_id.increment();

        StatementId::new(id)
    }

    pub fn next_expression_id(&self) -> ExpressionId {
        let id = self.next_expression_id.get_value();
        self.next_expression_id.increment();

        ExpressionId::new(id)
    }
}

#[derive(Debug, Clone)]
pub struct Ast {
    pub statements: HashMap<StatementId, Statement>,
    pub expressions: HashMap<ExpressionId, Expression>,
    pub top_level_statements: Vec<StatementId>,
    pub node_id_gen: NodeIdGen,
}

impl Ast {
    pub fn new() -> Self {
        Self {
            statements: HashMap::new(),
            expressions: HashMap::new(),
            top_level_statements: Vec::new(),
            node_id_gen: NodeIdGen::new(),
        }
    }

    pub fn query_statement(&self, stmt_id: &StatementId) -> &Statement {
        &self.statements[stmt_id]
    }

    pub fn query_expression(&self, expr_id: &ExpressionId) -> &Expression {
        &self.expressions[expr_id]
    }

    pub fn mark_top_level_statement(&mut self, stmt_id: StatementId) {
        self.top_level_statements.push(stmt_id);
    }

    pub fn set_type(&mut self, expr_id: &ExpressionId, ty: Type) {
        let expr = self.expressions.get_mut(expr_id).unwrap();
        expr.ty = ty;
    }

    // ASTStatement
    fn statement_from_kind(&mut self, kind: StatementKind) -> &Statement {
        let statement = Statement::new(kind, self.node_id_gen.next_statement_id());
        let id = statement.id;

        self.statements.insert(id, statement);

        &self.statements[&id]
    }

    pub fn expression_statement(&mut self, expr_id: ExpressionId) -> &Statement {
        self.statement_from_kind(StatementKind::Expression(expr_id))
    }

    pub fn let_statement(&mut self, identifier: Token, expr_id: ExpressionId, type_annotation: Option<StaticTypeAnnotation>) -> &Statement {
        self.statement_from_kind(StatementKind::Let(LetStatement { identifier, initialiser: expr_id, type_annotation }))
    }

    pub fn if_statement(&mut self, if_keyword: Token, condition: ExpressionId, then_branch: StatementId, else_statement: Option<ElseStatement>) -> &Statement {
        self.statement_from_kind(StatementKind::If(IfStatement { if_keyword, condition, then_branch, else_branch: else_statement }))
    }

    pub fn block_statement(&mut self, statements: Vec<StatementId>) -> &Statement {
        self.statement_from_kind(StatementKind::Block(BlockStatement { statements }))
    }

    pub fn while_statement(&mut self, while_keyword: Token, condition: ExpressionId, body: StatementId) -> &Statement {
        self.statement_from_kind(StatementKind::While(WhileStatement { while_keyword, condition, body }))
    }

    pub fn return_statement(&mut self, return_keyword: Token, return_value: Option<ExpressionId>) -> &Statement {
        self.statement_from_kind(StatementKind::Return(ReturnStatement { return_keyword, return_value }))
    }

    pub fn func_decl_statement(&mut self, identifier: Token, parameters: Vec<FxDeclarationParams>, body: StatementId, return_type: Option<FxReturnType>) -> &Statement {
        self.statement_from_kind(StatementKind::FxDeclaration(FxDeclarationStatement { identifier, parameters, body, return_type }))
    }

    // ASTExpression
    pub fn expression_from_kind(&mut self, kind: ExpressionKind) -> &Expression {
        let expression = Expression::new(kind, self.node_id_gen.next_expression_id(), Type::Unresolved);
        let expr_id = expression.id;

        self.expressions.insert(expr_id, expression);

        &self.expressions[&expr_id]
    }

    pub fn number_expression(&mut self, token: Token, number: i64) -> &Expression {
        self.expression_from_kind(ExpressionKind::Number(NumberExpression { token, number }))
    }

    pub fn binary_expression(&mut self, operator: BinaryOp, left: ExpressionId, right: ExpressionId) -> &Expression {
        self.expression_from_kind(ExpressionKind::Binary(BinaryExpression { left, operator, right }))
    }

    pub fn unary_expression(&mut self, operator: UnaryOp, operand: ExpressionId) -> &Expression {
        self.expression_from_kind(ExpressionKind::Unary(UnaryExpression { operator, operand }))
    }

    pub fn parenthesised_expression(&mut self, left_paren:Token, expression: ExpressionId, right_paren: Token) -> &Expression {
        self.expression_from_kind(ExpressionKind::Parenthesised(ParenExpression { left_paren, expression, right_paren }))
    }

    pub fn variable_expression(&mut self, identifier: Token) -> &Expression {
        self.expression_from_kind(ExpressionKind::Variable(VarExpression { identifier }))
    }

    pub fn assignment_expression(&mut self, identifier: Token, equals: Token, expression: ExpressionId) -> &Expression {
        self.expression_from_kind(ExpressionKind::Assignment(AssignExpression { identifier, equals, expression }))
    }

    pub fn boolean_expression(&mut self, token: Token, value: bool) -> &Expression {
        self.expression_from_kind(ExpressionKind::Boolean(BoolExpression { value, token }))
    }

    pub fn call_expression(&mut self, identifier: Token, left_paren:Token, arguments: Vec<ExpressionId>, right_paren: Token) -> &Expression {
        self.expression_from_kind(ExpressionKind::Call(CallExpression { identifier, left_paren, arguments, right_paren }))
    }

    pub fn error_expression(&mut self, span: TextSpan) -> &Expression {
        self.expression_from_kind(ExpressionKind::Error(span))
    }

    pub fn visit(&self, visitor: &mut dyn ASTVisitor) {
        for statement in &self.top_level_statements {
            visitor.visit_statement(statement);
        }
    }

    pub fn visualise(&self) -> () {
        let mut printer = ASTPrinter::new(self);
        self.visit(&mut printer);
        println!("{}", printer.result);
    }
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    Expression(ExpressionId),
    Let(LetStatement),
    If(IfStatement),
    Block(BlockStatement),
    While(WhileStatement),
    FxDeclaration(FxDeclarationStatement),
    Return(ReturnStatement),
}

#[derive(Debug, Clone)]
pub struct ReturnStatement {
    pub return_keyword: Token,
    pub return_value: Option<ExpressionId>,
}

#[derive(Debug, Clone)]
pub struct StaticTypeAnnotation {
    pub colon: Token,
    pub type_name: Token,
}

impl StaticTypeAnnotation {
    pub fn new(colon: Token, type_name: Token) -> Self {
        Self { colon, type_name }
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
pub struct FxDeclarationStatement {
    pub identifier: Token,
    pub parameters: Vec<FxDeclarationParams>,
    pub body: StatementId,
    pub return_type: Option<FxReturnType>,
}

#[derive(Debug, Clone)]
pub struct WhileStatement {
    pub while_keyword: Token,
    pub condition: ExpressionId,
    pub body: StatementId,
}

#[derive(Debug, Clone)]
pub struct BlockStatement {
    pub statements: Vec<StatementId>,
}

#[derive(Debug, Clone)]
pub struct ElseStatement {
    pub else_keyword: Token,
    pub else_statement: StatementId,
}

impl ElseStatement {
    pub fn new(else_keyword: Token, else_statement: StatementId) -> Self {
        ElseStatement { else_keyword, else_statement }
    }
}

#[derive(Debug, Clone)]
pub struct IfStatement {
    pub if_keyword: Token,
    pub condition: ExpressionId,
    pub then_branch: StatementId,
    pub else_branch: Option<ElseStatement>,
}

#[derive(Debug, Clone)]
pub struct LetStatement {
    pub identifier: Token,
    pub initialiser: ExpressionId,
    pub type_annotation: Option<StaticTypeAnnotation>,
}

#[derive(Debug, Clone)]
pub struct Statement {
    kind: StatementKind,
    id: StatementId,
}

impl Statement {
    pub fn new(kind: StatementKind, id: StatementId) -> Self {
        Statement { kind, id }
    }
}

#[derive(Debug, Clone)]
pub enum ExpressionKind {
    Number(
        NumberExpression
    ),
    Binary(
        BinaryExpression
    ),
    Unary(
        UnaryExpression
    ),
    Parenthesised(
        ParenExpression
    ),
    Variable(
        VarExpression
    ),
    Assignment(
        AssignExpression
    ),
    Boolean(
        BoolExpression
    ),
    Call(
        CallExpression
    ),
    Error(
        TextSpan
    )
}

#[derive(Debug, Clone)]
pub struct CallExpression {
    pub identifier: Token,
    pub left_paren: Token,
    pub arguments: Vec<ExpressionId>,
    pub right_paren: Token,
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
}

#[derive(Debug, Clone)]
pub enum UnaryOpKind {
    Negation, // unary minus
    BitwiseNot, // ~
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
}

impl VarExpression {
    pub fn identifier(&self) -> &str {
        &self.identifier.span.literal
    }
}

#[derive(Debug, Clone)]
pub enum BinaryOpKind {
    // arithmentic
    Plus,
    Minus,
    Multiply,
    Divide,
    Power,
    // bitwise
    BitwiseAnd, // &
    BitwiseOr,  // |
    BitwiseXor, // ^
    // relational
    Equals,
    NotEquals,
    LessThan,
    GreaterThan,
    LessThanOrEqual,
    GreaterThanOrEqual,
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
            BinaryOpKind::Equals => 30,
            BinaryOpKind::NotEquals => 30,
            BinaryOpKind::LessThan => 29,
            BinaryOpKind::GreaterThan => 29,
            BinaryOpKind::LessThanOrEqual => 29,
            BinaryOpKind::GreaterThanOrEqual => 29,
            BinaryOpKind::Power => 20,
            BinaryOpKind::Multiply => 19,
            BinaryOpKind::Divide => 19,
            BinaryOpKind::Plus => 18,
            BinaryOpKind::Minus => 18,
            BinaryOpKind::BitwiseAnd => 17,
            BinaryOpKind::BitwiseXor => 16,
            BinaryOpKind::BitwiseOr => 15,
        }
    }

    pub fn associativity(&self) -> BinaryOpAssociativity {
        match self.kind {
            BinaryOpKind::Power => BinaryOpAssociativity::Right,
            _ => BinaryOpAssociativity::Left,
        }
    }
}

#[derive(Debug, Clone)]
pub struct BinaryExpression {
    pub left: ExpressionId, // stored in heap instead of stack
    pub operator: BinaryOp,
    pub right: ExpressionId,
}

#[derive(Debug, Clone)]
pub struct NumberExpression {
    pub token: Token,
    pub number: i64,
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
}

impl Expression {
    pub fn new(kind: ExpressionKind, id: ExpressionId, ty: Type) -> Self {
        Expression { kind, id, ty }
    }

    pub fn span(&self, ast: &Ast) -> TextSpan {
        match &self.kind {
            ExpressionKind::Number(expr) => expr.token.span.clone(),
            ExpressionKind::Binary(expr) => {
                let left = ast.query_expression(&expr.left).span(ast);
                let operator = expr.operator.token.span.clone();
                let right = ast.query_expression(&expr.right).span(ast);

                TextSpan::combine(vec![left, operator, right])
            },
            ExpressionKind::Unary(expr) => {
                let operator = expr.operator.token.span.clone();
                let operand = ast.query_expression(&expr.operand).span(ast);

                TextSpan::combine(vec![operator, operand])
            },
            ExpressionKind::Parenthesised(expr) => {
                let open_paren = expr.left_paren.span.clone();
                let expression = ast.query_expression(&expr.expression).span(ast);
                let close_paren = expr.right_paren.span.clone();

                TextSpan::combine(vec![open_paren, expression, close_paren])
            },
            ExpressionKind::Variable(expr) => expr.identifier.span.clone(),
            ExpressionKind::Assignment(expr) => {
                let identifier = expr.identifier.span.clone();
                let equals = expr.equals.span.clone();
                let expression = ast.query_expression(&expr.expression).span(ast);

                TextSpan::combine(vec![identifier, equals, expression])
            },
            ExpressionKind::Boolean(expr) => expr.token.span.clone(),
            ExpressionKind::Call(expr) => {
                let identifier = expr.identifier.span.clone();
                let left_paren = expr.left_paren.span.clone();
                let right_paren = expr.right_paren.span.clone();
                let mut spans = vec![identifier, left_paren, right_paren];

                for arg in &expr.arguments {
                    spans.push(ast.query_expression(arg).span(ast));
                }

                TextSpan::combine(spans)
            },
            ExpressionKind::Error(span) => span.clone(),
        }
    }
}

/*
 * The goal for the below module is to flatten the AST into a single line of statements
 * Useful for debugging and visualising
 * Inclusive of all statements, expressions and their relationships
 */
#[cfg(test)]
mod tests {
    use super::*;
    use crate::compilation_unit::CompilationUnit;


    #[derive(Debug, PartialEq, Eq)]
    enum TestASTNode {
        Number(i64),
        Boolean(bool),
        Binary,
        Unary,
        Parenthesised,
        Let,
        Assignment,
        Block,
        Variable(String),
        If,
        Else,
        While,
        Function,
        Return,
        Call,
    }

    struct ASTVerifier {
        expected: Vec<TestASTNode>,
        actual: Vec<TestASTNode>,
        ast: Ast,
    }

    impl ASTVerifier {
        pub fn new(input: &str, expected: Vec<TestASTNode>) -> Self {
            let compilation_unit = CompilationUnit::compile(input).expect("Failed to compile");

            let mut verifier = ASTVerifier { expected, actual: Vec::new(), ast: compilation_unit.ast };
            verifier.flatten_ast();

            verifier
        }

        fn flatten_ast(&mut self) {
            self.actual.clear();
            let ast = &self.ast.clone();

            ast.visit(&mut *self);
        }

        pub fn verify(&self) {
            // ensure the expected and actual AST nodes match
            assert_eq!(self.expected.len(), self.actual.len(), "Expected {} nodes, but got {}.\nActual nodes: {:?}", self.expected.len(), self.actual.len(), self.actual);

            for (index, (expected, actual)) in self.expected.iter().zip(self.actual.iter()).enumerate() {
                assert_eq!(expected, actual, "Expected {:?} at index {}, but got {:?}", expected, index, actual);
            }
        }
    }

    impl ASTVisitor for ASTVerifier {
        fn get_ast(&self) -> &Ast {
            &self.ast
        }

        fn visit_let_statement(&mut self, let_statement: &LetStatement) {
            self.actual.push(TestASTNode::Let);
            self.visit_expression(&let_statement.initialiser);
        }

        fn visit_variable_expression(&mut self, variable_expression: &VarExpression, expr: &Expression) {
            self.actual.push(TestASTNode::Variable(variable_expression.identifier().to_string()));
        }

        fn visit_number_expression(&mut self, number: &NumberExpression, expr: &Expression) {
            self.actual.push(TestASTNode::Number(number.number));
        }

        fn visit_error(&mut self, span: &TextSpan) {
            // do nothing
        }

        fn visit_parenthesised_expression(&mut self, parenthesised_expression:&ParenExpression, expr: &Expression) {
            self.actual.push(TestASTNode::Parenthesised);
            self.visit_expression(&parenthesised_expression.expression);
        }

        fn visit_binary_expression(&mut self, binary_expression: &BinaryExpression, expr: &Expression) {
            self.actual.push(TestASTNode::Binary);
            self.visit_expression(&binary_expression.left);
            self.visit_expression(&binary_expression.right);
        }

        fn visit_unary_expression(&mut self, unary_expression: &UnaryExpression, expr: &Expression) {
            self.actual.push(TestASTNode::Unary);
            self.visit_expression(&unary_expression.operand);
        }

        fn visit_if_statement(&mut self, if_statement: &IfStatement) {
            self.actual.push(TestASTNode::If);
            self.visit_expression(&if_statement.condition);
            self.visit_statement(&if_statement.then_branch);

            if let Some(else_branch) = &if_statement.else_branch {
                self.actual.push(TestASTNode::Else);
                
                self.visit_statement(&else_branch.else_statement);
            }
        }

        fn visit_boolean_expression(&mut self, boolean: &BoolExpression, expr: &Expression) {
            self.actual.push(TestASTNode::Boolean(boolean.value));
        }

        fn visit_block_statement(&mut self, block_statement: &BlockStatement) {
            self.actual.push(TestASTNode::Block);

            for statement in &block_statement.statements {
                self.visit_statement(statement);
            }
        }

        fn visit_assignment_expression(&mut self, assignment_expression: &AssignExpression, expr: &Expression) {
            self.actual.push(TestASTNode::Assignment);
            self.visit_expression(&assignment_expression.expression);
        }

        fn visit_while_statement(&mut self, while_statement: &WhileStatement) {
            self.actual.push(TestASTNode::While);
            self.visit_expression(&while_statement.condition);
            self.visit_statement(&while_statement.body);
        }

        fn visit_function_declaration_statement(&mut self, fx_decl_statement: &FxDeclarationStatement) {
            self.actual.push(TestASTNode::Function);
            self.visit_statement(&fx_decl_statement.body);
        }

        fn visit_return_statement(&mut self, return_statement: &ReturnStatement) {
            self.actual.push(TestASTNode::Return);
            if let Some(expression) = &return_statement.return_value {
                self.visit_expression(expression);
            }
        }

        fn visit_call_expression(&mut self, call_expression: &CallExpression, expr: &Expression) {
            self.actual.push(TestASTNode::Call);
            for argument in &call_expression.arguments {
                self.visit_expression(argument);
            }
        }
    }

    fn assert_tree(input: &str, expected: Vec<TestASTNode>) {
        let verifier = ASTVerifier::new(input, expected);
        verifier.verify();
    }

    #[test]
    pub fn test_basic_binary_expression() {
        let input = "let a = 1 + 2";
        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Number(1),
            TestASTNode::Number(2),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_parenthesised_binary_expression() {
        let input = "let a = (6 + 9) * 42";
        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Parenthesised,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
            TestASTNode::Number(42),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_parenthesised_binary_expression_with_variable() {
        let input = "
        let b = 2
        let a = (6 + 9) * b";
        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Number(2),
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Parenthesised,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
            TestASTNode::Variable("b".to_string()),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_nested_parenthesised_binary_expression() {
        let input = "
        let b = 1
        let c = 2
        let a = (b + (c * 2)) / 3";

        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Number(1),
            TestASTNode::Let,
            TestASTNode::Number(2),
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Parenthesised,
            TestASTNode::Binary,
            TestASTNode::Variable("b".to_string()),
            TestASTNode::Parenthesised,
            TestASTNode::Binary,
            TestASTNode::Variable("c".to_string()),
            TestASTNode::Number(2),
            TestASTNode::Number(3),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_parenthesised_binary_expression_with_variable_and_number() {
        let input = "
        let b = 1
        let a = (6 + 9) * b + 42";

        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Number(1),
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Binary,
            TestASTNode::Parenthesised,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
            TestASTNode::Variable("b".to_string()),
            TestASTNode::Number(42),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_bitwise_and() {
        let input = "let a = 6 & 9";
        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_bitwise_or() {
        let input = "let a = 6 | 9";
        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_bitwise_xor() {
        let input = "let a = 6 ^ 9";
        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_bitwise_not() {
        let input = "let a = ~1";
        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Unary,
            TestASTNode::Number(1),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_negation() {
        let input = "let a = -1";
        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Unary,
            TestASTNode::Number(1),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_power() {
        let input = "let a = 2 ** 3";
        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Number(2),
            TestASTNode::Number(3),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_loooong_unary_exps() {
        let input = "let a = -1 + -2 * -3 ** ------4";
        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Unary,
            TestASTNode::Number(1),
            TestASTNode::Binary,
            TestASTNode::Unary,
            TestASTNode::Number(2),
            TestASTNode::Binary,
            TestASTNode::Unary,
            TestASTNode::Number(3),
            TestASTNode::Unary,
            TestASTNode::Unary,
            TestASTNode::Unary,
            TestASTNode::Unary,
            TestASTNode::Unary,
            TestASTNode::Unary,
            TestASTNode::Number(4),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_if_statement() {
        let input = "\
        let a = 1
        
        if a > 0 {
            a = 86
        }
        ";

        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Number(1),
            TestASTNode::If,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Number(0),
            TestASTNode::Block,
            TestASTNode::Assignment,
            TestASTNode::Number(86),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_if_else_statement() {
        let input = "\
        let a = 1
        
        if a > 0 {
            a = 86
        } else {
            a = 23
        }
        ";

        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Number(1),
            TestASTNode::If,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Number(0),
            TestASTNode::Block,
            TestASTNode::Assignment,
            TestASTNode::Number(86),
            TestASTNode::Else,
            TestASTNode::Block,
            TestASTNode::Assignment,
            TestASTNode::Number(23),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_while_statement() {
        let input = "\
        let a = 1

        while a < 10 {
            a = a + 1
        }
        ";

        let expected = vec![
            TestASTNode::Let,
            TestASTNode::Number(1),
            TestASTNode::While,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Number(10),
            TestASTNode::Block,
            TestASTNode::Assignment,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Number(1),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_function_declaration() { // parses function declaration properly
        let input = "\
        fx add(a: int, b: int) -> int {
            return a + b
        }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Block,
            TestASTNode::Return,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Variable("b".to_string()),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_call_expression() { // parses call expressions properly
        let input = "\
        fx add(a: int, b: int) -> int {
            return a + b
        }

        add(2 * 3, 4 + 5)
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Block,
            TestASTNode::Return,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Variable("b".to_string()),
            TestASTNode::Call,
            TestASTNode::Binary,
            TestASTNode::Number(2),
            TestASTNode::Number(3),
            TestASTNode::Binary,
            TestASTNode::Number(4),
            TestASTNode::Number(5),
        ];

        assert_tree(input, expected);
    }
}