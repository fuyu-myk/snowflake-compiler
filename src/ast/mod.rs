use std::{collections::HashMap};

use crate::ast::{lexer::{TextSpan, Token}, parser::Counter};
use visitor::ASTVisitor;
use printer::ASTPrinter;

pub mod lexer;
pub mod parser;
pub mod eval;
pub mod visitor;
pub mod printer;


#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct ASTStatementId {
    pub id: usize,
}

impl ASTStatementId {
    pub fn new(id: usize) -> Self {
        ASTStatementId { id }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct ASTExpressionId {
    pub id: usize,
}

impl ASTExpressionId {
    pub fn new(id: usize) -> Self {
        ASTExpressionId { id }
    }
}

#[derive(Debug, Clone)]
pub struct ASTNodeIdGen {
    pub next_statement_id: Counter,
    pub next_expression_id: Counter,
}

impl ASTNodeIdGen {
    pub fn new() -> Self {
        Self { next_statement_id: Counter::new(), next_expression_id: Counter::new() }
    }

    pub fn next_statement_id(&self) -> ASTStatementId {
        let id = self.next_statement_id.get_value();
        self.next_statement_id.increment();

        ASTStatementId::new(id)
    }

    pub fn next_expression_id(&self) -> ASTExpressionId {
        let id = self.next_expression_id.get_value();
        self.next_expression_id.increment();

        ASTExpressionId::new(id)
    }
}

#[derive(Debug, Clone)]
pub struct Ast {
    pub statements: HashMap<ASTStatementId, ASTStatement>,
    pub expressions: HashMap<ASTExpressionId, ASTExpression>,
    pub top_level_statements: Vec<ASTStatementId>,
    pub node_id_gen: ASTNodeIdGen,
}

impl Ast {
    pub fn new() -> Self {
        Self {
            statements: HashMap::new(),
            expressions: HashMap::new(),
            top_level_statements: Vec::new(),
            node_id_gen: ASTNodeIdGen::new(),
        }
    }

    pub fn query_statement(&self, stmt_id: &ASTStatementId) -> &ASTStatement {
        &self.statements[stmt_id]
    }

    pub fn query_expression(&self, expr_id: &ASTExpressionId) -> &ASTExpression {
        &self.expressions[expr_id]
    }

    pub fn mark_top_level_statement(&mut self, stmt_id: ASTStatementId) {
        self.top_level_statements.push(stmt_id);
    }

    // ASTStatement
    fn statement_from_kind(&mut self, kind: ASTStatementKind) -> &ASTStatement {
        let statement = ASTStatement::new(kind, self.node_id_gen.next_statement_id());
        let id = statement.id;

        self.statements.insert(id, statement);

        &self.statements[&id]
    }

    pub fn expression_statement(&mut self, expr_id: ASTExpressionId) -> &ASTStatement {
        self.statement_from_kind(ASTStatementKind::Expression(expr_id))
    }

    pub fn let_statement(&mut self, identifier: Token, expr_id: ASTExpressionId) -> &ASTStatement {
        self.statement_from_kind(ASTStatementKind::Let(ASTLetStatement { identifier, initialiser: expr_id }))
    }

    pub fn if_statement(&mut self, if_keyword: Token, condition: ASTExpressionId, then_branch: ASTStatementId, else_statement: Option<ASTElseStatement>) -> &ASTStatement {
        self.statement_from_kind(ASTStatementKind::If(ASTIfStatement { if_keyword, condition, then_branch, else_branch: else_statement }))
    }

    pub fn block_statement(&mut self, statements: Vec<ASTStatementId>) -> &ASTStatement {
        self.statement_from_kind(ASTStatementKind::Block(ASTBlockStatement { statements }))
    }

    pub fn while_statement(&mut self, while_keyword: Token, condition: ASTExpressionId, body: ASTStatementId) -> &ASTStatement {
        self.statement_from_kind(ASTStatementKind::While(ASTWhileStatement { while_keyword, condition, body }))
    }

    pub fn return_statement(&mut self, return_keyword: Token, return_value: Option<ASTExpressionId>) -> &ASTStatement {
        self.statement_from_kind(ASTStatementKind::Return(ASTReturnStatement { return_keyword, return_value }))
    }

    pub fn func_decl_statement(&mut self, identifier: Token, parameters: Vec<FxDeclarationParams>, body: ASTStatementId) -> &ASTStatement {
        self.statement_from_kind(ASTStatementKind::FxDeclaration(ASTFxDeclarationStatement { identifier, parameters, body }))
    }

    // ASTExpression
    pub fn expression_from_kind(&mut self, kind: ASTExpressionKind) -> &ASTExpression {
        let expression = ASTExpression::new(kind, self.node_id_gen.next_expression_id());
        let expr_id = expression.id;

        self.expressions.insert(expr_id, expression);

        &self.expressions[&expr_id]
    }

    pub fn number_expression(&mut self, token: Token, number: i64) -> &ASTExpression {
        self.expression_from_kind(ASTExpressionKind::Number(ASTNumberExpression { token, number }))
    }

    pub fn binary_expression(&mut self, operator: ASTBinaryOperator, left: ASTExpressionId, right: ASTExpressionId) -> &ASTExpression {
        self.expression_from_kind(ASTExpressionKind::Binary(ASTBinaryExpression { left, operator, right }))
    }

    pub fn unary_expression(&mut self, operator: ASTUnaryOperator, operand: ASTExpressionId) -> &ASTExpression {
        self.expression_from_kind(ASTExpressionKind::Unary(ASTUnaryExpression { operator, operand }))
    }

    pub fn parenthesised_expression(&mut self, expression: ASTExpressionId) -> &ASTExpression {
        self.expression_from_kind(ASTExpressionKind::Parenthesised(ASTParenthesisedExpression { expression }))
    }

    pub fn variable_expression(&mut self, identifier: Token) -> &ASTExpression {
        self.expression_from_kind(ASTExpressionKind::Variable(ASTVariableExpression { identifier }))
    }

    pub fn assignment_expression(&mut self, identifier: Token, expression: ASTExpressionId) -> &ASTExpression {
        self.expression_from_kind(ASTExpressionKind::Assignment(ASTAssignmentExpression { identifier, expression }))
    }

    pub fn boolean_expression(&mut self, token: Token, value: bool) -> &ASTExpression {
        self.expression_from_kind(ASTExpressionKind::Boolean(ASTBooleanExpression { value, token }))
    }

    pub fn call_expression(&mut self, identifier: Token, arguments: Vec<ASTExpressionId>) -> &ASTExpression {
        self.expression_from_kind(ASTExpressionKind::Call(ASTCallExpression { identifier, arguments }))
    }

    pub fn error_expression(&mut self, span: TextSpan) -> &ASTExpression {
        self.expression_from_kind(ASTExpressionKind::Error(span))
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
pub enum ASTStatementKind {
    Expression(ASTExpressionId),
    Let(ASTLetStatement),
    If(ASTIfStatement),
    Block(ASTBlockStatement),
    While(ASTWhileStatement),
    FxDeclaration(ASTFxDeclarationStatement),
    Return(ASTReturnStatement),
}

#[derive(Debug, Clone)]
pub struct ASTReturnStatement {
    pub return_keyword: Token,
    pub return_value: Option<ASTExpressionId>,
}

#[derive(Debug, Clone)]
pub struct FxDeclarationParams {
    pub identifier: Token,
}

#[derive(Debug, Clone)]
pub struct ASTFxDeclarationStatement {
    pub identifier: Token,
    pub parameters: Vec<FxDeclarationParams>,
    pub body: ASTStatementId
}

#[derive(Debug, Clone)]
pub struct ASTWhileStatement {
    pub while_keyword: Token,
    pub condition: ASTExpressionId,
    pub body: ASTStatementId,
}

#[derive(Debug, Clone)]
pub struct ASTBlockStatement {
    pub statements: Vec<ASTStatementId>,
}

#[derive(Debug, Clone)]
pub struct ASTElseStatement {
    pub else_keyword: Token,
    pub else_statement: ASTStatementId,
}

impl ASTElseStatement {
    pub fn new(else_keyword: Token, else_statement: ASTStatementId) -> Self {
        ASTElseStatement { else_keyword, else_statement }
    }
}

#[derive(Debug, Clone)]
pub struct ASTIfStatement {
    pub if_keyword: Token,
    pub condition: ASTExpressionId,
    pub then_branch: ASTStatementId,
    pub else_branch: Option<ASTElseStatement>,
}

#[derive(Debug, Clone)]
pub struct ASTLetStatement {
    pub identifier: Token,
    pub initialiser: ASTExpressionId,
}

#[derive(Debug, Clone)]
pub struct ASTStatement {
    kind: ASTStatementKind,
    id: ASTStatementId,
}

impl ASTStatement {
    pub fn new(kind: ASTStatementKind, id: ASTStatementId) -> Self {
        ASTStatement { kind, id }
    }
}

#[derive(Debug, Clone)]
pub enum ASTExpressionKind {
    Number(
        ASTNumberExpression
    ),
    Binary(
        ASTBinaryExpression
    ),
    Unary(
        ASTUnaryExpression
    ),
    Parenthesised(
        ASTParenthesisedExpression
    ),
    Variable(
        ASTVariableExpression
    ),
    Assignment(
        ASTAssignmentExpression
    ),
    Boolean(
        ASTBooleanExpression
    ),
    Call(
        ASTCallExpression
    ),
    Error(
        TextSpan
    )
}

#[derive(Debug, Clone)]
pub struct ASTCallExpression {
    pub identifier: Token,
    pub arguments: Vec<ASTExpressionId>,
}

#[derive(Debug, Clone)]
pub struct ASTBooleanExpression {
    pub value: bool,
    pub token: Token,
}

#[derive(Debug, Clone)]
pub struct ASTAssignmentExpression {
    pub identifier: Token, 
    pub expression: ASTExpressionId,
}

#[derive(Debug, Clone)]
pub enum ASTUnaryOperatorKind {
    Negation, // unary minus
    BitwiseNot, // ~
}

#[derive(Debug, Clone)]
pub struct ASTUnaryOperator {
    kind: ASTUnaryOperatorKind,
    token: Token,
}

impl ASTUnaryOperator {
    pub fn new(kind: ASTUnaryOperatorKind, token: Token) -> Self {
        ASTUnaryOperator { kind, token }
    }
}

#[derive(Debug, Clone)]
pub struct ASTUnaryExpression {
    pub operator: ASTUnaryOperator,
    pub operand: ASTExpressionId,
}

#[derive(Debug, Clone)]
pub struct ASTVariableExpression {
    pub identifier: Token,
}

impl ASTVariableExpression {
    pub fn identifier(&self) -> &str {
        &self.identifier.span.literal
    }
}

#[derive(Debug, Clone)]
pub enum ASTBinaryOperatorKind {
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
pub enum ASTBinaryOperatorAssociativity {
    Left,
    Right,
}

#[derive(Debug, Clone)]
pub struct ASTBinaryOperator {
    kind: ASTBinaryOperatorKind,
    token: Token,
}

impl ASTBinaryOperator {
    pub fn new(kind: ASTBinaryOperatorKind, token: Token) -> Self {
        ASTBinaryOperator { kind, token }
    }

    pub fn precedence(&self) -> u8 {
        match self.kind {
            ASTBinaryOperatorKind::Equals => 30,
            ASTBinaryOperatorKind::NotEquals => 30,
            ASTBinaryOperatorKind::LessThan => 29,
            ASTBinaryOperatorKind::GreaterThan => 29,
            ASTBinaryOperatorKind::LessThanOrEqual => 29,
            ASTBinaryOperatorKind::GreaterThanOrEqual => 29,
            ASTBinaryOperatorKind::Power => 20,
            ASTBinaryOperatorKind::Multiply => 19,
            ASTBinaryOperatorKind::Divide => 19,
            ASTBinaryOperatorKind::Plus => 18,
            ASTBinaryOperatorKind::Minus => 18,
            ASTBinaryOperatorKind::BitwiseAnd => 17,
            ASTBinaryOperatorKind::BitwiseXor => 16,
            ASTBinaryOperatorKind::BitwiseOr => 15,
        }
    }

    pub fn associativity(&self) -> ASTBinaryOperatorAssociativity {
        match self.kind {
            ASTBinaryOperatorKind::Power => ASTBinaryOperatorAssociativity::Right,
            _ => ASTBinaryOperatorAssociativity::Left,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ASTBinaryExpression {
    left: ASTExpressionId, // stored in heap instead of stack
    operator: ASTBinaryOperator,
    right: ASTExpressionId,
}

#[derive(Debug, Clone)]
pub struct ASTNumberExpression {
    token: Token,
    number: i64,
}

#[derive(Debug, Clone)]
pub struct ASTParenthesisedExpression {
    expression: ASTExpressionId,
}

#[derive(Debug, Clone)]
pub struct ASTExpression {
    kind: ASTExpressionKind,
    id: ASTExpressionId,
}

impl ASTExpression {
    pub fn new(kind: ASTExpressionKind, id: ASTExpressionId) -> Self {
        ASTExpression { kind, id }
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

        fn visit_let_statement(&mut self, let_statement: &ASTLetStatement) {
            self.actual.push(TestASTNode::Let);
            self.visit_expression(&let_statement.initialiser);
        }

        fn visit_variable_expression(&mut self, variable_expression: &ASTVariableExpression) {
            self.actual.push(TestASTNode::Variable(variable_expression.identifier().to_string()));
        }

        fn visit_number_expression(&mut self, number: &ASTNumberExpression) {
            self.actual.push(TestASTNode::Number(number.number));
        }

        fn visit_error(&mut self, span: &TextSpan) {
            // do nothing
        }

        fn visit_parenthesised_expression(&mut self, parenthesised_expression:&ASTParenthesisedExpression) {
            self.actual.push(TestASTNode::Parenthesised);
            self.visit_expression(&parenthesised_expression.expression);
        }

        fn visit_binary_expression(&mut self, binary_expression: &ASTBinaryExpression) {
            self.actual.push(TestASTNode::Binary);
            self.visit_expression(&binary_expression.left);
            self.visit_expression(&binary_expression.right);
        }

        fn visit_unary_expression(&mut self, unary_expression: &ASTUnaryExpression) {
            self.actual.push(TestASTNode::Unary);
            self.visit_expression(&unary_expression.operand);
        }

        fn visit_if_statement(&mut self, if_statement: &ASTIfStatement) {
            self.actual.push(TestASTNode::If);
            self.visit_expression(&if_statement.condition);
            self.visit_statement(&if_statement.then_branch);

            if let Some(else_branch) = &if_statement.else_branch {
                self.actual.push(TestASTNode::Else);
                
                self.visit_statement(&else_branch.else_statement);
            }
        }

        fn visit_boolean_expression(&mut self, boolean: &ASTBooleanExpression) {
            self.actual.push(TestASTNode::Boolean(boolean.value));
        }

        fn visit_block_statement(&mut self, block_statement: &ASTBlockStatement) {
            self.actual.push(TestASTNode::Block);

            for statement in &block_statement.statements {
                self.visit_statement(statement);
            }
        }

        fn visit_assignment_expression(&mut self, assignment_expression: &ASTAssignmentExpression) {
            self.actual.push(TestASTNode::Assignment);
            self.visit_expression(&assignment_expression.expression);
        }

        fn visit_while_statement(&mut self, while_statement: &ASTWhileStatement) {
            self.actual.push(TestASTNode::While);
            self.visit_expression(&while_statement.condition);
            self.visit_statement(&while_statement.body);
        }

        fn visit_function_declaration_statement(&mut self, fx_decl_statement: &ASTFxDeclarationStatement) {
            self.actual.push(TestASTNode::Function);
            self.visit_statement(&fx_decl_statement.body);
        }

        fn visit_return_statement(&mut self, return_statement: &ASTReturnStatement) {
            self.actual.push(TestASTNode::Return);
            if let Some(expression) = &return_statement.return_value {
                self.visit_expression(expression);
            }
        }

        fn visit_call_expression(&mut self, call_expression: &ASTCallExpression) {
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
        fx add(a, b) {
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
        fx add(a, b) {
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