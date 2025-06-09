use crate::ast::lexer::{Token, TextSpan};
use visitor::ASTVisitor;
use printer::ASTPrinter;

pub mod lexer;
pub mod parser;
pub mod eval;
pub mod visitor;
pub mod printer;


pub struct Ast {
    pub statements: Vec<ASTStatement>
}

impl Ast {
    pub fn new() -> Self {
        Self { statements: Vec::new() }
    }

    pub fn add_statement(&mut self, statement: ASTStatement) {
        self.statements.push(statement);
    }

    pub fn visit(&self, visitor: &mut dyn ASTVisitor) {
        for statement in &self.statements {
            visitor.visit_statement(statement);
        }
    }

    pub fn visualise(&self) -> () {
        let mut printer = ASTPrinter::new();
        self.visit(&mut printer);
        println!("{}", printer.result);
    }
}

pub enum ASTStatementKind {
    Expression(ASTExpression),
    Let(ASTLetStatement),
    If(ASTIfStatement),
    Block(ASTBlockStatement),
}

pub struct ASTBlockStatement {
    pub statements: Vec<ASTStatement>,
}

pub struct ASTElseStatement {
    pub else_keyword: Token,
    pub else_statement: Box<ASTStatement>,
}

impl ASTElseStatement {
    pub fn new(else_keyword: Token, else_statement: ASTStatement) -> Self {
        ASTElseStatement { else_keyword, else_statement: Box::new(else_statement) }
    }
}

pub struct ASTIfStatement {
    pub if_keyword: Token,
    pub condition: ASTExpression,
    pub then_branch: Box<ASTStatement>,
    pub else_branch: Option<ASTElseStatement>,
}

#[derive(Debug, Clone)]
pub struct ASTLetStatement {
    pub identifier: Token,
    pub initialiser: ASTExpression,
}

pub struct ASTStatement {
    kind: ASTStatementKind,
}

impl ASTStatement {
    pub fn new(kind: ASTStatementKind) -> Self {
        ASTStatement { kind }
    }

    pub fn expression(expr: ASTExpression) -> Self {
        ASTStatement::new(ASTStatementKind::Expression(expr))
    }

    pub fn let_statement(identifier: Token, initialiser: ASTExpression) -> Self {
        ASTStatement::new(ASTStatementKind::Let(ASTLetStatement { identifier, initialiser }))
    }

    pub fn if_statement(if_keyword: Token, condition: ASTExpression, then_branch: ASTStatement, else_statement: Option<ASTElseStatement>) -> Self {
        ASTStatement::new(ASTStatementKind::If(ASTIfStatement { if_keyword, condition, then_branch: Box::new(then_branch), else_branch: else_statement }))
    }

    pub fn block_statement(statements: Vec<ASTStatement>) -> Self {
        ASTStatement::new(ASTStatementKind::Block(ASTBlockStatement { statements }))
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
    Error(
        TextSpan
    )
}

#[derive(Debug, Clone)]
pub struct ASTBooleanExpression {
    pub value: bool,
    pub token: Token,
}

#[derive(Debug, Clone)]
pub struct ASTAssignmentExpression {
    pub identifier: Token, 
    pub expression: Box<ASTExpression>,
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
    pub operand: Box<ASTExpression>,
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
    left: Box<ASTExpression>, // stored in heap instead of stack
    operator: ASTBinaryOperator,
    right: Box<ASTExpression>,
}

#[derive(Debug, Clone)]
pub struct ASTNumberExpression {
    number: i64,
}

#[derive(Debug, Clone)]
pub struct ASTParenthesisedExpression {
    expression: Box<ASTExpression>,
}

#[derive(Debug, Clone)]
pub struct ASTExpression {
    kind: ASTExpressionKind,
}

impl ASTExpression {
    pub fn new(kind: ASTExpressionKind) -> Self {
        ASTExpression { kind }
    }

    pub fn number(number: i64) -> Self {
        ASTExpression::new(ASTExpressionKind::Number(ASTNumberExpression{ number }))
    }

    pub fn binary(operator: ASTBinaryOperator, left: ASTExpression, right: ASTExpression) -> Self {
        ASTExpression::new(ASTExpressionKind::Binary(ASTBinaryExpression{ left: Box::new(left), operator, right: Box::new(right) }))
    }

    pub fn unary(operator: ASTUnaryOperator, operand: ASTExpression) -> Self {
        ASTExpression::new(ASTExpressionKind::Unary(ASTUnaryExpression{ operator, operand: Box::new(operand) }))
    }

    pub fn parenthesised(expression: ASTExpression) -> Self {
        ASTExpression::new(ASTExpressionKind::Parenthesised(ASTParenthesisedExpression{ expression: Box::new(expression) }))
    }

    pub fn identifier(identifier: Token) -> Self {
        ASTExpression::new(ASTExpressionKind::Variable(ASTVariableExpression { identifier }))
    }

    pub fn assignment(identifier: Token, expression: ASTExpression) -> Self {
        ASTExpression::new(ASTExpressionKind::Assignment(ASTAssignmentExpression { identifier, expression: Box::new(expression) }))
    }

    pub fn boolean(token: Token, value: bool) -> Self {
        ASTExpression::new(ASTExpressionKind::Boolean(ASTBooleanExpression { value, token }))
    }

    pub fn error(span: TextSpan) -> Self {
        ASTExpression::new(ASTExpressionKind::Error(span))
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
        LetStatement,
        Assignment,
        Block,
        Variable(String),
        If,
        Else,
    }

    struct ASTVerifier {
        expected: Vec<TestASTNode>,
        actual: Vec<TestASTNode>,
    }

    impl ASTVerifier {
        pub fn new(input: &str, expected: Vec<TestASTNode>) -> Self {
            let compilation_unit = CompilationUnit::compile(input);
            assert_eq!(compilation_unit.diagnostics_report.borrow().diagnostics.len(), 0, "Expected no diagnostics, but got {:?}", compilation_unit.diagnostics_report.borrow().diagnostics);

            let mut verifier = ASTVerifier { expected, actual: Vec::new() };
            verifier.flatten_ast(&compilation_unit.ast);

            verifier
        }

        fn flatten_ast(&mut self, ast: &Ast) {
            self.actual.clear();
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
        fn visit_let_statement(&mut self, let_statement: &ASTLetStatement) {
            self.actual.push(TestASTNode::LetStatement);
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
    }

    fn assert_tree(input: &str, expected: Vec<TestASTNode>) {
        let verifier = ASTVerifier::new(input, expected);
        verifier.verify();
    }

    #[test]
    pub fn test_basic_binary_expression() {
        let input = "let a = 1 + 2";
        let expected = vec![
            TestASTNode::LetStatement,
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
            TestASTNode::LetStatement,
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
            TestASTNode::LetStatement,
            TestASTNode::Number(2),
            TestASTNode::LetStatement,
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
            TestASTNode::LetStatement,
            TestASTNode::Number(1),
            TestASTNode::LetStatement,
            TestASTNode::Number(2),
            TestASTNode::LetStatement,
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
            TestASTNode::LetStatement,
            TestASTNode::Number(1),
            TestASTNode::LetStatement,
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
            TestASTNode::LetStatement,
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
            TestASTNode::LetStatement,
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
            TestASTNode::LetStatement,
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
            TestASTNode::LetStatement,
            TestASTNode::Unary,
            TestASTNode::Number(1),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_negation() {
        let input = "let a = -1";
        let expected = vec![
            TestASTNode::LetStatement,
            TestASTNode::Unary,
            TestASTNode::Number(1),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_power() {
        let input = "let a = 2 ** 3";
        let expected = vec![
            TestASTNode::LetStatement,
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
            TestASTNode::LetStatement,
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
            TestASTNode::LetStatement,
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
            TestASTNode::LetStatement,
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
}