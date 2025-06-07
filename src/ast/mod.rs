use crate::ast::lexer::{Token, TextSpan};
use crate::compilation_unit::CompilationUnit;
use termion::color;
use termion::color::Reset;
use termion::color::Fg;

pub mod lexer;
pub mod parser;
pub mod eval;


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

pub trait ASTVisitor {
    fn do_visit_statement(&mut self, statement: &ASTStatement) {
        match &statement.kind {
            ASTStatementKind::Expression(expr) => {
                self.visit_expression(expr);
            }
            ASTStatementKind::LetStatement(expr) => {
                self.visit_let_statement(expr);
            }
        }
    }

    fn visit_let_statement(&mut self, let_statement: &ASTLetStatement);

    fn visit_statement(&mut self, statement: &ASTStatement) {
        self.do_visit_statement(statement);
    }

    fn do_visit_expression(&mut self, expression: &ASTExpression) {
        match &expression.kind {
            ASTExpressionKind::Number(number) => {
                self.visit_number_expression(number);
            }
            ASTExpressionKind::Binary(expr) => {
                self.visit_binary_expression(expr);
            }
            ASTExpressionKind::Parenthesised(expr) => {
                self.visit_parenthesised_expression(expr);
            }
            ASTExpressionKind::Variable(expr) => {
                self.visit_variable_expression(expr);
            }
            ASTExpressionKind::Error(span) => {
                self.visit_error(span);
            }
        }
    }

    fn visit_expression(&mut self, expression: &ASTExpression) {
        self.do_visit_expression(expression);
    }

    fn visit_number_expression(&mut self, number: &ASTNumberExpression);

    fn visit_binary_expression(&mut self, binary_expression: &ASTBinaryExpression) {
        self.visit_expression(&binary_expression.left);
        self.visit_expression(&binary_expression.right);
    }

    fn visit_parenthesised_expression(&mut self, parenthesised_expression: &ASTParenthesisedExpression) {
        self.visit_expression(&parenthesised_expression.expression);
    }

    fn visit_variable_expression(&mut self, variable_expression: &ASTVariableExpression);

    fn visit_error(&mut self, span: &TextSpan);
}

pub struct ASTPrinter {
    indent: usize,
    result: String,
}

impl ASTPrinter {
    const NUMBER_COLOUR: color::Cyan = color::Cyan;
    const TEXT_COLOUR: color::LightWhite = color::LightWhite;
    const KEYWORD_COLOUR: color::Magenta = color::Magenta;
    const VARIABLE_COLOUR: color::Green = color::Green;

    pub fn new() -> Self {
        Self { indent: 0, result: String::new() }
    }

    fn add_whitespace(&mut self) {
        self.result.push_str(" ");
    }

    fn add_newline(&mut self) {
        self.result.push_str("
        ");
    }
}

impl ASTVisitor for ASTPrinter {
    fn visit_statement(&mut self, statement: &ASTStatement) {
        Self::do_visit_statement(self, statement);

        self.result.push_str(&format!("{}\n", Fg(Reset)));
    }

    fn visit_number_expression(&mut self, number: &ASTNumberExpression) {
        self.result.push_str(&format!("{}{}", Self::NUMBER_COLOUR.fg_str(), number.number));
    }

    fn visit_binary_expression(&mut self, binary_expression: &ASTBinaryExpression) {
        self.visit_expression(&binary_expression.left);
        self.add_whitespace();

        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), 
                             binary_expression.operator.token.span.literal));
        self.add_whitespace();

        self.visit_expression(&binary_expression.right);
    }

    fn visit_parenthesised_expression(&mut self, parenthesised_expression: &ASTParenthesisedExpression) {
        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), "("));

        self.visit_expression(&parenthesised_expression.expression);

        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), ")"));
    }

    fn visit_let_statement(&mut self, let_statement: &ASTLetStatement) {
        self.result.push_str(&format!("{}let", Self::KEYWORD_COLOUR.fg_str())); // let keyword in magenta
        self.add_whitespace();

        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), let_statement.identifier.span.literal)); // variable name in white
        self.add_whitespace();

        self.result.push_str(&format!("{}=", Self::TEXT_COLOUR.fg_str())); // '=' in white
        self.add_whitespace();

        self.visit_expression(&let_statement.initialiser);
    }

    fn visit_variable_expression(&mut self, variable_expression: &ASTVariableExpression) {
        self.result.push_str(&format!("{}{}", Self::VARIABLE_COLOUR.fg_str(), variable_expression.identifier.span.literal));
    }

    fn visit_error(&mut self, span: &TextSpan) {
        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), span.literal));
    }
}

pub enum ASTStatementKind {
    Expression(ASTExpression),
    LetStatement(ASTLetStatement),
}

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
        ASTStatement::new(ASTStatementKind::LetStatement(ASTLetStatement { identifier, initialiser }))
    }
}

pub enum ASTExpressionKind {
    Number(
        ASTNumberExpression
    ),
    Binary(
        ASTBinaryExpression
    ),
    Parenthesised(
        ASTParenthesisedExpression
    ),
    Variable(
        ASTVariableExpression
    ),
    Error(
        TextSpan
    )
}

pub struct ASTVariableExpression {
    pub identifier: Token,
}

impl ASTVariableExpression {
    pub fn identifier(&self) -> &str {
        &self.identifier.span.literal
    }
}

#[derive(Debug)]
pub enum ASTBinaryOperatorKind {
    Plus,
    Minus,
    Multiply,
    Divide,
    Power,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ASTBinaryOperatorAssociativity {
    Left,
    Right,
}

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
            ASTBinaryOperatorKind::Plus => 1,
            ASTBinaryOperatorKind::Minus => 1,
            ASTBinaryOperatorKind::Multiply => 2,
            ASTBinaryOperatorKind::Divide => 2,
            ASTBinaryOperatorKind::Power => todo!(),
        }
    }

    pub fn associativity(&self) -> ASTBinaryOperatorAssociativity {
        match self.kind {
            ASTBinaryOperatorKind::Power => ASTBinaryOperatorAssociativity::Right,
            _ => ASTBinaryOperatorAssociativity::Left,
        }
    }
}

pub struct ASTBinaryExpression {
    left: Box<ASTExpression>, // stored in heap instead of stack
    operator: ASTBinaryOperator,
    right: Box<ASTExpression>,
}

pub struct ASTNumberExpression {
    number: i64,
}

pub struct ASTParenthesisedExpression {
    expression: Box<ASTExpression>,
}

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

    pub fn parenthesised(expression: ASTExpression) -> Self {
        ASTExpression::new(ASTExpressionKind::Parenthesised(ASTParenthesisedExpression{ expression: Box::new(expression) }))
    }

    pub fn identifier(identifier: Token) -> Self {
        ASTExpression::new(ASTExpressionKind::Variable(ASTVariableExpression { identifier }))
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


    #[derive(Debug, PartialEq, Eq)]
    enum TestASTNode {
        Number(i64),
        Binary,
        Parenthesised,
        LetStatement,
        Variable(String),
    }

    struct ASTVerifier {
        expected: Vec<TestASTNode>,
        actual: Vec<TestASTNode>,
    }

    impl ASTVerifier {
        pub fn new(input: &str, expected: Vec<TestASTNode>) -> Self {
            let compilation_unit = CompilationUnit::compile(input);
            let mut verifier = ASTVerifier { expected, actual: Vec::new() };
            let flattened_ast = verifier.flatten_ast(&compilation_unit.ast);

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
        let input = "let a = (6 + 9) * b";
        let expected = vec![
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
        let input = "let a = (b + (c * 2)) / 3";
        let expected = vec![
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
        let input = "let a = (6 + 9) * b + 42";
        let expected = vec![
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
}