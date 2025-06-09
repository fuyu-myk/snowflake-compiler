/*
 * This program contains the visitor implemntation for traversing the AST.
 */

use termion::color::{Fg, Reset};
use crate::ast::{
    ASTAssignmentExpression, ASTBinaryExpression, ASTBlockStatement, ASTExpression, ASTExpressionKind, ASTIfStatement, ASTLetStatement, ASTNumberExpression, ASTParenthesisedExpression, ASTStatement, ASTStatementKind, ASTUnaryExpression, ASTVariableExpression};
use crate::ast::lexer::TextSpan;


pub trait ASTVisitor {
    fn do_visit_statement(&mut self, statement: &ASTStatement) {
        match &statement.kind {
            ASTStatementKind::Expression(expr) => {
                self.visit_expression(expr);
            }
            ASTStatementKind::Let(expr) => {
                self.visit_let_statement(expr);
            }
            ASTStatementKind::If(statement) => {
                self.visit_if_statement(statement);
            }
            ASTStatementKind::Block(statement) => {
                self.visit_block_statement(statement);
            }
        }
    }

    fn visit_block_statement(&mut self, block_statement: &ASTBlockStatement) {
        for statement in &block_statement.statements {
            self.visit_statement(statement);
        }
    }

    fn visit_if_statement(&mut self, if_statement: &ASTIfStatement) {
        self.visit_expression(&if_statement.condition);
        self.visit_statement(&if_statement.then_branch);

        if let Some(else_branch) = &if_statement.else_branch {
            self.visit_statement(&else_branch.else_statement);
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
            ASTExpressionKind::Unary(expr) => {
                self.visit_unary_expression(expr);
            }
            ASTExpressionKind::Parenthesised(expr) => {
                self.visit_parenthesised_expression(expr);
            }
            ASTExpressionKind::Variable(expr) => {
                self.visit_variable_expression(expr);
            }
            ASTExpressionKind::Assignment(expr) => {
                self.visit_assignment_expression(expr);
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

    fn visit_unary_expression(&mut self, unary_expression: &ASTUnaryExpression);

    fn visit_parenthesised_expression(&mut self, parenthesised_expression: &ASTParenthesisedExpression) {
        self.visit_expression(&parenthesised_expression.expression);
    }

    fn visit_variable_expression(&mut self, variable_expression: &ASTVariableExpression);

    fn visit_assignment_expression(&mut self, assignment_expression: &ASTAssignmentExpression) {
        self.visit_expression(&assignment_expression.expression);
    }

    fn visit_error(&mut self, span: &TextSpan);
}