/*
 * This program contains the visitor implemntation for traversing the AST.
 */

use crate::ast::{
    ASTAssignmentExpression, ASTBinaryExpression, ASTBlockStatement, ASTBooleanExpression, ASTCallExpression, ASTExpressionId, ASTExpressionKind, ASTFxDeclarationStatement, ASTIfStatement, ASTLetStatement, ASTNumberExpression, ASTParenthesisedExpression, ASTReturnStatement, ASTStatementId, ASTStatementKind, ASTUnaryExpression, ASTVariableExpression, ASTWhileStatement, Ast};
use crate::ast::lexer::TextSpan;


pub trait ASTVisitor {
    fn get_ast(&self) -> &Ast;

    fn do_visit_statement(&mut self, statement: &ASTStatementId) {
        let statement = self.get_ast().query_statement(statement).clone();

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
            ASTStatementKind::While(statement) => {
                self.visit_while_statement(statement);
            }
            ASTStatementKind::FxDeclaration(statement) => {
                self.visit_function_declaration_statement(statement);
            }
            ASTStatementKind::Return(statement) => {
                self.visit_return_statement(statement);
            }
        }
    }

    fn visit_function_declaration_statement(&mut self, fx_decl_statement: &ASTFxDeclarationStatement);

    fn visit_return_statement(&mut self, return_statement: &ASTReturnStatement) {
        if let Some(expr) = &return_statement.return_value {
            self.visit_expression(expr);
        }
    }

    fn visit_while_statement(&mut self, while_statement: &ASTWhileStatement) {
        self.visit_expression(&while_statement.condition);
        self.visit_statement(&while_statement.body);
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

    fn visit_statement(&mut self, statement: &ASTStatementId) {
        self.do_visit_statement(statement);
    }

    fn do_visit_expression(&mut self, expression: &ASTExpressionId) {
        let expression = self.get_ast().query_expression(expression).clone();

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
            ASTExpressionKind::Boolean(expr) => {
                self.visit_boolean_expression(expr);
            }
            ASTExpressionKind::Call(expr) => {
                self.visit_call_expression(expr);
            }
            ASTExpressionKind::Error(span) => {
                self.visit_error(span);
            }
        }
    }

    fn visit_call_expression(&mut self, call_expression: &ASTCallExpression) {
        for argument in &call_expression.arguments {
            self.visit_expression(argument);
        }
    }

    fn visit_expression(&mut self, expression: &ASTExpressionId) {
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

    fn visit_boolean_expression(&mut self, boolean: &ASTBooleanExpression);

    fn visit_error(&mut self, span: &TextSpan);
}