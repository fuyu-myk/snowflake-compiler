/*
 * This program contains the visitor implemntation for traversing the AST.
 */

use crate::{ast::{
    AssignExpression, BinaryExpression, BlockStatement, BoolExpression, CallExpression, 
    Expression, ExpressionId, ExpressionKind, FxDeclarationStatement, IfStatement, LetStatement, 
    NumberExpression, ParenExpression, ReturnStatement, StatementId, StatementKind, UnaryExpression, 
    VarExpression, WhileStatement, Ast}, text::span::TextSpan};


pub trait ASTVisitor {
    fn get_ast(&self) -> &Ast;

    fn do_visit_statement(&mut self, statement: &StatementId) {
        let statement = self.get_ast().query_statement(statement).clone();

        match &statement.kind {
            StatementKind::Expression(expr) => {
                self.visit_expression(expr);
            }
            StatementKind::Let(expr) => {
                self.visit_let_statement(expr);
            }
            StatementKind::If(statement) => {
                self.visit_if_statement(statement);
            }
            StatementKind::Block(statement) => {
                self.visit_block_statement(statement);
            }
            StatementKind::While(statement) => {
                self.visit_while_statement(statement);
            }
            StatementKind::FxDeclaration(statement) => {
                self.visit_function_declaration_statement(statement);
            }
            StatementKind::Return(statement) => {
                self.visit_return_statement(statement);
            }
        }
    }

    fn visit_function_declaration_statement(&mut self, fx_decl_statement: &FxDeclarationStatement);

    fn visit_return_statement(&mut self, return_statement: &ReturnStatement) {
        if let Some(expr) = &return_statement.return_value {
            self.visit_expression(expr);
        }
    }

    fn visit_while_statement(&mut self, while_statement: &WhileStatement) {
        self.visit_expression(&while_statement.condition);
        self.visit_statement(&while_statement.body);
    }

    fn visit_block_statement(&mut self, block_statement: &BlockStatement) {
        for statement in &block_statement.statements {
            self.visit_statement(statement);
        }
    }

    fn visit_if_statement(&mut self, if_statement: &IfStatement) {
        self.visit_expression(&if_statement.condition);
        self.visit_statement(&if_statement.then_branch);

        if let Some(else_branch) = &if_statement.else_branch {
            self.visit_statement(&else_branch.else_statement);
        }
    }

    fn visit_let_statement(&mut self, let_statement: &LetStatement);

    fn visit_statement(&mut self, statement: &StatementId) {
        self.do_visit_statement(statement);
    }

    fn do_visit_expression(&mut self, expression: &ExpressionId) {
        let expression = self.get_ast().query_expression(expression).clone();

        match &expression.kind {
            ExpressionKind::Number(number) => {
                self.visit_number_expression(number, &expression);
            }
            ExpressionKind::Binary(expr) => {
                self.visit_binary_expression(expr, &expression);
            }
            ExpressionKind::Unary(expr) => {
                self.visit_unary_expression(expr, &expression);
            }
            ExpressionKind::Parenthesised(expr) => {
                self.visit_parenthesised_expression(expr, &expression);
            }
            ExpressionKind::Variable(expr) => {
                self.visit_variable_expression(expr, &expression);
            }
            ExpressionKind::Assignment(expr) => {
                self.visit_assignment_expression(expr, &expression);
            }
            ExpressionKind::Boolean(expr) => {
                self.visit_boolean_expression(expr, &expression);
            }
            ExpressionKind::Call(expr) => {
                self.visit_call_expression(expr, &expression);
            }
            ExpressionKind::Error(span) => {
                self.visit_error(span);
            }
        }
    }

    fn visit_call_expression(&mut self, call_expression: &CallExpression, expr: &Expression) {
        for argument in &call_expression.arguments {
            self.visit_expression(argument);
        }
    }

    fn visit_expression(&mut self, expression: &ExpressionId) {
        self.do_visit_expression(expression);
    }

    fn visit_number_expression(&mut self, number: &NumberExpression, expr: &Expression);

    fn visit_binary_expression(&mut self, binary_expression: &BinaryExpression, expr: &Expression) {
        self.visit_expression(&binary_expression.left);
        self.visit_expression(&binary_expression.right);
    }

    fn visit_unary_expression(&mut self, unary_expression: &UnaryExpression, expr: &Expression);

    fn visit_parenthesised_expression(&mut self, parenthesised_expression: &ParenExpression, expr: &Expression) {
        self.visit_expression(&parenthesised_expression.expression);
    }

    fn visit_variable_expression(&mut self, variable_expression: &VarExpression, expr: &Expression);

    fn visit_assignment_expression(&mut self, assignment_expression: &AssignExpression, expr: &Expression) {
        self.visit_expression(&assignment_expression.expression);
    }

    fn visit_boolean_expression(&mut self, boolean: &BoolExpression, expr: &Expression);

    fn visit_error(&mut self, span: &TextSpan);
}