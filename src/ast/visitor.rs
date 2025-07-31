/*
 * This program contains the visitor implemntation for traversing the AST.
 */

use crate::ast::{
    AssignExpression, Ast, BinaryExpression, BlockExpression, Body, BoolExpression, CallExpression, CompoundBinaryExpression, Expression, ExpressionId, ExpressionKind, FxDeclaration, IfExpression, ItemId, ItemKind, LetStatement, NumberExpression, ParenExpression, ReturnStatement, Statement, StatementId, StatementKind, StringExpression, UnaryExpression, VarExpression, WhileStatement};
use crate::text::span::TextSpan;


pub trait ASTVisitor {
    fn do_visit_statement(&mut self, ast: &mut Ast, statement: StatementId) {
        let statement = ast.query_statement(statement).clone();

        match &statement.kind {
            StatementKind::Expression(expr) => {
                self.visit_expression(ast, *expr);
            }
            StatementKind::Let(expr) => {
                self.visit_let_statement(ast, expr, &statement);
            }
            StatementKind::While(statement) => {
                self.visit_while_statement(ast, statement);
            }
            StatementKind::Return(statement) => {
                self.visit_return_statement(ast, statement);
            }
        }
    }

    fn visit_item(&mut self, ast: &mut Ast, item: ItemId) {
        self.visit_item_default(ast, item);
    }

    fn visit_item_default(&mut self, ast: &mut Ast, item: ItemId) {
        let item = ast.query_item(item).clone();

        match &item.kind {
            ItemKind::Statement(statement) => {
                self.visit_statement(ast, *statement);
            }
            ItemKind::Function(fx_decl) => {
                self.visit_fx_decl(ast, fx_decl, item.id);
            }
        }
    }

    fn visit_body(&mut self, ast: &mut Ast, body: &Body) {
        self.visit_body_default(ast, body);
    }

    fn visit_body_default(&mut self, ast: &mut Ast, body: &Body) {
        for statement in body.iter() {
            self.visit_statement(ast, *statement);
        }
    }

    fn visit_fx_decl(&mut self, ast: &mut Ast, fx_decl: &FxDeclaration, item_id: ItemId);

    fn visit_return_statement(&mut self, ast: &mut Ast, return_statement: &ReturnStatement) {
        if let Some(expr) = &return_statement.return_value {
            self.visit_expression(ast, *expr);
        }
    }

    fn visit_while_statement(&mut self, ast: &mut Ast, while_statement: &WhileStatement) {
        self.visit_expression(ast, while_statement.condition);
        self.visit_body(ast, &while_statement.body);
    }

    fn visit_block_expression(&mut self, ast: &mut Ast, block_expression: &BlockExpression, _expr: &Expression) {
        for statement in &block_expression.statements {
            self.visit_statement(ast, *statement);
        }
    }

    fn visit_if_expression(&mut self, ast: &mut Ast, if_expression: &IfExpression, _expr: &Expression) {
        self.visit_expression(ast, if_expression.condition);
        for statement in if_expression.then_branch.iter() {
            self.visit_statement(ast, *statement);
        }

        if let Some(else_branch) = &if_expression.else_branch {
            for statement in else_branch.body.iter() {
                self.visit_statement(ast, *statement);
            }
        }
    }

    fn visit_let_statement(&mut self, ast: &mut Ast, let_statement: &LetStatement, statement: &Statement);

    fn visit_statement(&mut self, ast: &mut Ast, statement: StatementId) {
        self.do_visit_statement(ast, statement);
    }

    fn do_visit_expression(&mut self, ast: &mut Ast, expression: ExpressionId) {
        let expression = ast.query_expression(expression).clone();

        match &expression.kind {
            ExpressionKind::Number(number) => {
                self.visit_number_expression(ast, number, &expression);
            }
            ExpressionKind::String(string) => {
                self.visit_string_expression(ast, string, &expression);
            }
            ExpressionKind::Binary(expr) => {
                self.visit_binary_expression(ast, expr, &expression);
            }
            ExpressionKind::CompoundBinary(expr) => {
                self.visit_compound_binary_expression(ast, expr, &expression);
            }
            ExpressionKind::Unary(expr) => {
                self.visit_unary_expression(ast, expr, &expression);
            }
            ExpressionKind::Parenthesised(expr) => {
                self.visit_parenthesised_expression(ast, expr, &expression);
            }
            ExpressionKind::Variable(expr) => {
                self.visit_variable_expression(ast, expr, &expression);
            }
            ExpressionKind::Assignment(expr) => {
                self.visit_assignment_expression(ast, expr, &expression);
            }
            ExpressionKind::Boolean(expr) => {
                self.visit_boolean_expression(ast, expr, &expression);
            }
            ExpressionKind::Call(expr) => {
                self.visit_call_expression(ast, expr, &expression);
            }
            ExpressionKind::If(expr) => {
                self.visit_if_expression(ast, expr, &expression);
            }
            ExpressionKind::Block(expr) => {
                self.visit_block_expression(ast, expr, &expression);
            }
            ExpressionKind::Error(span) => {
                self.visit_error(ast, span);
            }
        }
    }

    fn visit_call_expression(&mut self, ast: &mut Ast, call_expression: &CallExpression, _expr: &Expression) {
        for argument in &call_expression.arguments {
            self.visit_expression(ast, *argument);
        }
    }

    fn visit_expression(&mut self, ast: &mut Ast, expression: ExpressionId) {
        self.do_visit_expression(ast, expression);
    }

    fn visit_number_expression(&mut self, ast: &mut Ast, number: &NumberExpression, expr: &Expression);

    fn visit_string_expression(&mut self, ast: &mut Ast, string: &StringExpression, expr: &Expression);

    fn visit_binary_expression(&mut self, ast: &mut Ast, binary_expression: &BinaryExpression, _expr: &Expression) {
        self.visit_expression(ast, binary_expression.left);
        self.visit_expression(ast, binary_expression.right);
    }

    fn visit_compound_binary_expression(&mut self, ast: &mut Ast, compound_expression: &CompoundBinaryExpression, _expr: &Expression) {
        self.visit_expression(ast, compound_expression.left);
        self.visit_expression(ast, compound_expression.right);
    }

    fn visit_unary_expression(&mut self, ast: &mut Ast, unary_expression: &UnaryExpression, expr: &Expression);

    fn visit_parenthesised_expression(&mut self, ast: &mut Ast, parenthesised_expression: &ParenExpression, _expr: &Expression) {
        self.visit_expression(ast, parenthesised_expression.expression);
    }

    fn visit_variable_expression(&mut self, ast: &mut Ast, variable_expression: &VarExpression, expr: &Expression);

    fn visit_assignment_expression(&mut self, ast: &mut Ast, assignment_expression: &AssignExpression, _expr: &Expression) {
        self.visit_expression(ast, assignment_expression.expression);
    }

    fn visit_boolean_expression(&mut self, ast: &mut Ast, boolean: &BoolExpression, expr: &Expression);

    fn visit_error(&mut self, ast: &mut Ast, span: &TextSpan);
}