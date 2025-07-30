use snowflake_compiler::Idx;

use crate::{ast::{ASTVisitor, AssignExpression, Ast, BinaryExpression, BinaryOpKind, Body, BoolExpression, CallExpression, Expression, FxDeclaration, IfExpression, ItemId, LetStatement, NumberExpression, ParenExpression, Statement, TextSpan, UnaryExpression, UnaryOpKind, VarExpression, WhileStatement}, compilation_unit::{FunctionIndex, GlobalScope, VariableIndex}};
use std::{collections::HashMap};


// Frame type here used for scoping
#[derive(Debug)]
pub struct Frame {
    variables: HashMap<VariableIndex, Value>
}

impl Frame {
    fn new() -> Self {
        Self { variables: HashMap::new() }
    }

    fn insert(&mut self, index: VariableIndex, value: Value) {
        self.variables.insert(index, value);
    }

    fn get(&self, index: &VariableIndex) -> Option<&Value> {
        self.variables.get(index)
    }
}

#[derive(Debug)]
pub struct FrameStack {
    frames: Vec<Frame>
}

impl FrameStack {
    fn new() -> Self {
        Self { frames: vec![Frame::new()] }
    }

    fn push(&mut self) {
        self.frames.push(Frame::new());
    }

    fn pop(&mut self) {
        self.frames.pop();
    }
    
fn update(&mut self, index: VariableIndex, value: Value) {
        for frame in self.frames.iter_mut().rev() {
            if frame.get(&index).is_some() {
                frame.insert(index, value);
                return;
            }
        }
    }

    fn insert(&mut self, index: VariableIndex, value: Value) {
        self.frames.last_mut().unwrap().insert(index, value);
    }

    fn get(&self, index: &VariableIndex) -> Option<&Value> {
        for frame in self.frames.iter().rev() {
            if let Some(value) = frame.get(index) {
                return Some(value);
            }
        }

        None
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Number(i64),
    Boolean(bool),
    String(String),
    Function(FunctionIndex),
}

impl Value {
    pub fn expect_boolean(&self) -> bool {
        match self {
            Value::Boolean(value) => *value,
            _ => panic!("Expected boolean value"),
        }
    }

    pub fn expect_number(&self) -> i64 {
        match self {
            Value::Number(value) => *value,
            _ => panic!("Expected number value"),
        }
    }

    pub fn expect_function(&self) -> FunctionIndex {
        match self {
            Value::Function(value) => *value,
            _ => panic!("Expected function value"),
        }
    }
}

pub struct ASTEvaluator<'a> {
    pub last_value: Option<Value>,
    pub frames: FrameStack,
    pub global_scope: &'a GlobalScope,
}

impl <'a> ASTEvaluator<'a> {
    pub fn new(global_scope: &'a GlobalScope) -> Self {
        Self { last_value: None, frames: FrameStack::new(), global_scope }
    }

    fn push_frame(&mut self) {
        self.frames.push();
    }

    fn pop_frame(&mut self) {
        self.frames.pop();
    }

    fn expect_last_value(&self) -> &Value {
        self.last_value.as_ref().expect("Expected last value to be set")
    }
}

impl <'a> ASTVisitor for ASTEvaluator<'a> {
    fn visit_number_expression(&mut self, _ast: &mut Ast, number: &NumberExpression, _expr: &Expression) {
        self.last_value = Some(Value::Number(number.number));
    }

    fn visit_string_expression(&mut self, _ast: &mut Ast, string: &super::StringExpression, _expr: &Expression) {
        self.last_value = Some(Value::String(string.value.clone()));
    }

    fn visit_binary_expression(&mut self, ast: &mut Ast, binary_expr: &BinaryExpression, _expr: &Expression) {
        self.visit_expression(ast, binary_expr.left);
        let left = self.expect_last_value().clone();

        self.visit_expression(ast, binary_expr.right);
        let right = self.expect_last_value().clone();

        self.last_value = Some(match binary_expr.operator.kind {
            // classic arithmetic operators
            BinaryOpKind::Plus => Value::Number(left.expect_number() + right.expect_number()),
            BinaryOpKind::Minus => Value::Number(left.expect_number() - right.expect_number()),
            BinaryOpKind::Multiply => Value::Number(left.expect_number() * right.expect_number()),
            BinaryOpKind::Divide => Value::Number(left.expect_number() / right.expect_number()),
            BinaryOpKind::Modulo => Value::Number(left.expect_number() % right.expect_number()),
            BinaryOpKind::Power => Value::Number(left.expect_number().pow(right.expect_number() as u32)),

            // bitwise operators
            BinaryOpKind::BitwiseAnd => Value::Number(left.expect_number() & right.expect_number()),
            BinaryOpKind::BitwiseOr => Value::Number(left.expect_number() | right.expect_number()),
            BinaryOpKind::BitwiseXor => Value::Number(left.expect_number() ^ right.expect_number()),
            BinaryOpKind::ShiftLeft => Value::Number(left.expect_number() << right.expect_number()),
            BinaryOpKind::ShiftRight => Value::Number(left.expect_number() >> right.expect_number()),

            // relation operators
            BinaryOpKind::Equals => Value::Boolean(left == right),
            BinaryOpKind::NotEquals => Value::Boolean(left != right),
            BinaryOpKind::LessThan => Value::Boolean(left.expect_number() < right.expect_number()),
            BinaryOpKind::GreaterThan => Value::Boolean(left.expect_number() > right.expect_number()),
            BinaryOpKind::LessThanOrEqual => Value::Boolean(left.expect_number() <= right.expect_number()),
            BinaryOpKind::GreaterThanOrEqual => Value::Boolean(left.expect_number() >= right.expect_number()),
        });
    }

    fn visit_unary_expression(&mut self, ast: &mut Ast, unary_expression: &UnaryExpression, _expr: &Expression) {
        self.visit_expression(ast, unary_expression.operand);
        let operand = self.expect_last_value().expect_number();

        self.last_value = Some(Value::Number(match unary_expression.operator.kind {
            UnaryOpKind::Negation => -operand,
            UnaryOpKind::BitwiseNot => !operand,
        }));
    }

    fn visit_body(&mut self, ast: &mut Ast, body: &Body) {
        self.push_frame();

        for statement in body.iter() {
            self.visit_statement(ast, *statement);
        }

        self.pop_frame();
    }

    fn visit_if_expression(&mut self, ast: &mut Ast, if_statement: &IfExpression, _expr: &Expression) {
        self.push_frame();
        self.visit_expression(ast, if_statement.condition);

        if self.expect_last_value().expect_boolean() {
            self.push_frame();
            for statement in if_statement.then_branch.iter() {
                self.visit_statement(ast, *statement);
            }
            self.pop_frame();
        } else if let Some(else_branch) = &if_statement.else_branch {
            self.push_frame();
            for statement in else_branch.body.iter() {
                self.visit_statement(ast, *statement);
            }
            self.pop_frame();
        }
        self.pop_frame();
    }

    fn visit_let_statement(&mut self, ast: &mut Ast, let_statement: &LetStatement, _statement: &Statement) {
        self.visit_expression(ast, let_statement.initialiser);
        self.frames.insert(let_statement.variable_index, self.expect_last_value().clone());
    }

    fn visit_parenthesised_expression(&mut self, ast: &mut Ast, parenthesised_expression: &ParenExpression, _expr: &Expression) {
        self.visit_expression(ast, parenthesised_expression.expression);
    }

    fn visit_variable_expression(&mut self, _ast: &mut Ast, variable_expression: &VarExpression, _expr: &Expression) {
        let identifier = &variable_expression.identifier.span.literal;
        self.last_value = Some(
            self.frames.get(&variable_expression.variable_index)
            .expect(format!("Variable {} '{}' not found", variable_expression.variable_index.as_index(), identifier)
            .as_str())
            .clone());
    }

    fn visit_assignment_expression(&mut self, ast: &mut Ast, assignment_expression: &AssignExpression, _expr: &Expression) {
        self.visit_expression(ast, assignment_expression.expression);
        self.frames.update(assignment_expression.variable_index, self.last_value.clone().unwrap());
    }

    fn visit_boolean_expression(&mut self, _ast: &mut Ast, boolean: &BoolExpression, _expr: &Expression) {
        self.last_value = Some(Value::Boolean(boolean.value));
    }

    fn visit_while_statement(&mut self, ast: &mut Ast, while_statement: &WhileStatement) {
        self.push_frame();
        self.visit_expression(ast, while_statement.condition);

        while self.expect_last_value().expect_boolean() {
            self.visit_body(ast, &while_statement.body);
            self.visit_expression(ast, while_statement.condition);
        }
        self.pop_frame();
    }

    fn visit_call_expression(&mut self, ast: &mut Ast, call_expression: &CallExpression, _expr: &Expression) {
        let fx_name = &call_expression.fx_name();
        let function = self.global_scope.lookup_fx(fx_name)
            .map(|f| self.global_scope.functions.get(f))
            .expect(format!("Function '{}' not found", fx_name).as_str());
        let mut arguments = Vec::new();

        for argument in &call_expression.arguments {
            self.visit_expression(ast, *argument);
            arguments.push(self.last_value.clone().unwrap());
        }

        self.push_frame();
        for (argument, parameter) in arguments.iter().zip(function.parameters.iter()) {
            self.frames.insert(*parameter, argument.clone());
        }

        for statement in &*function.body {
            self.visit_statement(ast, *statement);
        }
        self.pop_frame();
    }

    fn visit_block_expression(&mut self, ast: &mut Ast, block_statement: &super::BlockExpression, _expr: &Expression) {
        self.push_frame();

        for statement in &block_statement.statements {
            self.visit_statement(ast, *statement);
        }

        self.pop_frame();
    }

    fn visit_fx_decl(&mut self, _ast: &mut Ast, _fx_expr: &FxDeclaration, _item_id: ItemId) {
    }

    fn visit_error(&mut self, _ast: &mut Ast, _span: &TextSpan) {
        panic!("Unable to evaluate error expression")
    }
}