use snowflake_common::Idx;

use crate::{ast::{ASTVisitor, AssignExpression, Ast, BinaryExpression, BinaryOpKind, Body, BoolExpression, BreakExpression, CallExpression, ContinueExpression, Expression, FxDeclaration, IfExpression, IndexExpression, ItemId, LetStatement, NumberExpression, ParenExpression, ReturnStatement, Statement, TupleExpression, TupleIndexExpression, UnaryExpression, UnaryOpKind, VarExpression, WhileStatement}, compilation_unit::{FunctionIndex, GlobalScope, VariableIndex}};
use snowflake_common::text::span::TextSpan;
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
    Float(f64),
    Usize(usize),
    Boolean(bool),
    String(String),
    Void,
    Function(FunctionIndex),
    Array(Vec<Value>),
    Tuple(Vec<Value>),
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
            Value::Usize(value) => *value as i64,
            _ => panic!("Expected number value"),
        }
    }

    pub fn expect_float(&self) -> f64 {
        match self {
            Value::Float(value) => *value,
            Value::Number(value) => *value as f64,
            Value::Usize(value) => *value as f64,
            _ => panic!("Expected float value"),
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
    pub returned: bool,
    pub loop_break: bool,
    pub loop_continue: bool,
}

impl <'a> ASTEvaluator<'a> {
    pub fn new(global_scope: &'a GlobalScope) -> Self {
        Self { last_value: None, frames: FrameStack::new(), global_scope, returned: false, loop_break: false, loop_continue: false }
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

    fn visit_float_expression(&mut self, _ast: &mut Ast, float: &super::FloatExpression, _expr: &Expression) {
        self.last_value = Some(Value::Float(float.number));
    }

    fn visit_usize_expression(&mut self, _ast: &mut Ast, number: &super::UsizeExpression, _expr: &Expression) {
        self.last_value = Some(Value::Usize(number.number));
    }

    fn visit_string_expression(&mut self, _ast: &mut Ast, string: &super::StringExpression, _expr: &Expression) {
        self.last_value = Some(Value::String(string.string.clone()));
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
            if self.returned || self.loop_break || self.loop_continue {
                break;
            }
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
                if self.returned {
                    break;
                }
                self.visit_statement(ast, *statement);
            }
            self.pop_frame();
        } else if let Some(else_branch) = &if_statement.else_branch {
            self.push_frame();
            for statement in else_branch.body.iter() {
                if self.returned {
                    break;
                }
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

        while self.expect_last_value().expect_boolean() && !self.returned && !self.loop_break {
            self.visit_body(ast, &while_statement.body);
            if self.returned || self.loop_break {
                break;
            }
            if self.loop_continue {
                self.loop_continue = false;
                self.visit_expression(ast, while_statement.condition);
                continue;
            }
            self.visit_expression(ast, while_statement.condition);
        }
        
        self.loop_break = false;
        self.loop_continue = false;
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
            if self.returned {
                break;
            }
            self.visit_statement(ast, *statement);
        }

        self.pop_frame();
        self.returned = false;
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

    fn visit_return_statement(&mut self, ast: &mut Ast, return_statement: &ReturnStatement) {
        if let Some(expr) = &return_statement.return_value {
            self.visit_expression(ast, *expr);
            self.last_value = Some(self.expect_last_value().clone());
        } else {
            self.last_value = Some(Value::Void); // Default return value if none is provided
        }
        self.returned = true;
    }

    fn visit_break_expression(&mut self, _ast: &mut Ast, _break_expression: &BreakExpression, _expr: &Expression) {
        self.loop_break = true;
    }

    fn visit_continue_expression(&mut self, _ast: &mut Ast, _continue_expression: &ContinueExpression, _expr: &Expression) {
        self.loop_continue = true;
    }

    fn visit_array_expression(&mut self, ast: &mut Ast, array_expression: &super::ArrayExpression, _expr: &Expression) {
        let elements = array_expression.elements.iter().map(|element| {
            self.visit_expression(ast, *element);
            self.expect_last_value().clone()
        }).collect();

        self.last_value = Some(Value::Array(elements));
    }

    fn visit_index_expression(&mut self, ast: &mut Ast, index_expression: &IndexExpression, _expr: &Expression) {
        self.visit_expression(ast, index_expression.object);
        let mut current_value = self.expect_last_value().clone();

        self.visit_expression(ast, index_expression.index.idx_no);
        let index_value = self.expect_last_value();
        
        // Handle both usize and converted numbers as array indices
        let index = match index_value {
            Value::Usize(val) => *val,
            Value::Number(val) => {
                if *val < 0 {
                    panic!("Array index cannot be negative: {}", val);
                }
                *val as usize
            }
            _ => panic!("Invalid array index type: {:?}", index_value),
        };

        // Apply the index to the current value
        current_value = match &current_value {
            Value::Array(arr) => {
                if index >= arr.len() {
                    panic!("Array index out of bounds: index {} >= length {}", index, arr.len());
                }
                arr[index].clone()
            }
            _ => panic!("Cannot index into non-array value: {:?}", current_value),
        };

        self.last_value = Some(current_value);
    }

    fn visit_tuple_expression(&mut self, ast: &mut Ast, tuple_expression: &TupleExpression, _expr: &Expression) {
        let elements = tuple_expression.elements.iter().map(|element| {
            self.visit_expression(ast, *element);
            self.expect_last_value().clone()
        }).collect();

        self.last_value = Some(Value::Tuple(elements)); 
    }

    fn visit_tuple_index_expression(&mut self, ast: &mut Ast, tuple_index_expression: &TupleIndexExpression, _expr: &Expression) {
        self.visit_expression(ast, tuple_index_expression.tuple);
        let mut current_value = self.expect_last_value().clone();

        self.visit_expression(ast, tuple_index_expression.index.idx_no);
        let index_value = self.expect_last_value();
        
        // Handle both usize and converted numbers as tuple indices
        let index = match index_value {
            Value::Usize(val) => *val,
            Value::Number(val) => {
                if *val < 0 {
                    panic!("Tuple index cannot be negative: {}", val);
                }
                *val as usize
            }
            _ => panic!("Invalid tuple index type: {:?}", index_value),
        };

        // Apply the index to the current value
        current_value = match &current_value {
            Value::Tuple(tup) => {
                if index >= tup.len() {
                    panic!("Tuple index out of bounds: index {} >= length {}", index, tup.len());
                }
                tup[index].clone()
            }
            _ => panic!("Cannot index into non-tuple value: {:?}", current_value),
        };

        self.last_value = Some(current_value);
    }

    fn visit_error(&mut self, _ast: &mut Ast, _span: &TextSpan) {
        panic!("Unable to evaluate error expression")
    }
}