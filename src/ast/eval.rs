use crate::{ast::{ASTVisitor, AssignExpression, Ast, BinaryExpression, BinaryOpKind, BoolExpression, CallExpression, Expression, IfExpression, LetStatement, NumberExpression, ParenExpression, Statement, TextSpan, UnaryExpression, UnaryOpKind, VarExpression, WhileStatement}, compilation_unit::{GlobalScope, VariableIndex}};
use std::collections::HashMap;


// Frame type here used for scoping
pub struct Frame {
    variables: HashMap<VariableIndex, i64>
}

impl Frame {
    fn new() -> Self {
        Self { variables: HashMap::new() }
    }

    fn insert(&mut self, index: VariableIndex, value: i64) {
        self.variables.insert(index, value);
    }

    fn get(&self, index: &VariableIndex) -> Option<&i64> {
        self.variables.get(index)
    }
}

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
    
fn update(&mut self, index: VariableIndex, value: i64) {
        for frame in self.frames.iter_mut().rev() {
            if frame.variables.contains_key(&index) {
                frame.insert(index, value);
                return;
            }
        }
    }

    fn insert(&mut self, index: VariableIndex, value: i64) {
        self.frames.last_mut().unwrap().insert(index, value);
    }

    fn get(&self, index: &VariableIndex) -> Option<&i64> {
        for frame in self.frames.iter().rev() {
            if let Some(value) = frame.get(index) {
                return Some(value);
            }
        }

        None
    }
}

pub struct ASTEvaluator<'a> {
    pub last_value: Option<i64>,
    pub frames: FrameStack,
    pub global_scope: &'a GlobalScope,
}

impl <'a> ASTEvaluator<'a> {
    pub fn new(global_scope: &'a GlobalScope) -> Self {
        Self { last_value: None, frames: FrameStack::new(), global_scope }
    }

    fn eval_boolean_instruction<F>(&self, instruction: F) -> i64 where F: FnOnce() -> bool {
        let result = instruction();

        if result {
            1
        } else {
            0
        }
    }

    fn push_frame(&mut self) {
        self.frames.push();
    }

    fn pop_frame(&mut self) {
        self.frames.pop();
    }
}

impl <'a> ASTVisitor for ASTEvaluator<'a> {
    fn visit_number_expression(&mut self, ast: &mut Ast, number: &NumberExpression, expr: &Expression) {
        self.last_value = Some(number.number);
    }

    fn visit_binary_expression(&mut self, ast: &mut Ast, binary_expr: &BinaryExpression, expr: &Expression) {
        self.visit_expression(ast, binary_expr.left);
        let left = self.last_value.unwrap();

        self.visit_expression(ast, binary_expr.right);
        let right = self.last_value.unwrap();

        self.last_value = Some(match binary_expr.operator.kind {
            // classic arithmetic operators
            BinaryOpKind::Plus => left + right,
            BinaryOpKind::Minus => left - right,
            BinaryOpKind::Multiply => left * right,
            BinaryOpKind::Divide => left / right,
            BinaryOpKind::Power => left.pow(right as u32),

            // bitwise operators
            BinaryOpKind::BitwiseAnd => left & right,
            BinaryOpKind::BitwiseOr => left | right,
            BinaryOpKind::BitwiseXor => left ^ right,

            // relation operators
            BinaryOpKind::Equals => if left == right { 1 } else { 0 },
            BinaryOpKind::NotEquals => self.eval_boolean_instruction(|| left != right),
            BinaryOpKind::LessThan => self.eval_boolean_instruction(|| left < right),
            BinaryOpKind::GreaterThan => self.eval_boolean_instruction(|| left > right),
            BinaryOpKind::LessThanOrEqual => self.eval_boolean_instruction(|| left <= right),
            BinaryOpKind::GreaterThanOrEqual => self.eval_boolean_instruction(|| left >= right),
        });
    }

    fn visit_unary_expression(&mut self, ast: &mut Ast, unary_expression: &UnaryExpression, expr: &Expression) {
        self.visit_expression(ast, unary_expression.operand);
        let operand = self.last_value.unwrap();

        self.last_value = Some(match unary_expression.operator.kind {
            UnaryOpKind::Negation => -operand,
            UnaryOpKind::BitwiseNot => !operand,
        });
    }

    fn visit_if_expression(&mut self, ast: &mut Ast, if_statement: &IfExpression, expr: &Expression) {
        self.push_frame();
        self.visit_expression(ast, if_statement.condition);

        if self.last_value.unwrap() != 0 {
            self.push_frame();
            self.visit_expression(ast, if_statement.then_branch);
            self.pop_frame();
        } else {
            if let Some(else_branch) = &if_statement.else_branch {
                self.push_frame();
                self.visit_expression(ast, else_branch.else_expression);
                self.pop_frame();
            }
        }
        self.pop_frame();
    }

    fn visit_let_statement(&mut self, ast: &mut Ast, let_statement: &LetStatement, statement: &Statement) {
        self.visit_expression(ast, let_statement.initialiser);
        self.frames.insert(let_statement.variable_index, self.last_value.unwrap());
    }

    fn visit_parenthesised_expression(&mut self, ast: &mut Ast, parenthesised_expression: &ParenExpression, expr: &Expression) {
        self.visit_expression(ast, parenthesised_expression.expression);
    }

    fn visit_variable_expression(&mut self, ast: &mut Ast, variable_expression: &VarExpression, expr: &Expression) {
        let identifier = &variable_expression.identifier.span.literal;
        self.last_value = Some(*self.frames.get(&variable_expression.variable_index).expect(format!("Variable {} not found", identifier).as_str()));
    }

    fn visit_assignment_expression(&mut self, ast: &mut Ast, assignment_expression: &AssignExpression, expr: &Expression) {
        self.visit_expression(ast, assignment_expression.expression);
        self.frames.update(assignment_expression.variable_index, self.last_value.unwrap());
    }

    fn visit_boolean_expression(&mut self, ast: &mut Ast, boolean: &BoolExpression, expr: &Expression) {
        self.last_value = Some(boolean.value as i64);
    }

    fn visit_while_statement(&mut self, ast: &mut Ast, while_statement: &WhileStatement) {
        self.push_frame();
        self.visit_expression(ast, while_statement.condition);

        while self.last_value.unwrap() != 0 {
            self.visit_expression(ast, while_statement.body);
            self.visit_expression(ast, while_statement.condition);
        }
        self.pop_frame();
    }

    fn visit_call_expression(&mut self, ast: &mut Ast, call_expression: &CallExpression, expr: &Expression) {
        let fx_idx = self.global_scope.lookup_function(&call_expression.identifier.span.literal).unwrap();
        let function = self.global_scope.functions.get(fx_idx);
        let mut arguments = Vec::new();

        for argument in &call_expression.arguments {
            self.visit_expression(ast, *argument);
            arguments.push(self.last_value.unwrap());
        }

        self.push_frame();
        for (argument, parameter) in arguments.iter().zip(function.parameters.iter()) {
            self.frames.insert(*parameter, *argument);
        }

        self.visit_statement(ast, function.body);
        self.pop_frame();
    }

    fn visit_block_expression(&mut self, ast: &mut Ast, block_statement: &super::BlockExpression, expr: &Expression) {
        self.push_frame();

        for statement in &block_statement.statements {
            self.visit_statement(ast, *statement);
        }

        self.pop_frame();
    }

    fn visit_function_declaration(&mut self, ast: &mut Ast, fx_decl_statement: &super::FxDeclaration) {
        
    }

    fn visit_error(&mut self, ast: &mut Ast, span: &TextSpan) {
        todo!()
    }
}