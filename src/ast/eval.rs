use crate::{ast::{ASTAssignmentExpression, ASTBinaryExpression, ASTBinaryOperatorKind, ASTBooleanExpression, ASTIfStatement, ASTLetStatement, ASTNumberExpression, ASTParenthesisedExpression, ASTUnaryExpression, ASTUnaryOperatorKind, ASTVariableExpression, ASTVisitor, ASTWhileStatement, Ast, TextSpan}, compilation_unit::GlobalScope};
use std::collections::HashMap;


// Frame type here used for scoping
pub struct Frame {
    variables: HashMap<String, i64>
}

impl Frame {
    fn new() -> Self {
        Self { variables: HashMap::new() }
    }

    fn insert(&mut self, identifier: String, value: i64) {
        self.variables.insert(identifier, value);
    }

    fn get(&self, identifier: &String) -> Option<&i64> {
        self.variables.get(identifier)
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
    
fn update(&mut self, identifier: String, value: i64) {
        for frame in self.frames.iter_mut().rev() {
            if frame.get(&identifier).is_some() {
                frame.insert(identifier, value);
                return;
            }
        }
        panic!("Variable {} not found", identifier)
    }

    fn insert(&mut self, identifier: String, value: i64) {
        self.frames.last_mut().unwrap().insert(identifier, value);
    }

    fn get(&self, identifier: &String) -> Option<&i64> {
        for frame in self.frames.iter().rev() {
            if let Some(value) = frame.get(identifier) {
                return Some(value);
            }
        }

        None
    }
}

pub struct ASTEvaluator<'a> {
    pub last_value: Option<i64>,
    pub frames: FrameStack,
    pub global_scope: &'a GlobalScope,pub ast: &'a Ast,
}

impl <'a> ASTEvaluator<'a> {
    pub fn new(global_scope: &'a GlobalScope, ast: &'a Ast) -> Self {
        Self { last_value: None, frames: FrameStack::new(), global_scope, ast }
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
    fn get_ast(&self) -> &Ast {
        self.ast
    }

    fn visit_number_expression(&mut self, number: &ASTNumberExpression) {
        self.last_value = Some(number.number);
    }

    fn visit_binary_expression(&mut self, expr: &ASTBinaryExpression) {
        self.visit_expression(&expr.left);
        let left = self.last_value.unwrap();

        self.visit_expression(&expr.right);
        let right = self.last_value.unwrap();

        self.last_value = Some(match expr.operator.kind {
            // classic arithmetic operators
            ASTBinaryOperatorKind::Plus => left + right,
            ASTBinaryOperatorKind::Minus => left - right,
            ASTBinaryOperatorKind::Multiply => left * right,
            ASTBinaryOperatorKind::Divide => left / right,
            ASTBinaryOperatorKind::Power => left.pow(right as u32),

            // bitwise operators
            ASTBinaryOperatorKind::BitwiseAnd => left & right,
            ASTBinaryOperatorKind::BitwiseOr => left | right,
            ASTBinaryOperatorKind::BitwiseXor => left ^ right,

            // relation operators
            ASTBinaryOperatorKind::Equals => if left == right { 1 } else { 0 },
            ASTBinaryOperatorKind::NotEquals => self.eval_boolean_instruction(|| left != right),
            ASTBinaryOperatorKind::LessThan => self.eval_boolean_instruction(|| left < right),
            ASTBinaryOperatorKind::GreaterThan => self.eval_boolean_instruction(|| left > right),
            ASTBinaryOperatorKind::LessThanOrEqual => self.eval_boolean_instruction(|| left <= right),
            ASTBinaryOperatorKind::GreaterThanOrEqual => self.eval_boolean_instruction(|| left >= right),
        });
    }

    fn visit_unary_expression(&mut self, unary_expression: &ASTUnaryExpression) {
        self.visit_expression(&unary_expression.operand);
        let operand = self.last_value.unwrap();

        self.last_value = Some(match unary_expression.operator.kind {
            ASTUnaryOperatorKind::Negation => -operand,
            ASTUnaryOperatorKind::BitwiseNot => !operand,
        });
    }

    fn visit_if_statement(&mut self, if_statement: &ASTIfStatement) {
        self.push_frame();
        self.visit_expression(&if_statement.condition);

        if self.last_value.unwrap() != 0 {
            self.push_frame();
            self.visit_statement(&if_statement.then_branch);
            self.pop_frame();
        } else {
            if let Some(else_branch) = &if_statement.else_branch {
                self.push_frame();
                self.visit_statement(&else_branch.else_statement);
                self.pop_frame();
            }
        }
        self.pop_frame();
    }

    fn visit_let_statement(&mut self, let_statement: &ASTLetStatement) {
        self.visit_expression(&let_statement.initialiser);
        self.frames.insert(let_statement.identifier.span.literal.clone(), self.last_value.unwrap());
    }

    fn visit_parenthesised_expression(&mut self, parenthesised_expression: &ASTParenthesisedExpression) {
        self.visit_expression(&parenthesised_expression.expression);
    }

    fn visit_variable_expression(&mut self, variable_expression: &ASTVariableExpression) {
        let identifier = &variable_expression.identifier.span.literal;
        self.last_value = Some(*self.frames.get(identifier).expect(format!("Variable {} not found", identifier).as_str()));
    }

    fn visit_assignment_expression(&mut self, assignment_expression: &ASTAssignmentExpression) {
        let identifier = &assignment_expression.identifier.span.literal;
        self.visit_expression(&assignment_expression.expression);
        self.frames.update(identifier.clone(), self.last_value.unwrap());
    }

    fn visit_boolean_expression(&mut self, boolean: &ASTBooleanExpression) {
        self.last_value = Some(boolean.value as i64);
    }

    fn visit_while_statement(&mut self, while_statement: &ASTWhileStatement) {
        self.push_frame();
        self.visit_expression(&while_statement.condition);

        while self.last_value.unwrap() != 0 {
            self.visit_statement(&while_statement.body);
            self.visit_expression(&while_statement.condition);
        }
        self.pop_frame();
    }

    fn visit_call_expression(&mut self, call_expression: &super::ASTCallExpression) {
        let function = self.global_scope.lookup_function(&call_expression.identifier.span.literal).unwrap();
        let mut arguments = Vec::new();

        for argument in &call_expression.arguments {
            self.visit_expression(argument);
            arguments.push(self.last_value.unwrap());
        }

        self.push_frame();
        for (i, argument) in arguments.iter().enumerate() {
            let parameter_name = function.parameters[i].clone();
            self.frames.insert(parameter_name, *argument);
        }

        self.visit_statement(&function.body);
        self.pop_frame();
    }

    fn visit_block_statement(&mut self, block_statement: &super::ASTBlockStatement) {
        self.push_frame();

        for statement in &block_statement.statements {
            self.visit_statement(statement);
        }

        self.pop_frame();
    }

    fn visit_function_declaration_statement(&mut self, fx_decl_statement: &super::ASTFxDeclarationStatement) {
        
    }

    fn visit_error(&mut self, span: &TextSpan) {
        todo!()
    }
}