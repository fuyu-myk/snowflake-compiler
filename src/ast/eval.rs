use crate::ast::{ASTBinaryExpression, ASTNumberExpression, ASTVisitor, ASTBinaryOperatorKind, ASTUnaryExpression, TextSpan,
    ASTLetStatement, ASTExpression, ASTVariableExpression, ASTParenthesisedExpression, ASTUnaryOperatorKind, ASTIfStatement, ASTAssignmentExpression};
use std::collections::HashMap;


pub struct ASTEvaluator {
    pub last_value: Option<i64>,
    pub variables: HashMap<String, i64>,
}

impl ASTEvaluator {
    pub fn new() -> Self {
        Self { last_value: None, variables: HashMap::new() }
    }

    fn eval_boolean_instruction<F>(&self, instruction: F) -> i64 where F: FnOnce() -> bool {
        let result = instruction();

        if result {
            1
        } else {
            0
        }
    }
}

impl ASTVisitor for ASTEvaluator {
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
        // self.push_frame();
        self.visit_expression(&if_statement.condition);

        if self.last_value.unwrap() != 0 {
            // self.push_frame();
            self.visit_statement(&if_statement.then_branch);
            // self.pop_frame();
        } else {
            if let Some(else_branch) = &if_statement.else_branch {
                // self.push_frame();
                self.visit_statement(&else_branch.else_statement);
                // self.pop_frame();
            }
        }
        // self.pop_frame();
    }

    fn visit_let_statement(&mut self, let_statement: &ASTLetStatement) {
        self.visit_expression(&let_statement.initialiser);
        self.variables.insert(let_statement.identifier.span.literal.clone(), self.last_value.unwrap());
    }

    fn visit_parenthesised_expression(&mut self, parenthesised_expression: &ASTParenthesisedExpression) {
        self.visit_expression(&parenthesised_expression.expression);
    }

    fn visit_variable_expression(&mut self, variable_expression: &ASTVariableExpression) {
        self.last_value = Some(*self.variables.get(&variable_expression.identifier.span.literal).unwrap());
    }

    fn visit_assignment_expression(&mut self, assignment_expression: &ASTAssignmentExpression) {
        let identifier = &assignment_expression.identifier.span.literal;
        self.visit_expression(&assignment_expression.expression);
        self.variables.insert(identifier.clone(), self.last_value.unwrap());
    }

    fn visit_error(&mut self, span: &TextSpan) {
        todo!()
    }
}