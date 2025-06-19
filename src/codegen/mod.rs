use crate::{ast::{visitor::ASTVisitor, AssignExpression, Ast, BinaryOp, BinaryOpKind, BlockExpression, BoolExpression, CallExpression, Expression, ExpressionId, ExpressionKind, FxDeclaration, IfExpression, ItemId, ItemKind, LetStatement, NumberExpression, ParenExpression, ReturnStatement, Statement, StatementId, UnaryExpression, UnaryOp, UnaryOpKind, VarExpression, WhileStatement}, compilation_unit::{GlobalScope, VariableIndex}, text::span::TextSpan, typings::Type};


pub struct CTranspiler<'a> {
    pub result: String,
    pub indent: usize,
    pub global_scope: &'a GlobalScope,
    pub l_value_stack: Vec<(VariableIndex, ExpressionId)>,
}

impl <'a> CTranspiler<'a> {
    pub fn new(global_scope: &'a GlobalScope) -> Self {
        Self { result: String::new(), indent: 0, global_scope: global_scope, l_value_stack: Vec::new() }
    }

    pub fn transpile(mut self, ast: &mut Ast) -> String {
        let items = ast.items.clone();
        for item in items.iter() {
            match &item.kind {
                ItemKind::Statement(_) => {}
                ItemKind::Function(fx_decl) => {
                    self.visit_fx_decl(ast, fx_decl, item.id);
                }
            }
        }

        // writing main fx
        self.result.push_str("int main() {\n");
        self.indent += 1;
        for item in items.iter() {
            match &item.kind {
                ItemKind::Statement(statement) => {
                    self.visit_statement(ast, *statement);
                }
                ItemKind::Function(_) => {}
            }
        }
        self.write_indent();

        self.result.push_str("return 0;\n");

        self.indent -=1;
        self.result.push_str("}\n");

        return self.result;
    }

    fn transpile_type(ty: &Type) -> String {
        return match ty {
            Type::Int => "int".to_string(),
            Type::Bool => "int".to_string(),
            Type::Void => "void".to_string(),
            Type::Unresolved => panic!("Unresolved type"),
            Type::Error => panic!("Error type"),
        }
    }

    fn transpile_binary_operator(&self, operator: &BinaryOp) -> &'static str {
        return match &operator.kind {
            BinaryOpKind::Plus => "+",
            BinaryOpKind::Minus => "-",
            BinaryOpKind::Multiply => "*",
            BinaryOpKind::Divide => "/",
            BinaryOpKind::Power => panic!("Power operator unsupported"),
            BinaryOpKind::Equals => "==",
            BinaryOpKind::NotEquals => "!=",
            BinaryOpKind::LessThan => "<",
            BinaryOpKind::LessThanOrEqual => "<=",
            BinaryOpKind::GreaterThan => ">",
            BinaryOpKind::GreaterThanOrEqual => ">=",
            BinaryOpKind::BitwiseAnd => "&",
            BinaryOpKind::BitwiseOr => "|",
            BinaryOpKind::BitwiseXor => "^",
        }
    }

    fn transpile_unary_operator(&self, operator: &UnaryOp) -> &'static str {
        return match &operator.kind {
            UnaryOpKind::Negation => "-",
            UnaryOpKind::BitwiseNot => "~",
        };
    }

    fn is_valid_r_value(&mut self, ast: &Ast, expr_id: ExpressionId) -> bool {
        let expr = ast.query_expression(expr_id);

        return match &expr.kind {
            ExpressionKind::Number(_) => true,
            ExpressionKind::Boolean(_) => true,
            ExpressionKind::Unary(_) => self.is_valid_r_value(ast, expr.id),
            ExpressionKind::Variable(_) => true,
            ExpressionKind::Binary(bin_expr) => {
                let left = self.is_valid_r_value(ast, bin_expr.left);
                let right = self.is_valid_r_value(ast, bin_expr.right);
                left && right
            }
            ExpressionKind::Parenthesised(paren_expr) => self.is_valid_r_value(ast, paren_expr.expression),
            ExpressionKind::Assignment(assign_expr) => self.is_valid_r_value(ast, assign_expr.expression),
            ExpressionKind::Call(call_expr) => {
                for argument in call_expr.arguments.iter() {
                    if !self.is_valid_r_value(ast, *argument) {
                        return false;
                    }
                }
                true
            },
            ExpressionKind::If(_) => false,
            ExpressionKind::Block(_) => false,
            ExpressionKind::Error(_) => panic!("Error expression"),
        };
    }

    fn write_type(&mut self, ty: &Type) {
        self.result.push_str(&CTranspiler::transpile_type(ty));
    }

    fn write_whitespace(&mut self) {
        self.result.push_str(" ");
    }

    fn write_indent(&mut self) {
        for _ in 0..self.indent {
            self.result.push_str("    ");
        }
    }

    fn write_newline(&mut self) {
        self.result.push('\n');
    }
}

impl ASTVisitor for CTranspiler<'_> {
    fn visit_statement(&mut self, ast: &mut Ast, statement: StatementId) {
        self.write_indent();
        self.do_visit_statement(ast, statement);
        self.result.push(';');
        self.write_newline();
    }

    fn visit_number_expression(&mut self, ast: &mut Ast, number: &NumberExpression, expr: &Expression) {
        self.result.push_str(&number.number.to_string());
    }

    fn visit_unary_expression(&mut self, ast: &mut Ast, unary_expression: &UnaryExpression, expr: &Expression) {
        self.result.push_str(self.transpile_unary_operator(&unary_expression.operator));
        self.visit_expression(ast, unary_expression.operand);
    }

    fn visit_boolean_expression(&mut self, ast: &mut Ast, boolean: &BoolExpression, expr: &Expression) {
        self.result.push_str(if boolean.value { "1" } else { "0" });
    }

    fn visit_binary_expression(&mut self, ast: &mut Ast, binary_expression: &crate::ast::BinaryExpression, expr: &Expression) {
        self.visit_expression(ast, binary_expression.left);
        self.write_whitespace();

        self.result.push_str(self.transpile_binary_operator(&binary_expression.operator));
        self.write_whitespace();

        self.visit_expression(ast, binary_expression.right);
    }

    fn visit_let_statement(&mut self, ast: &mut Ast, let_statement: &LetStatement, statement: &Statement) {
        let expr = ast.query_expression(let_statement.initialiser).clone();

        match &expr.kind {
            ExpressionKind::If(expr) => {
                let var = self.global_scope.variables.get(let_statement.variable_index);
                let indent_temp = self.indent;

                // Var declaration
                self.write_type(&var.ty);
                self.write_whitespace();
                self.result.push_str(&var.name);
                self.result.push_str(";\n");

                // If statement
                self.write_indent();
                self.result.push_str(&expr.if_keyword.span.literal);
                self.write_whitespace();

                self.result.push('(');
                self.visit_expression(ast, expr.condition);
                self.result.push_str(") {\n");

                self.indent += 1;
                self.write_indent();
                self.indent = 0;
                self.result.push_str(&var.name);
                self.result.push_str(" = ");
                self.visit_expression(ast, expr.then_branch);
                self.indent = indent_temp;

                self.write_indent();
                self.result.push('}');

                if let Some(else_branch) = &expr.else_branch {
                    self.result.push_str(" else {\n");

                    self.indent += 1;
                    self.write_indent();
                    self.indent = 0;
                    self.result.push_str(&var.name);
                    self.result.push_str(" = ");
                    self.visit_expression(ast, else_branch.else_expression);
                    self.indent = indent_temp;

                    self.write_indent();
                    self.result.push('}');
                }
            }
            _ => {
                let var = self.global_scope.variables.get(let_statement.variable_index);
                self.write_type(&var.ty);
                self.write_whitespace();

                self.result.push_str(&var.name);
                self.result.push_str(" = ");
                self.visit_expression(ast, let_statement.initialiser);
            }
        }
    }

    fn visit_variable_expression(&mut self, ast: &mut Ast, variable_expression: &VarExpression, expr: &Expression) {
        let variable = self.global_scope.variables.get(variable_expression.variable_index);
        self.result.push_str(&variable.name);
    }

    fn visit_parenthesised_expression(&mut self, ast: &mut Ast, parenthesised_expression: &ParenExpression, expr: &Expression) {
        self.result.push('(');
        self.visit_expression(ast, parenthesised_expression.expression);
        self.result.push(')');
    }

    fn visit_if_expression(&mut self, ast: &mut Ast, if_expression: &IfExpression, expr: &Expression) {
        self.result.push_str(&if_expression.if_keyword.span.literal);
        self.write_whitespace();

        self.result.push('(');
        self.visit_expression(ast, if_expression.condition);
        self.result.push_str(") {\n");

        self.indent += 1;
        self.visit_expression(ast, if_expression.then_branch);
        self.indent -= 1;

        self.write_indent();
        self.result.push('}');

        if let Some(else_branch) = &if_expression.else_branch {
            self.result.push_str(" else {\n");

            self.indent += 1;
            self.visit_expression(ast, else_branch.else_expression);
            self.indent -= 1;

            self.write_indent();
            self.result.push('}');
        }
    }

    fn visit_block_expression(&mut self, ast: &mut Ast, block_expression: &BlockExpression, expr: &Expression) {
        for statement in block_expression.statements.iter().take(block_expression.statements.len() - 1) { // all statements besides last
            self.visit_statement(ast, *statement);
        }

        if let Some((assigned, r_value_id)) = self.l_value_stack.last() {
            if *r_value_id == expr.id {
                self.result.push_str(&self.global_scope.variables.get(*assigned).name);
                self.result.push_str(" = ");
            }
        }

        if let Some(last_statement) = block_expression.statements.last() {
            self.visit_statement(ast, *last_statement);
        }
    }

    fn visit_assignment_expression(&mut self, ast: &mut Ast, assignment_expression: &AssignExpression, expr: &Expression) {
        self.result.push_str(&self.global_scope.variables.get(assignment_expression.variable_index).name);
        self.result.push_str(" = ");
        self.visit_expression(ast, assignment_expression.expression);
    }

    fn visit_while_statement(&mut self, ast: &mut Ast, while_statement: &WhileStatement) {
        self.result.push_str(&while_statement.while_keyword.span.literal);
        self.write_whitespace();

        self.result.push('(');
        self.visit_expression(ast, while_statement.condition);
        self.result.push_str(") {");
        self.write_newline();

        self.indent += 1;
        self.visit_expression(ast, while_statement.body);
        self.write_newline();
        self.indent -= 1;
        self.write_indent();
        self.result.push('}');
    }

    fn visit_fx_decl(&mut self, ast: &mut Ast, fx_decl: &FxDeclaration, item_id: ItemId) {
        let function = self.global_scope.functions.get(fx_decl.index);
        self.write_type(&function.return_type);
        self.write_whitespace();

        self.result.push_str(&function.name);

        self.result.push_str("(");
        for (i, param) in function.parameters.iter().enumerate() {
            let parameter = self.global_scope.variables.get(*param);
            self.write_type(&parameter.ty);
            self.write_whitespace();

            self.result.push_str(&parameter.name);
            if i != function.parameters.len() - 1 {
                self.result.push_str(", ");
            }
        }

        self.result.push_str(") {\n");
        self.indent += 1;

        self.visit_expression(ast, fx_decl.body);
        self.result.push_str("}\n");
        self.indent -= 1;
    }

    fn visit_return_statement(&mut self, ast: &mut Ast, return_statement: &ReturnStatement) {
        self.result.push_str(&return_statement.return_keyword.span.literal);
        self.write_whitespace();

        if let Some(return_statement) = return_statement.return_value {
            self.visit_expression(ast, return_statement);
        }
    }

    fn visit_call_expression(&mut self, ast: &mut Ast, call_expression: &CallExpression, expr: &Expression) {
        self.result.push_str(&call_expression.callee.span.literal);
        self.result.push_str(&call_expression.left_paren.span.literal);

        for (i, argument) in call_expression.arguments.iter().enumerate() {
            if i != 0 {
                self.result.push(',');
                self.write_whitespace();
            }

            self.visit_expression(ast, *argument);
        }

        self.result.push_str(&call_expression.right_paren.span.literal);
    }

    fn visit_error(&mut self, ast: &mut Ast, span: &TextSpan) {
        self.result.push_str("/* error */");
    }
}