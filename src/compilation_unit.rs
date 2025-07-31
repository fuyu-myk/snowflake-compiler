use snowflake_compiler::{Idx, idx, IndexVec};

use crate::ast::{AssignExpression, AssignmentOpKind, Ast, BinaryExpression, BinaryOp, BinaryOpKind, BlockExpression, Body, BoolExpression, CallExpression, CompoundBinaryExpression, Expression, ExpressionKind, FxDeclaration, IfExpression, ItemId, LetStatement, NumberExpression, ParenExpression, ReturnStatement, Statement, StatementKind, StringExpression, UnaryExpression, UnaryOpKind, VarExpression, WhileStatement};
use crate::ast::visitor::ASTVisitor;
use crate::ast::eval::ASTEvaluator;
use crate::diagnostics::{DiagnosticsReportCell};
use crate::text;
use crate::ast::lexer::{Lexer, Token, TokenKind};
use crate::ast::parser::Parser;
use crate::text::span::TextSpan;
pub use crate::typings::Type;

use std::rc::Rc;
use std::cell::RefCell;
use crate::diagnostics;
use crate::diagnostics::printer::DiagnosticsPrinter;


idx!(FunctionIndex);
idx!(VariableIndex);

#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub parameters: Vec<VariableIndex>,
    pub body: Body,
    pub return_type: Type,
}

#[derive(Debug, Clone)]
pub struct Variable {
    pub name: String,
    pub ty: Type,
    pub is_shadowing: bool,
}

pub struct GlobalScope {
    pub variables: IndexVec<VariableIndex, Variable>,
    pub functions: IndexVec<FunctionIndex, Function>,
    pub global_variables: Vec<VariableIndex>,
}

impl GlobalScope {
    fn new() -> Self {
        GlobalScope {
            variables: IndexVec::new(),
            functions: IndexVec::new(),
            global_variables: Vec::new(),
        } 
    }

    pub fn declare_variable(&mut self, identifier: &str, ty: Type, is_global: bool, is_shadowing: bool) -> VariableIndex {
        let variable = Variable { name: identifier.to_string(), ty, is_shadowing };
        let variable_index = self.variables.push(variable);

        if is_global {
            self.global_variables.push(variable_index);
        }

        variable_index
    }

    fn lookup_global_variable(&self, identifier: &str) -> Option<VariableIndex> {
        self.global_variables.iter().rev()
            .map(|variable_index| (*variable_index, self.variables.get(*variable_index)))
            .find(|(_, variable)| variable.name == identifier)
            .map(|(variable_index, _) | variable_index)
    }

    pub fn create_function(&mut self, identifier: String, function_body: Body, parameters: Vec<VariableIndex>, return_type: Type) -> Result<FunctionIndex, FunctionIndex> {
        if let Some(existing_fx_idx) = self.lookup_fx(&identifier) {
            return Err(existing_fx_idx);
        }

        let function = Function { name: identifier, parameters: parameters, body: function_body, return_type };
        return Ok(self.functions.push(function));
    }

    fn set_variable_type(&mut self, var_idx: VariableIndex, ty: Type) {
        self.variables[var_idx].ty = ty;
    }

    pub fn lookup_fx(&self, identifier: &str) -> Option<FunctionIndex> {
        self.functions.indexed_iter().find(|(_, function)| function.name == identifier).map(|(idx, _)| idx)
    }
}

struct LocalScope {
    locals: Vec<VariableIndex>,
    function: Option<FunctionIndex>,
}

impl LocalScope {
    fn new(function: Option<FunctionIndex>) -> Self {
        LocalScope { locals: Vec::new(), function }
    }

    fn add_local_var(&mut self, local: VariableIndex) {
        self.locals.push(local);
    }
}

struct ScopeStack {
    local_scopes: Vec<LocalScope>,
    global_scope: GlobalScope,
}

impl ScopeStack {
    fn new() -> Self {
        ScopeStack { local_scopes: Vec::new(), global_scope: GlobalScope::new() }
    }

    fn enter_scope(&mut self) {
        self._enter_scope(None);
    }

    fn _enter_scope(&mut self, fx_idx: Option<FunctionIndex>) {
        self.local_scopes.push(LocalScope::new(fx_idx));
    }

    fn enter_fx_scope(&mut self, fx_idx: FunctionIndex) {
        self._enter_scope(Some(fx_idx));
    }
    
    fn exit_scope(&mut self) {
        self.local_scopes.pop();
    }

    fn exit_fx_scope(&mut self) {
        assert!(self.local_scopes.last().unwrap().function.is_some());
        self.exit_scope();
    }

    fn declare_variable(&mut self, identifier: &str, ty: Type) -> VariableIndex {
        let is_inside_global_scope = self.is_inside_local_scope();
        let index = self._declare_variable(identifier, ty, !is_inside_global_scope);

        if is_inside_global_scope {
            self.current_local_scope_mut().add_local_var(index);
        }

        return index;
    }

    fn _declare_variable(&mut self, identifier: &str, ty: Type, is_global: bool) -> VariableIndex {
        let is_shadowing = match self.current_local_scope() {
            None => false,
            Some(scope) => scope.locals.iter().any(|local| {
                let local = self.global_scope.variables.get(*local);
                local.name == identifier
            }),
        };

        self.global_scope.declare_variable(identifier, ty, is_global, is_shadowing)
    }

    fn lookup_variable(&mut self, identifier: &str) -> Option<VariableIndex> { // top-down lookup
        for scope in self.local_scopes.iter_mut().rev() {
            if let Some((index, _variable)) = scope.locals.iter() // loop local var idxs
                .map(|idx| (*idx, self.global_scope.variables.get(*idx))) // lookup idx in global_scope
                .find(|(_idx, variable)| variable.name == identifier) { // use name to lookup var

                return Some(index)
            }
        }

        self.global_scope.lookup_global_variable(identifier)
    }

    fn is_inside_local_scope(&self) -> bool { // checks if variable is in local scope
        !self.local_scopes.is_empty()
    }

    fn from_global_scope(global_scope: GlobalScope) -> Self {
        ScopeStack {
            local_scopes: Vec::new(),
            global_scope,
        }
    }

    fn surrounding_function(&self) -> Option<&Function> {
        return self.surrounding_function_idx()
        .map(|fx| self.global_scope.functions.get(fx));
    }

    fn surrounding_function_idx(&self) -> Option<FunctionIndex> {
        self.local_scopes.iter().rev()
            .filter_map(|scope| scope.function)
            .next()
    }

    fn current_local_scope(&self) -> Option<&LocalScope> {
        self.local_scopes.last()
    }

    fn current_local_scope_mut(&mut self) -> &mut LocalScope {
        self.local_scopes.last_mut().unwrap()
    }
}

struct Resolver {
    scopes: ScopeStack,
    diagnostics: DiagnosticsReportCell,
}

fn expect_type(diagnostics: &DiagnosticsReportCell, expected: Type, actual: &Type, span: &TextSpan) -> Type {
    if !actual.is_assignable_to(&expected) {
        diagnostics.borrow_mut().report_type_mismatch(&expected, actual, span);
    }

    expected
}

impl Resolver {
    fn new(diagnostics: DiagnosticsReportCell, scopes: ScopeStack) -> Self {
        Resolver {
            scopes,
            diagnostics,
        }
    }

    fn expect_type(&self, expected: Type, actual: &Type, span: &TextSpan) -> Type {
        expect_type(&self.diagnostics, expected, actual, span)
    }

    pub fn resolve(&mut self, ast: &mut Ast) {
        for id in ast.items.cloned_indices() {
            self.visit_item(ast, id);
        }
    }

    pub fn resolve_binary_expression(&self, ast: &Ast, left: &Expression, right: &Expression, operator: &BinaryOpKind) -> Type {
        let type_matrix: (Type, Type, Type) = match operator {
            BinaryOpKind::Equals => (Type::Int, Type::Int, Type::Bool),
            BinaryOpKind::NotEquals => (Type::Int, Type::Int, Type::Bool),
            BinaryOpKind::LessThan => (Type::Int, Type::Int, Type::Bool),
            BinaryOpKind::GreaterThan => (Type::Int, Type::Int, Type::Bool),
            BinaryOpKind::LessThanOrEqual => (Type::Int, Type::Int, Type::Bool),
            BinaryOpKind::GreaterThanOrEqual => (Type::Int, Type::Int, Type::Bool),
            BinaryOpKind::Power => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::Modulo => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::Multiply => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::Divide => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::Plus => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::Minus => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::BitwiseAnd => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::BitwiseXor => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::BitwiseOr => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::ShiftLeft => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::ShiftRight => (Type::Int, Type::Int, Type::Int),
        };

        self.expect_type(type_matrix.0, &left.ty, &left.span(&ast));

        self.expect_type(type_matrix.1, &right.ty, &right.span(&ast));

        type_matrix.2
    }

    pub fn resolve_compound_binary_expression(&self, ast: &Ast, left: &Expression, right: &Expression, operator: &AssignmentOpKind) -> Type {
        // First, validate that the left-hand side is a valid l-value (variable)
        // If it's not, we'll let the type checker catch it when we return void
        // This will generate errors like "binary operation '+=' cannot be applied to type 'int' and 'void'"
        match &left.kind {
            ExpressionKind::Variable(_) => {
                // Valid l-value, proceed with normal type checking
                let type_matrix: (Type, Type) = match operator {
                    AssignmentOpKind::PlusAs => (Type::Int, Type::Int),
                    AssignmentOpKind::MinusAs => (Type::Int, Type::Int),
                    AssignmentOpKind::MultiplyAs => (Type::Int, Type::Int),
                    AssignmentOpKind::DivideAs => (Type::Int, Type::Int),
                    AssignmentOpKind::ModuloAs => (Type::Int, Type::Int),
                    AssignmentOpKind::BitwiseAndAs => (Type::Int, Type::Int),
                    AssignmentOpKind::BitwiseOrAs => (Type::Int, Type::Int),
                    AssignmentOpKind::BitwiseXorAs => (Type::Int, Type::Int),
                    AssignmentOpKind::ShiftLeftAs => (Type::Int, Type::Int),
                    AssignmentOpKind::ShiftRightAs => (Type::Int, Type::Int),
                };

                self.expect_type(type_matrix.0, &left.ty, &left.span(&ast));
                self.expect_type(type_matrix.1, &right.ty, &right.span(&ast));
            }
            _ => {
                // Invalid l-value (like another assignment expression)
                // Still check the right side for completeness, but left side will have void type
                // This will naturally cause the intended error message when this void type
                // is used in subsequent operations
                let expected_right_type = match operator {
                    AssignmentOpKind::PlusAs | AssignmentOpKind::MinusAs | 
                    AssignmentOpKind::MultiplyAs | AssignmentOpKind::DivideAs | 
                    AssignmentOpKind::ModuloAs | AssignmentOpKind::BitwiseAndAs | 
                    AssignmentOpKind::BitwiseOrAs | AssignmentOpKind::BitwiseXorAs | 
                    AssignmentOpKind::ShiftLeftAs | AssignmentOpKind::ShiftRightAs => Type::Int,
                };
                
                self.expect_type(expected_right_type, &right.ty, &right.span(&ast));
            }
        }

        // Compound assignment expressions always return void
        // This is key for generating the intended error messages
        Type::Void
    }

    pub fn resolve_unary_expression(&self, ast: &Ast, operand: &Expression, operator: &UnaryOpKind) -> Type {
        let type_matrix: (Type, Type) = match operator {
            UnaryOpKind::Negation => (Type::Int, Type::Int),
            UnaryOpKind::BitwiseNot => (Type::Int, Type::Int),
        };

        self.expect_type(type_matrix.0, &operand.ty, &operand.span(&ast));

        type_matrix.1
    }
}

pub fn resolve_type_from_string(diagnostics: &DiagnosticsReportCell, type_name: &Token) -> Type {
        let ty = Type::from_str(&type_name.span.literal);
        return match ty {
        None => {
            diagnostics.borrow_mut().report_undeclared_type(&type_name);
            Type::Error
        }
        Some(ty) => ty
    };
}

impl ASTVisitor for Resolver {
    fn visit_let_statement(&mut self, ast: &mut Ast, let_statement: &LetStatement, statement: &Statement) {
        let identifier = let_statement.identifier.span.literal.clone();
        self.visit_expression(ast, let_statement.initialiser);
        let initialiser_expression = &ast.query_expression(let_statement.initialiser);

        let ty = match &let_statement.type_annotation {
            Some(type_annotation) => {
                let ty = resolve_type_from_string(&self.diagnostics, &type_annotation.type_name);
                self.expect_type(ty.clone(), &initialiser_expression.ty, &initialiser_expression.span(&ast));
                ty
            }
            None => initialiser_expression.ty.clone(),
        };

        let variable = self.scopes.declare_variable(&identifier, ty);
        ast.set_variable_for_statement(&statement.id, variable);
    }

    fn visit_variable_expression(&mut self, ast: &mut Ast, variable_expression: &VarExpression, expr: &Expression) {
        let variable_name = &variable_expression.identifier.span.literal;
        match self.scopes.lookup_variable(variable_name) {
            None => {
                let mut diagnostics = self.diagnostics.borrow_mut();
                diagnostics.report_undeclared_variable(&variable_expression.identifier);
            }
            Some(variable_index) => {
                let variable = self.scopes.global_scope.variables.get(variable_index);
                ast.set_type(expr.id, variable.ty.clone());
                ast.set_variable(expr.id, variable_index);
            }
        };
    }

    fn visit_number_expression(&mut self, ast: &mut Ast, _number: &NumberExpression, expr: &Expression) {
        ast.set_type(expr.id, Type::Int);
    }

    fn visit_string_expression(&mut self, ast: &mut Ast, _string: &StringExpression, expr: &Expression) {
        ast.set_type(expr.id, Type::String);
    }

    fn visit_unary_expression(&mut self, ast: &mut Ast, unary_expression: &UnaryExpression, expr: &Expression) {
        self.visit_expression(ast, unary_expression.operand);

        let operand = ast.query_expression(unary_expression.operand);
        let ty = self.resolve_unary_expression(ast, &operand, &unary_expression.operator.kind);

        ast.set_type(expr.id, ty);
    }

    fn visit_binary_expression(&mut self, ast: &mut Ast, binary_expression: &BinaryExpression, expr: &Expression) {
        self.visit_expression(ast, binary_expression.left);
        self.visit_expression(ast, binary_expression.right);
        
        let left = ast.query_expression(binary_expression.left);
        let right = ast.query_expression(binary_expression.right);

        let ty = self.resolve_binary_expression(ast, &left, &right, &binary_expression.operator.kind);
        ast.set_type(expr.id, ty);
    }

    fn visit_compound_binary_expression(&mut self, ast: &mut Ast, compound_expression: &CompoundBinaryExpression, expr: &Expression) {
        self.visit_expression(ast, compound_expression.left);
        self.visit_expression(ast, compound_expression.right);

        let left = ast.query_expression(compound_expression.left);
        let right = ast.query_expression(compound_expression.right);

        match &left.kind {
            ExpressionKind::Variable(var_expr) => {
                // Valid assignment target - perform desugaring
                // Transform `a += b` into `a = (a + b)`
                let ty = self.resolve_compound_binary_expression(ast, &left, &right, &compound_expression.operator);
                
                let var_identifier = var_expr.identifier.clone();
                let var_idx = var_expr.variable_index;
                let left_expr_id = compound_expression.left;
                let right_expr_id = compound_expression.right;
                let operator = compound_expression.operator;
                
                // Desugaring: create the binary operation (a + b)
                let binary_op_kind = self.assignment_to_binary_op(operator);
                let binary_op = BinaryOp::new(binary_op_kind, self.desugared_token(&compound_expression.operator_token));
                let binary_expr_id = ast.binary_expression(binary_op, left_expr_id, right_expr_id).id;
                
                // Visit the newly created binary expression to resolve its type
                self.visit_expression(ast, binary_expr_id);
                
                // Create the assignment expression (a = (a + b))
                let assignment_expr = AssignExpression {
                    identifier: var_identifier.clone(),
                    equals: self.create_synthetic_equals_token(&var_identifier),
                    expression: binary_expr_id,
                    variable_index: var_idx,
                };
                
                // Replace the current expression with the desugared assignment
                let expr_mut = ast.query_expression_mut(expr.id);
                expr_mut.kind = ExpressionKind::Assignment(assignment_expr);
                expr_mut.ty = ty;
            }
            _ => {
                let operator_str = format!("{}=", match compound_expression.operator {
                    AssignmentOpKind::PlusAs => "+",
                    AssignmentOpKind::MinusAs => "-",
                    AssignmentOpKind::MultiplyAs => "*",
                    AssignmentOpKind::DivideAs => "/",
                    AssignmentOpKind::ModuloAs => "%",
                    AssignmentOpKind::BitwiseAndAs => "&",
                    AssignmentOpKind::BitwiseOrAs => "|",
                    AssignmentOpKind::BitwiseXorAs => "^",
                    AssignmentOpKind::ShiftLeftAs => "<<",
                    AssignmentOpKind::ShiftRightAs => ">>",
                });
                
                self.diagnostics.borrow_mut().report_invalid_assignment_target(&operator_str, &expr.span(ast));
                ast.set_type(expr.id, Type::Void);
            }
        }
    }

    fn visit_parenthesised_expression(&mut self, ast: &mut Ast, parenthesised_expression: &ParenExpression, expr: &Expression) {
        self.visit_expression(ast, parenthesised_expression.expression);

        let expression = ast.query_expression(parenthesised_expression.expression);

        ast.set_type(expr.id, expression.ty.clone());
    }

    fn visit_block_expression(&mut self, ast: &mut Ast, block_expression: &BlockExpression, expr: &Expression) {
        self.scopes.enter_scope();

        for statement in &block_expression.statements {
            self.visit_statement(ast, *statement);
        }

        self.scopes.exit_scope();

        let ty = block_expression.statements.last().map(|statement| {
            let statement = ast.query_statement(*statement);
            match statement.kind {
                StatementKind::Expression(expr_id) => {
                    let expr = ast.query_expression(expr_id);
                    expr.ty.clone()
                }
                _ => Type::Void,
            }
        }).unwrap_or(Type::Void);
        ast.set_type(expr.id, ty);
    }

    fn visit_boolean_expression(&mut self, ast: &mut Ast, _boolean: &BoolExpression, expr: &Expression) {
        ast.set_type(expr.id, Type::Bool);
    }

    fn visit_if_expression(&mut self, ast: &mut Ast, if_statement: &IfExpression, expr: &Expression) {
        self.scopes.enter_scope();
        self.visit_expression(ast, if_statement.condition);

        // conditional expression type check
        let conditional_expression = ast.query_expression(if_statement.condition);
        self.expect_type(Type::Bool, &conditional_expression.ty, &conditional_expression.span(&ast));

        self.visit_body(ast, &if_statement.then_branch);
        let mut ty = Type::Void;
        self.scopes.exit_scope();

        if let Some(else_branch) = &if_statement.else_branch {
            self.scopes.enter_scope();

            self.visit_body(ast, &else_branch.body);

            let then_expression_type = if_statement.then_branch.type_or_void(ast);
            let else_expression_type = else_branch.body.type_or_void(ast);
            
            // Only perform type unification if both branches return non-void types
            if !matches!(then_expression_type, Type::Void) && !matches!(else_expression_type, Type::Void) {
                let else_span = else_branch.body.span(ast);
                ty = self.expect_type(then_expression_type, &else_expression_type, &else_span);
            } else {
                ty = Type::Void;
            }

            self.scopes.exit_scope();
        }

        ast.set_type(expr.id, ty);
    }
    
    fn visit_fx_decl(&mut self, ast: &mut Ast, fx_decl: &FxDeclaration, _item_id: ItemId) {
        // fetching fx idx
        let fx_idx = fx_decl.index;

        self.scopes.enter_fx_scope(fx_idx);

        let function = self.scopes.global_scope.functions.get(fx_idx);
        for parameter in function.parameters.clone() {
            self.scopes.current_local_scope_mut().locals.push(parameter); // TODO: parameter types
        }

        let function = self.scopes.global_scope.functions.get(fx_idx);
        for statement in (*function.body).clone() {
            self.visit_statement(ast, statement);
        }
        self.scopes.exit_fx_scope();
    }

    fn visit_return_statement(&mut self, ast: &mut Ast, return_statement: &ReturnStatement) {
        let return_keyword = return_statement.return_keyword.clone();
        // todo: do not clone this
        match self.scopes.surrounding_function().cloned() {
            None => {
                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                diagnostics_binding.report_return_outside_function(&return_statement.return_keyword);
            }
            Some(function) => {
                if let Some(return_expression) = &return_statement.return_value {
                    self.visit_expression(ast, *return_expression);
                    let return_expression = ast.query_expression(*return_expression);
                    self.expect_type(function.return_type.clone(), &return_expression.ty, &return_expression.span(&ast));
                } else {
                    self.expect_type(function.return_type.clone(), &Type::Void, &return_keyword.span);
                }
            }
        }
    }

    fn visit_call_expression(&mut self, ast: &mut Ast, call_expression: &CallExpression, expr: &Expression) {
        let function = self.scopes.global_scope.lookup_fx(&call_expression.callee.span.literal);

        let ty = match function {
            None => {
                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                diagnostics_binding.report_undeclared_function(&call_expression.callee);

                Type::Error
            }
            Some(fx_idx) => {
                let function = self.scopes.global_scope.functions.get(fx_idx);
                ast.set_function(expr.id, fx_idx);
                if function.parameters.len() != call_expression.arguments.len() {
                    let mut diagnostics_binding = self.diagnostics.borrow_mut();
                    diagnostics_binding.report_invalid_arg_count(
                        &call_expression.callee.span,
                        function.parameters.len(),
                        call_expression.arguments.len(),
                    );
                }

                let return_type = function.return_type.clone();
                for (argument, parameter) in call_expression.arguments.iter().zip(function.parameters.clone().iter()) {
                    self.visit_expression(ast, *argument);

                    let argument_expression = ast.query_expression(*argument);
                    let parameter = self.scopes.global_scope.variables.get(*parameter);
                    self.expect_type(parameter.ty.clone(), &argument_expression.ty, &argument_expression.span(&ast));
                }

                return_type
            }
        };

        ast.set_type(expr.id, ty);
    }

    fn visit_assignment_expression(&mut self, ast: &mut Ast, assignment_expression: &AssignExpression, expr: &Expression) {
        self.visit_expression(ast, assignment_expression.expression);
        let identifier = assignment_expression.identifier.span.literal.clone();
        
        let ty = match self.scopes.lookup_variable(&identifier) {
            None => {
                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                diagnostics_binding.report_undeclared_variable(&assignment_expression.identifier);
                Type::Void
            }
            Some(variable) => {
                ast.set_variable(expr.id, variable);
                let value_expression = ast.query_expression(assignment_expression.expression);
                let variable = self.scopes.global_scope.variables.get(variable);
                self.expect_type(variable.ty.clone(), &value_expression.ty, &value_expression.span(&ast));
                variable.ty.clone()
            }
        };

        ast.set_type(expr.id, ty);
    }

    fn visit_while_statement(&mut self, ast: &mut Ast, while_statement: &WhileStatement) {
        self.visit_expression(ast, while_statement.condition);
        let condition = ast.query_expression(while_statement.condition);
        self.expect_type(Type::Bool, &condition.ty, &condition.span(&ast));

        self.visit_body(ast, &while_statement.body);
    }

    fn visit_error(&mut self, _ast: &mut Ast, _span: &TextSpan) {

    }
}

impl Resolver {
    fn assignment_to_binary_op(&self, op_kind: AssignmentOpKind) -> BinaryOpKind {
        match op_kind {
            AssignmentOpKind::PlusAs => BinaryOpKind::Plus,
            AssignmentOpKind::MinusAs => BinaryOpKind::Minus,
            AssignmentOpKind::MultiplyAs => BinaryOpKind::Multiply,
            AssignmentOpKind::DivideAs => BinaryOpKind::Divide,
            AssignmentOpKind::ModuloAs => BinaryOpKind::Modulo,
            AssignmentOpKind::BitwiseAndAs => BinaryOpKind::BitwiseAnd,
            AssignmentOpKind::BitwiseOrAs => BinaryOpKind::BitwiseOr,
            AssignmentOpKind::BitwiseXorAs => BinaryOpKind::BitwiseXor,
            AssignmentOpKind::ShiftLeftAs => BinaryOpKind::ShiftLeft,
            AssignmentOpKind::ShiftRightAs => BinaryOpKind::ShiftRight,
        }
    }

    fn desugared_token(&self, token: &Token) -> Token {
        let desugared_kind = token.kind.to_non_assignment()
            .expect("Token should be an assignment operator");
        
        let literal = format!("{}", desugared_kind);
        
        let start = token.span.start;
        let end = start + literal.len();
        
        Token {
            kind: desugared_kind,
            span: TextSpan {
                start,
                end,
                literal,
            },
        }
    }

    fn create_synthetic_equals_token(&self, identifier_token: &Token) -> Token {
        Token {
            kind: TokenKind::Equals,
            span: identifier_token.span.clone(),
        }
    }
}

pub struct CompilationUnit {
    pub ast: Ast,
    pub diagnostics_report: DiagnosticsReportCell,
    pub global_scope: GlobalScope,
}

impl CompilationUnit {
    pub fn compile(input: &str) -> Result<CompilationUnit, DiagnosticsReportCell> {
        let text = text::SourceText::new(input.to_string());

        // lexer
        let mut lexer = Lexer::new(input);
        let mut tokens = Vec::new();

        while let Some(token) = lexer.next_token() {
            tokens.push(token);
        }

        // parser & ast
        let mut global_scope = GlobalScope::new(); // defining global scope
        let diagnostics_report: DiagnosticsReportCell = Rc::new(RefCell::new(diagnostics::DiagnosticsReport::new()));
        let mut ast = Ast::new();
        let mut parser = Parser::new(
            tokens, 
            Rc::clone(&diagnostics_report),
            &mut ast,
            &mut global_scope,
        );

        parser.parse();

        // error handling (todo: improve)
        Self::check_diagnostics(&text, &diagnostics_report).map_err(|_| Rc::clone(&diagnostics_report))?;

        // symbol check
        let scopes = ScopeStack::from_global_scope(global_scope);
        let mut resolver = Resolver::new(Rc::clone(&diagnostics_report), scopes);
        resolver.resolve(&mut ast);

        ast.visualise();

        Self::check_diagnostics(&text, &diagnostics_report).map_err(|_| Rc::clone(&diagnostics_report))?;
        Ok(CompilationUnit { 
            global_scope: resolver.scopes.global_scope,
            ast, 
            diagnostics_report,
        })
    }

    pub fn maybe_run_compiler(&mut self) {
        if self.diagnostics_report.borrow().diagnostics.len() > 0 {
            return;
        }

        self.run_compiler();
    }

    pub fn run_compiler(&mut self) {
        // evaluator (temp)
        let mut eval = ASTEvaluator::new(&self.global_scope);
        let main_function_ref = self.global_scope.lookup_fx("main");

        if let Some(function) = main_function_ref {
            let function = self.global_scope.functions.get(function);
            for statement in &*function.body {
                eval.visit_statement(&mut self.ast, *statement);
            }
        } else {
            self.ast.visit(&mut eval);
        }

        println!("Result: {:?}", eval.last_value);
    }

    fn check_diagnostics(text: &text::SourceText, diagnostics_report: &DiagnosticsReportCell) -> Result<(), ()> {
    let diagnostics_binding = diagnostics_report.borrow();
    if diagnostics_binding.diagnostics.len() > 0 {
        let diagnostics_printer = DiagnosticsPrinter::new(
            &text,
            &diagnostics_binding.diagnostics
        );

        diagnostics_printer.print();

        if diagnostics_binding.diagnostics.len() == 1 {
                println!("\nCompilation failed due to {} previous error.", diagnostics_binding.diagnostics.len());
            } else {
                println!("\nCompilation failed due to {} previous errors.", diagnostics_binding.diagnostics.len());
            }
        
        return Err(());
        }
    Ok(())
    }
}