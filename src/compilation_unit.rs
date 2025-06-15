use snowflake_compiler::{Idx, idx, IndexVec};

use crate::ast::{AssignExpression, Ast, BinaryExpression, BinaryOpKind, BlockExpression, BoolExpression, CallExpression, Expression, FxDeclarationParams, FxDeclaration, IfExpression, LetStatement, NumberExpression, ParenExpression, ReturnStatement, Statement, StatementId, StatementKind, UnaryExpression, UnaryOpKind, VarExpression, WhileStatement};
use crate::ast::visitor::ASTVisitor;
use crate::ast::eval::ASTEvaluator;
use crate::diagnostics::{DiagnosticsReportCell};
use crate::text;
use crate::ast::lexer::{Lexer, Token};
use crate::ast::parser::Parser;
use crate::text::span::TextSpan;
use crate::typings::Type;
use std::any::Any;
use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use crate::diagnostics;
use crate::diagnostics::printer::DiagnosticsPrinter;


idx!(FunctionIndex);
idx!(VariableIndex);

#[derive(Debug, Clone)]
pub struct FunctionSymbol {
    pub parameters: Vec<VariableIndex>,
    pub body: StatementId,
    pub return_type: Type,
    pub name: String,
}

#[derive(Debug, Clone)]
pub struct VariableSymbol {
    pub name: String,
    pub ty: Type,
}

pub struct GlobalScope {
    pub variables: IndexVec<VariableIndex, VariableSymbol>,
    pub functions: IndexVec<FunctionIndex, FunctionSymbol>,
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

    fn declare_variable(&mut self, identifier: &str, ty: Type, is_global: bool) -> VariableIndex {
        let variable = VariableSymbol { name: identifier.to_string(), ty };
        let variable_index = self.variables.push(variable);

        if is_global {
            self.global_variables.push(variable_index);
        }

        variable_index
    }

    fn lookup_global_variable(&self, identifier: &str) -> Option<VariableIndex> {
        self.global_variables.iter().map(
            |variable_index| (*variable_index, self.variables.get(*variable_index))
        ).find(|(_, variable)| variable.name == identifier).map(
            |(variable_index, _) | variable_index)
    }

    fn declare_function(&mut self, identifier: &str, function_body_id: &StatementId, parameters: Vec<VariableIndex>, return_type: Type) -> Result<(), ()> {
        if self.lookup_function(identifier).is_some() { // handling similarly named functions
            return Err(())
        }

        let function = FunctionSymbol { parameters: parameters, body: *function_body_id, return_type, name: identifier.to_string() };
        self.functions.push(function);
        Ok(())
    }

    pub fn lookup_function(&self, identifier: &str) -> Option<FunctionIndex> {
        self.functions.indexed_iter().find(|(_, function)| function.name == identifier).map(|(idx, _)| idx)
    }
}

struct LocalScope {
    locals: Vec<VariableIndex>,
}

impl LocalScope {
    fn new() -> Self {
        LocalScope { locals: Vec::new() }
    }

    fn add_local_var(&mut self, local: VariableIndex) {
        self.locals.push(local);
    }
}

struct ScopeStack {
    local_scopes: Vec<LocalScope>,
    global_scope: GlobalScope,
    surrounding_function: Option<FunctionIndex>,
}

impl ScopeStack {
    fn new() -> Self {
        ScopeStack { local_scopes: Vec::new(), global_scope: GlobalScope::new(), surrounding_function: None }
    }

    fn enter_scope(&mut self) {
        self.local_scopes.push(LocalScope::new());
    }

    fn enter_fx_scope(&mut self, fx_idx: FunctionIndex) {
        self.surrounding_function = Some(fx_idx);
        self.enter_scope();
    }
    
    fn exit_scope(&mut self) {
        self.local_scopes.pop();
    }

    fn exit_fx_scope(&mut self) {
        self.surrounding_function = None;
        self.exit_scope();
    }

    fn declare_variable(&mut self, identifier: &str, ty: Type) -> VariableIndex {
        let is_inside_local_scope = self.is_inside_local_scope();
        let index = self.global_scope.declare_variable(identifier, ty, !is_inside_local_scope);

        if is_inside_local_scope {
            self.current_local_scope_mut().add_local_var(index);
        }

        return index;
    }

    fn lookup_variable(&mut self, identifier: &str) -> Option<VariableIndex> { // top-down lookup
        for scope in self.local_scopes.iter_mut().rev() {
            if let Some((index, _variable)) = scope.locals.iter().map( // loop local var idxs
                |idx| (*idx, self.global_scope.variables.get(*idx)) // lookup idx in global_scope
            ).find(|(_idx, variable)| variable.name == identifier) { // use name to lookup var
                return Some(index)
            }
        }

        self.global_scope.lookup_global_variable(identifier)
    }

    fn lookup_function(&mut self, identifier: &str) -> Option<FunctionIndex> {
        self.global_scope.lookup_function(identifier)
    }

    fn is_inside_local_scope(&self) -> bool { // checks if variable is in local scope
        !self.local_scopes.is_empty()
    }

    fn from_global_scope(global_scope: GlobalScope) -> Self {
        ScopeStack {
            local_scopes: Vec::new(),
            global_scope,
            surrounding_function: None
        }
    }

    fn surrounding_function(&self) -> Option<&FunctionSymbol> {
        return self.surrounding_function.map(|idx| self.global_scope.functions.get(idx));
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
            BinaryOpKind::Multiply => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::Divide => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::Plus => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::Minus => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::BitwiseAnd => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::BitwiseXor => (Type::Int, Type::Int, Type::Int),
            BinaryOpKind::BitwiseOr => (Type::Int, Type::Int, Type::Int),
        };

        self.expect_type(type_matrix.0, &left.ty, &left.span(&ast));

        self.expect_type(type_matrix.1, &right.ty, &right.span(&ast));

        type_matrix.2
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

struct GlobalSymbolResolver {
    diagnostics: DiagnosticsReportCell,
    global_scope: GlobalScope,
}

impl GlobalSymbolResolver {
    fn new(diagnostics: DiagnosticsReportCell) -> Self {
        GlobalSymbolResolver { diagnostics, global_scope: GlobalScope::new() }
    }
}

impl ASTVisitor for GlobalSymbolResolver {
    fn visit_let_statement(&mut self, ast: &mut Ast, let_statement: &LetStatement, statement: &Statement) {
        
    }

    fn visit_variable_expression(&mut self, ast: &mut Ast, variable_expression: &VarExpression, expr: &Expression) {
        
    }

    fn visit_number_expression(&mut self, ast: &mut Ast, number: &NumberExpression, expr: &Expression) {
        
    }

    fn visit_boolean_expression(&mut self, ast: &mut Ast, boolean: &BoolExpression, expr: &Expression) {
        
    }

    fn visit_unary_expression(&mut self, ast: &mut Ast, unary_expression: &UnaryExpression, expr: &Expression) {
        
    }

    fn visit_function_declaration(&mut self, ast: &mut Ast, fx_decl_statement: &FxDeclaration) {
        let parameters = fx_decl_statement.parameters.iter().map(|parameter| self.global_scope.declare_variable( 
            &parameter.identifier.span.literal,
            resolve_type_from_string(&self.diagnostics, &parameter.type_annotation.type_name),
            false,
        )).collect();
        let literal_span = &fx_decl_statement.identifier.span;
        let return_type = match &fx_decl_statement.return_type {
            None => Type::Void, // each fx return type to be specified
            Some(return_type) => {
                resolve_type_from_string(&self.diagnostics, &return_type.type_name)
            }
        };
        match self.global_scope.declare_function(literal_span.literal.as_str(), &fx_decl_statement.body, parameters, return_type) {
            Ok(_) => {}
            Err(_) => {
                self.diagnostics.borrow_mut().report_function_already_declared(&fx_decl_statement.identifier);
            }
        }
    }

    fn visit_error(&mut self, ast: &mut Ast, span: &TextSpan) {
        
    }
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
            None => {
                initialiser_expression.ty.clone()
            }
        };

        let variable = self.scopes.declare_variable(&identifier, ty);
        ast.set_variable_for_statement(&statement.id, variable);
    }

    fn visit_variable_expression(&mut self, ast: &mut Ast, variable_expression: &VarExpression, expr: &Expression) {
        match self.scopes.lookup_variable(&variable_expression.identifier.span.literal) {
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

    fn visit_number_expression(&mut self, ast: &mut Ast, number: &NumberExpression, expr: &Expression) {
        ast.set_type(expr.id, Type::Int);
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

    fn visit_boolean_expression(&mut self, ast: &mut Ast, boolean: &BoolExpression, expr: &Expression) {
        ast.set_type(expr.id, Type::Bool);
    }

    fn visit_if_expression(&mut self, ast: &mut Ast, if_statement: &IfExpression, expr: &Expression) {
        self.scopes.enter_scope();
        self.visit_expression(ast, if_statement.condition);

        // conditional expression type check
        let conditional_expression = ast.query_expression(if_statement.condition);
        self.expect_type(Type::Bool, &conditional_expression.ty, &conditional_expression.span(&ast));

        self.visit_expression(ast, if_statement.then_branch);
        let mut ty = Type::Void;
        self.scopes.exit_scope();

        if let Some(else_branch) = &if_statement.else_branch {
            self.scopes.enter_scope();

            self.visit_expression(ast, else_branch.else_expression);

            let then_expression = ast.query_expression(if_statement.then_branch);
            let else_expression = ast.query_expression(else_branch.else_expression);
            ty = self.expect_type(then_expression.ty.clone(), &else_expression.ty, &else_expression.span(&ast));

            self.scopes.exit_scope();
        }

        ast.set_type(expr.id, ty);
    }
    
    fn visit_function_declaration(&mut self, ast: &mut Ast, fx_decl_statement: &FxDeclaration) {
        let fx_idx = self.scopes.lookup_function(&fx_decl_statement.identifier.span.literal).unwrap();
        self.scopes.enter_fx_scope(fx_idx);

        let function = self.scopes.global_scope.functions.get(fx_idx);
        for parameter in function.parameters.clone() {
            self.scopes.current_local_scope_mut().locals.push(parameter); // TODO: parameter types
        }

        self.visit_statement(ast, fx_decl_statement.body);
        self.scopes.exit_fx_scope();
    }

    fn visit_return_statement(&mut self, ast: &mut Ast, return_statement: &ReturnStatement) {
        let return_keyword = return_statement.return_keyword.clone();
        // todo: do not clone this
        match self.scopes.surrounding_function().map(|function| function.clone()) {
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
                    self.expect_type(Type::Void, &function.return_type, &return_keyword.span);
                }
            }
        }
    }

    fn visit_call_expression(&mut self, ast: &mut Ast, call_expression: &CallExpression, expr: &Expression) {
        let function = self.scopes.lookup_function(&call_expression.identifier.span.literal);
        let ty = match function {
            None => {
                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                diagnostics_binding.report_undeclared_function(&call_expression.identifier);

                Type::Void
            }
            Some(function) => {
                let function = self.scopes.global_scope.functions.get(function);
                if function.parameters.len() != call_expression.arguments.len() {
                    let mut diagnostics_binding = self.diagnostics.borrow_mut();
                    diagnostics_binding.report_invalid_arg_count(
                        &call_expression.identifier,
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

        self.visit_expression(ast, while_statement.body);
    }

    fn visit_error(&mut self, ast: &mut Ast, span: &TextSpan) {

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
        let diagnostics_report: DiagnosticsReportCell = Rc::new(RefCell::new(diagnostics::DiagnosticsReport::new()));
        let mut ast = Ast::new();
        let mut parser = Parser::new(
            tokens, 
            Rc::clone(&diagnostics_report),
            &mut ast
        );

        parser.parse();

        ast.visualise();

        // error handling (todo: improve)
        Self::check_diagnostics(&text, &diagnostics_report).map_err(|_| Rc::clone(&diagnostics_report))?;

        // symbol check
        let mut global_symbol_resolver = GlobalSymbolResolver::new(Rc::clone(&diagnostics_report));
        ast.visit(&mut global_symbol_resolver);
        let global_scope = global_symbol_resolver.global_scope;
        let scopes = ScopeStack::from_global_scope(global_scope);
        let mut resolver = Resolver::new(Rc::clone(&diagnostics_report), scopes);
        resolver.resolve(&mut ast);

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
        let main_function = self.global_scope.lookup_function("main");

        if let Some(function) = main_function {
            let function = self.global_scope.functions.get(function);
            eval.visit_statement(&mut self.ast, function.body);
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