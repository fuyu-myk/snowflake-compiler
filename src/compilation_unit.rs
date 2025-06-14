use crate::ast::{AssignExpression, BinaryExpression, BinaryOpKind, BlockStatement, BoolExpression, CallExpression, Expression, 
    FxDeclarationStatement, IfStatement, LetStatement, NumberExpression, ParenExpression, ReturnStatement, StatementId, UnaryExpression, 
    UnaryOpKind, VarExpression, WhileStatement, Ast, FxDeclarationParams};
use crate::ast::visitor::ASTVisitor;
use crate::ast::eval::ASTEvaluator;
use crate::diagnostics::{DiagnosticsReportCell};
use crate::text;
use crate::ast::lexer::{Lexer, Token};
use crate::ast::parser::Parser;
use crate::text::span::TextSpan;
use crate::typings::Type;
use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use crate::diagnostics;
use crate::diagnostics::printer::DiagnosticsPrinter;


#[derive(Debug, Clone)]
pub struct FunctionSymbol {
    pub parameters: Vec<VariableSymbol>,
    pub body: StatementId,
    pub return_type: Type,
}

#[derive(Debug, Clone)]
pub struct VariableSymbol {
    pub name: String,
    pub ty: Type,
}

pub struct GlobalScope {
    variables: HashMap<String, VariableSymbol>,
    pub functions: HashMap<String, FunctionSymbol>,
}

impl GlobalScope {
    fn new() -> Self {
        GlobalScope {
            variables: HashMap::new(),
            functions: HashMap::new(),
        } 
    }

    fn declare_variable(&mut self, identifier: &str, ty: Type) {
        let variable = VariableSymbol { name: identifier.to_string(), ty };
        self.variables.insert(identifier.to_string(), variable);
    }

    fn lookup_variable(&self, identifier: &str) -> Option<&VariableSymbol> {
        self.variables.get(identifier)
    }

    fn declare_function(&mut self, identifier: &str, function_body_id: &StatementId, parameters: Vec<VariableSymbol>, return_type: Type) -> Result<(), ()> {
        if self.functions.contains_key(identifier) { // handling similarly named functions
            return Err(())
        }

        let function = FunctionSymbol { parameters: parameters, body: function_body_id.clone(), return_type };
        self.functions.insert(identifier.to_string(), function);
        Ok(())
    }

    pub fn lookup_function(&self, identifier: &str) -> Option<&FunctionSymbol> {
        self.functions.get(identifier)
    }
}

struct LocalScope {
    variables: HashMap<String, VariableSymbol>,
    function: Option<FunctionSymbol>,
    // todo: make reference
}

impl LocalScope {
    fn new(function: Option<FunctionSymbol>) -> Self {
        LocalScope { variables: HashMap::new(), function }
    }

    fn declare_variable(&mut self, identifier: &str, ty: Type) {
        let variable = VariableSymbol { name:identifier.to_string(), ty };
        self.variables.insert(identifier.to_string(), variable);
    }

    fn lookup_variable(&mut self, identifier:&str) -> Option<&VariableSymbol> {
        self.variables.get(identifier)
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

    fn enter_scope(&mut self, function: Option<FunctionSymbol>) {
        self.local_scopes.push(LocalScope::new(function));
    }

    fn exit_scope(&mut self) {
        self.local_scopes.pop();
    }

    fn declare_variable(&mut self, identifier: &str, ty: Type) {
        if self.is_inside_local_scope() {
            self.local_scopes.last_mut().unwrap().declare_variable(identifier, ty);
        } else {
            self.global_scope.declare_variable(identifier, ty);
        }
    }

    fn lookup_variable(&mut self, identifier: &str) -> Option<&VariableSymbol> { // top-down lookup
        for scope in self.local_scopes.iter_mut().rev() {
            if let Some(variable) = scope.lookup_variable(identifier) {
                return Some(variable)
            }
        }

        self.global_scope.lookup_variable(identifier)
    }

    fn lookup_function(&mut self, identifier: &str) -> Option<&FunctionSymbol> {
        self.global_scope.lookup_function(identifier)
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

    fn surrounding_function(&self) -> Option<&FunctionSymbol> {
        for scope in self.local_scopes.iter().rev() {
            if let Some(function) = &scope.function {
                return Some(function)
            }
        }
        None
    }
}

struct Resolver<'a> {
    scopes: ScopeStack,
    diagnostics: DiagnosticsReportCell,
    ast: &'a mut Ast,
}

fn expect_type(diagnostics: &DiagnosticsReportCell, expected: Type, actual: &Type, span: &TextSpan) {
    if !actual.is_assignable_to(&expected) {
        diagnostics.borrow_mut().report_type_mismatch(&expected, actual, span);
    }
}

impl <'a> Resolver<'a> {
    fn new(diagnostics: DiagnosticsReportCell, scopes: ScopeStack, ast: &'a mut Ast) -> Self {
        Resolver {
            scopes,
            diagnostics,
            ast,
        }
    }

    fn expect_type(&self, expected: Type, actual: &Type, span: &TextSpan) {
        expect_type(&self.diagnostics, expected, actual, span);
    }

    pub fn resolve(&mut self) {
        let stmt_ids: Vec<StatementId> = self.ast.top_level_statements.iter().map(|stmt| stmt.clone()).collect();
        for stmt_id in stmt_ids {
            self.visit_statement(&stmt_id);
        }
    }

    pub fn resolve_binary_expression(&self, left: &Expression, right: &Expression, operator: &BinaryOpKind) -> Type {
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

        self.expect_type(type_matrix.0, &left.ty, &left.span(&self.ast));

        self.expect_type(type_matrix.1, &right.ty, &right.span(&self.ast));

        type_matrix.2
    }

    pub fn resolve_unary_expression(&self, operand: &Expression, operator: &UnaryOpKind) -> Type {
        let type_matrix: (Type, Type) = match operator {
            UnaryOpKind::Negation => (Type::Int, Type::Int),
            UnaryOpKind::BitwiseNot => (Type::Int, Type::Int),
        };

        self.expect_type(type_matrix.0, &operand.ty, &operand.span(&self.ast));

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

struct GlobalSymbolResolver<'a> {
    diagnostics: DiagnosticsReportCell,
    global_scope: GlobalScope,
    ast: &'a Ast,
}

impl <'a> GlobalSymbolResolver<'a> {
    fn new(diagnostics: DiagnosticsReportCell, ast: &'a Ast) -> Self {
        GlobalSymbolResolver { diagnostics, global_scope: GlobalScope::new(), ast }
    }
}

impl ASTVisitor for GlobalSymbolResolver<'_> {
    fn get_ast(&self) -> &Ast {
        self.ast
    }

    fn visit_let_statement(&mut self, let_statement: &LetStatement) {
        
    }

    fn visit_variable_expression(&mut self, variable_expression: &VarExpression, expr: &Expression) {
        
    }

    fn visit_number_expression(&mut self, number: &NumberExpression, expr: &Expression) {
        
    }

    fn visit_boolean_expression(&mut self, boolean: &BoolExpression, expr: &Expression) {
        
    }

    fn visit_unary_expression(&mut self, unary_expression: &UnaryExpression, expr: &Expression) {
        
    }

    fn visit_function_declaration_statement(&mut self, fx_decl_statement: &FxDeclarationStatement) {
        let parameters = fx_decl_statement.parameters.iter().map(|parameter| VariableSymbol {
            name: parameter.identifier.span.literal.clone(),
            ty: resolve_type_from_string(&self.diagnostics, &parameter.type_annotation.type_name),
        }).collect();
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

    fn visit_error(&mut self, span: &TextSpan) {
        
    }
}

impl ASTVisitor for Resolver<'_> {
    fn get_ast(&self) -> &Ast {
        self.ast    
    }

    fn visit_let_statement(&mut self, let_statement: &LetStatement) {
        let identifier = let_statement.identifier.span.literal.clone();
        self.visit_expression(&let_statement.initialiser);
        let initialiser_expression = &self.ast.query_expression(&let_statement.initialiser);

        let ty = match &let_statement.type_annotation {
            Some(type_annotation) => {
                let ty = resolve_type_from_string(&self.diagnostics, &type_annotation.type_name);
                self.expect_type(ty.clone(), &initialiser_expression.ty, &initialiser_expression.span(&self.ast));
                ty
            }
            None => {
                initialiser_expression.ty.clone()
            }
        };

        self.scopes.declare_variable(&identifier, ty);
    }

    fn visit_variable_expression(&mut self, variable_expression: &VarExpression, expr: &Expression) {
        match self.scopes.lookup_variable(&variable_expression.identifier.span.literal) {
            None => {
                let mut diagnostics = self.diagnostics.borrow_mut();
                diagnostics.report_undeclared_variable(&variable_expression.identifier);
            }

            Some(variable) => {
                self.ast.set_type(&expr.id, variable.ty.clone());
            }
        };
    }

    fn visit_number_expression(&mut self, number: &NumberExpression, expr: &Expression) {
        self.ast.set_type(&expr.id, Type::Int);
    }

    fn visit_unary_expression(&mut self, unary_expression: &UnaryExpression, expr: &Expression) {
        self.visit_expression(&unary_expression.operand);

        let operand = self.ast.query_expression(&unary_expression.operand);
        let ty = self.resolve_unary_expression(&operand, &unary_expression.operator.kind);

        self.ast.set_type(&expr.id, ty);
    }

    fn visit_binary_expression(&mut self, binary_expression: &BinaryExpression, expr: &Expression) {
        self.visit_expression(&binary_expression.left);
        self.visit_expression(&binary_expression.right);
        
        let left = self.ast.query_expression(&binary_expression.left);
        let right = self.ast.query_expression(&binary_expression.right);

        let ty = self.resolve_binary_expression(&left, &right, &binary_expression.operator.kind);
        self.ast.set_type(&expr.id, ty);
    }

    fn visit_parenthesised_expression(&mut self, parenthesised_expression: &ParenExpression, expr: &Expression) {
        self.visit_expression(&parenthesised_expression.expression);

        let expression = self.ast.query_expression(&parenthesised_expression.expression);

        self.ast.set_type(&expr.id, expression.ty.clone());
    }

    fn visit_block_statement(&mut self, block_statement: &BlockStatement) {
        self.scopes.enter_scope(None);

        for statement in &block_statement.statements {
            self.visit_statement(statement);
        }

        self.scopes.exit_scope();
    }

    fn visit_boolean_expression(&mut self, boolean: &BoolExpression, expr: &Expression) {
        self.ast.set_type(&expr.id, Type::Bool);
    }

    fn visit_if_statement(&mut self, if_statement: &IfStatement) {
        self.scopes.enter_scope(None);
        self.visit_expression(&if_statement.condition);

        // conditional expression type check
        let conditional_expression = self.ast.query_expression(&if_statement.condition);
        self.expect_type(Type::Bool, &conditional_expression.ty, &conditional_expression.span(&self.ast));

        self.visit_statement(&if_statement.then_branch);
        self.scopes.exit_scope();

        if let Some(else_branch) = &if_statement.else_branch {
            self.scopes.enter_scope(None);
            self.visit_statement(&else_branch.else_statement);
            self.scopes.exit_scope();
        }
    }
    
    fn visit_function_declaration_statement(&mut self, fx_decl_statement: &FxDeclarationStatement) {
        let function_symbol = self.scopes.lookup_function(&fx_decl_statement.identifier.span.literal).unwrap().clone();
        self.scopes.enter_scope(Some(function_symbol.clone()));

        for parameter in &function_symbol.parameters {
            self.scopes.declare_variable(&parameter.name, parameter.ty.clone()); // TODO: parameter types
        }

        self.visit_statement(&fx_decl_statement.body);
        self.scopes.exit_scope();
    }

    fn visit_return_statement(&mut self, return_statement: &ReturnStatement) {
        let return_keyword = return_statement.return_keyword.clone();
        // todo: do not clone this
        match self.scopes.surrounding_function().map(|function| function.clone()) {
            None => {
                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                diagnostics_binding.report_return_outside_function(&return_statement.return_keyword);
            }
            Some(function) => {
                if let Some(return_expression) = &return_statement.return_value {
                    self.visit_expression(return_expression);
                    let return_expression = self.ast.query_expression(return_expression);
                    self.expect_type(function.return_type.clone(), &return_expression.ty, &return_expression.span(&self.ast));
                } else {
                    self.expect_type(Type::Void, &function.return_type, &return_keyword.span);
                }
            }
        }
    }

    fn visit_call_expression(&mut self, call_expression: &CallExpression, expr: &Expression) {
        // todo: do not clone
        let function = self.scopes.lookup_function(&call_expression.identifier.span.literal).map(|function| function.clone());
        let ty = match function {
            None => {
                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                diagnostics_binding.report_undeclared_function(&call_expression.identifier);

                Type::Void
            }
            Some(function) => {
                if function.parameters.len() != call_expression.arguments.len() {
                    let mut diagnostics_binding = self.diagnostics.borrow_mut();
                    diagnostics_binding.report_invalid_arg_count(
                        &call_expression.identifier,
                        function.parameters.len(),
                        call_expression.arguments.len(),
                    );
                }

                let return_type = function.return_type.clone();
                for (argument, parameter) in call_expression.arguments.iter().zip(function.parameters.iter()) {
                    self.visit_expression(argument);
                    let argument_expression = self.ast.query_expression(argument);
                    self.expect_type(parameter.ty.clone(), &argument_expression.ty, &argument_expression.span(&self.ast));
                }

                return_type
            }
        };

        self.ast.set_type(&expr.id, ty);
    }

    fn visit_assignment_expression(&mut self, assignment_expression: &AssignExpression, expr: &Expression) {
        self.visit_expression(&assignment_expression.expression);
        let value_expression = self.ast.query_expression(&assignment_expression.expression);
        let identifier = assignment_expression.identifier.span.literal.clone();
        let ty = match self.scopes.lookup_variable(&identifier) {
            None => {
                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                diagnostics_binding.report_undeclared_variable(&assignment_expression.identifier);
                Type::Void
            }
            Some(variable) => {
                let variable_ty = variable.ty.clone();
                self.expect_type(variable_ty.clone(), &value_expression.ty, &value_expression.span(&self.ast));
                variable_ty
            }
        };

        self.ast.set_type(&expr.id, ty);
    }

    fn visit_while_statement(&mut self, while_statement: &WhileStatement) {
        self.visit_expression(&while_statement.condition);
        let condition = self.ast.query_expression(&while_statement.condition);
        self.expect_type(Type::Bool, &condition.ty, &condition.span(&self.ast));

        self.visit_statement(&while_statement.body);
    }

    fn visit_error(&mut self, span: &TextSpan) {

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
        let mut global_symbol_resolver = GlobalSymbolResolver::new(Rc::clone(&diagnostics_report), &ast);
        ast.visit(&mut global_symbol_resolver);
        let global_scope = global_symbol_resolver.global_scope;
        let scopes = ScopeStack::from_global_scope(global_scope);
        let mut resolver = Resolver::new(Rc::clone(&diagnostics_report), scopes, &mut ast);
        resolver.resolve();

        Self::check_diagnostics(&text, &diagnostics_report).map_err(|_| Rc::clone(&diagnostics_report))?;
        Ok(CompilationUnit { 
            global_scope: resolver.scopes.global_scope,
            ast, 
            diagnostics_report,
        })
    }

    pub fn run_errorless(&self) {
        if self.diagnostics_report.borrow().diagnostics.len() > 0 {
            if self.diagnostics_report.borrow().diagnostics.len() == 1 {
                println!("Compilation failed due to {} previous error.", self.diagnostics_report.borrow().diagnostics.len());
                return;
            } else {
                println!("Compilation failed due to {} previous errors.", self.diagnostics_report.borrow().diagnostics.len());
                return;
            }
        }

        self.run_compiler();
    }
    pub fn run_compiler(&self) {
        // evaluator (temp)
        let mut eval = ASTEvaluator::new(&self.global_scope, &self.ast);
        let main_function = self.global_scope.lookup_function("main");

        if let Some(function) = main_function {
            eval.visit_statement(&function.body);
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
        return Err(());
        }
    Ok(())
    }
}