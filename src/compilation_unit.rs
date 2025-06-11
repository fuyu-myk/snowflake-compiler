use crate::ast::{ASTBlockStatement, ASTBooleanExpression, ASTCallExpression, ASTFxDeclarationStatement, ASTIfStatement, ASTLetStatement, ASTNumberExpression, ASTStatement, ASTUnaryExpression, ASTVariableExpression, Ast};
use crate::ast::visitor::ASTVisitor;
use crate::ast::eval::ASTEvaluator;
use crate::diagnostics::{DiagnosticsReport, DiagnosticsReportCell};
use crate::text;
use crate::ast::lexer::{Lexer, TextSpan};
use crate::ast::parser::Parser;
use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use crate::diagnostics;
use crate::diagnostics::printer::DiagnosticsPrinter;

pub struct GlobalScope {
    variables: HashMap<String, ()>,
    pub functions: HashMap<String, FunctionSymbol>,
}

pub struct FunctionSymbol {
    pub parameters: Vec<String>,
    pub body: ASTStatement,
}

impl GlobalScope {
    fn new() -> Self {
        GlobalScope {
            variables: HashMap::new(),
            functions: HashMap::new(),
        } 
    }

    fn declare_variable(&mut self, identifier: &str) {
        self.variables.insert(identifier.to_string(), ());
    }

    fn lookup_variable(&self, identifier: &str) -> bool {
        self.variables.get(identifier).is_some()
    }

    fn declare_function(&mut self, identifier: &str, function: &ASTStatement, parameters: Vec<String>) -> Result<(), ()> {
        if self.functions.contains_key(identifier) { // handling similarly named functions
            return Err(())
        }

        let function = FunctionSymbol { parameters: parameters, body: function.clone() };
        self.functions.insert(identifier.to_string(), function);
        Ok(())
    }

    pub fn lookup_function(&self, identifier: &str) -> Option<&FunctionSymbol> {
        self.functions.get(identifier)
    }
}

struct LocalScope {
    variables: HashMap<String, ()>,
}

impl LocalScope {
    fn new() -> Self {
        LocalScope { variables: HashMap::new() }
    }

    fn declare_variable(&mut self, identifier: &str) {
        self.variables.insert(identifier.to_string(), ());
    }

    fn lookup_variable(&mut self, identifier:&str) -> bool {
        self.variables.get(identifier).is_some()
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
        self.local_scopes.push(LocalScope::new());
    }

    fn exit_scope(&mut self) {
        self.local_scopes.pop();
    }

    fn declare_variable(&mut self, identifier: &str) {
        if self.is_inside_local_scope() {
            self.local_scopes.last_mut().unwrap().declare_variable(identifier);
        } else {
            self.global_scope.declare_variable(identifier);
        }
    }

    fn lookup_variable(&mut self, identifier: &str) -> bool { // top-down lookup
        let in_local_scope = self.local_scopes.iter_mut().rev().any(|scope| scope.lookup_variable(identifier));
        if in_local_scope {
            return true;
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
}

struct Resolver {
    scopes: ScopeStack,
    diagnostics: DiagnosticsReportCell,
}

impl Resolver {
    fn new(diagnostics: DiagnosticsReportCell, scopes: ScopeStack) -> Self {
        Resolver {
            scopes,
            diagnostics,
        }
    }
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

impl ASTVisitor<'_> for GlobalSymbolResolver {
    fn visit_let_statement(&mut self, let_statement: &ASTLetStatement) {
        
    }

    fn visit_variable_expression(&mut self, variable_expression: &ASTVariableExpression) {
        
    }

    fn visit_number_expression(&mut self, number: &ASTNumberExpression) {
        
    }

    fn visit_boolean_expression(&mut self, boolean: &ASTBooleanExpression) {
        
    }

    fn visit_unary_expression(&mut self, unary_expression: &ASTUnaryExpression) {
        
    }

    fn visit_function_declaration_statement(&mut self, fx_decl_statement: &ASTFxDeclarationStatement) {
        let parameters = fx_decl_statement.parameters.iter().map(|parameter| parameter.identifier.span.literal.clone()).collect();
        let literal_span = &fx_decl_statement.identifier.span;
        match self.global_scope.declare_function(literal_span.literal.as_str(), &fx_decl_statement.body, parameters) {
            Ok(_) => {}
            Err(_) => {
                self.diagnostics.borrow_mut().report_function_already_declared(&fx_decl_statement.identifier);
            }
        }
    }

    fn visit_error(&mut self, span: &TextSpan) {
        
    }
}

impl ASTVisitor<'_> for Resolver {
    fn visit_let_statement(&mut self, statement: &ASTLetStatement) {
        let identifier = statement.identifier.span.literal.clone();
        self.visit_expression(&statement.initialiser);
        self.scopes.declare_variable(&identifier);
    }

    fn visit_variable_expression(&mut self, variable_expression: &ASTVariableExpression) {
        if !self.scopes.lookup_variable(&variable_expression.identifier.span.literal) {

            let mut diagnostics = self.diagnostics.borrow_mut();
            
            diagnostics.report_undeclared_variable(&variable_expression.identifier);
        }
    }

    fn visit_number_expression(&mut self, number: &ASTNumberExpression) {

    }

    fn visit_unary_expression(&mut self, unary_expression: &ASTUnaryExpression) {
        self.visit_expression(&unary_expression.operand);
    }

    fn visit_block_statement(&mut self, block_statement: &ASTBlockStatement) {
        self.scopes.enter_scope();

        for statement in &block_statement.statements {
            self.visit_statement(statement);
        }

        self.scopes.exit_scope();
    }

    fn visit_boolean_expression(&mut self, boolean: &ASTBooleanExpression) {
        
    }

    fn visit_if_statement(&mut self, if_statement: &ASTIfStatement) {
        self.scopes.enter_scope();
        self.visit_expression(&if_statement.condition);
        self.visit_statement(&if_statement.then_branch);
        self.scopes.exit_scope();

        if let Some(else_branch) = &if_statement.else_branch {
            self.scopes.enter_scope();
            self.visit_statement(&else_branch.else_statement);
            self.scopes.exit_scope();
        }
    }
    
    fn visit_function_declaration_statement(&mut self, fx_decl_statement: &ASTFxDeclarationStatement) {
        self.scopes.enter_scope();

        for parameter in &fx_decl_statement.parameters {
            self.scopes.declare_variable(&parameter.identifier.span.literal);
        }

        self.visit_statement(&fx_decl_statement.body);
        self.scopes.exit_scope();
    }

    fn visit_call_expression(&mut self, call_expression: &ASTCallExpression) {
        let function = self.scopes.lookup_function(&call_expression.identifier.span.literal);
        match function {
            None => {
                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                diagnostics_binding.report_undeclared_function(&call_expression.identifier);
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
            }
        }

        for argument in &call_expression.arguments {
            self.visit_expression(argument);
        }
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
        );

        while let Some(statement) = parser.next_statement() {
            ast.add_statement(statement);
        }

        ast.visualise();

        // error handling (todo: improve)
        Self::check_diagnostics(&text, &diagnostics_report).map_err(|_| Rc::clone(&diagnostics_report))?;

        // symbol check
        let mut global_symbol_resolver = GlobalSymbolResolver::new(Rc::clone(&diagnostics_report));
        ast.visit(&mut global_symbol_resolver);
        let global_scope = global_symbol_resolver.global_scope;
        let scopes = ScopeStack::from_global_scope(global_scope);
        let mut resolver = Resolver::new(Rc::clone(&diagnostics_report), scopes);
        ast.visit(&mut resolver);

        Self::check_diagnostics(&text, &diagnostics_report).map_err(|_| Rc::clone(&diagnostics_report))?;
        Ok(CompilationUnit { 
            ast, 
            diagnostics_report,
            global_scope: resolver.scopes.global_scope,
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
        let mut eval = ASTEvaluator::new(&self.global_scope);
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