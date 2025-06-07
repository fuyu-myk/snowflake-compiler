use crate::ast::{Ast, ASTVisitor, ASTLetStatement, ASTVariableExpression, ASTNumberExpression};
use crate::ast::eval::ASTEvaluator;
use crate::diagnostics::DiagnosticsReportCell;
use crate::text;
use crate::ast::lexer::{Lexer, TextSpan};
use crate::ast::parser::Parser;
use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use crate::diagnostics;
use crate::diagnostics::printer::DiagnosticsPrinter;

struct SymbolCheck {
    symbols: HashMap<String, ()>,
    diagnostics: DiagnosticsReportCell,
}

impl SymbolCheck {
    fn new(diagnostics: DiagnosticsReportCell) -> Self {
        SymbolCheck {
            symbols: HashMap::new(),
            diagnostics,
        }
    }
}

impl ASTVisitor for SymbolCheck {
    fn visit_let_statement(&mut self, statement: &ASTLetStatement) {
        let identifier = statement.identifier.span.literal.clone();
        self.visit_expression(&statement.initialiser);
        self.symbols.insert(identifier, ());
    }

    fn visit_variable_expression(&mut self, variable_expression: &ASTVariableExpression) {
        if self.symbols.get(&variable_expression.identifier.span.literal).is_none() {

            let mut diagnostics = self.diagnostics.borrow_mut();
            
            diagnostics.report_undeclared_variable(&variable_expression.identifier);
        }
    }

    fn visit_number_expression(&mut self, number: &ASTNumberExpression) {

    }

    fn visit_error(&mut self, span: &TextSpan) {

    }
}

pub struct CompilationUnit {
    pub ast: Ast,
    pub diagnostics_report: DiagnosticsReportCell,
}

impl CompilationUnit {
    pub fn compile(input: &str) -> CompilationUnit {
        let text = text::SourceText::new(input.to_string());

        // lexer
        let mut lexer = Lexer::new(input);
        let mut tokens = Vec::new();

        while let Some(token) = lexer.next_token() {
            tokens.push(token);
        }

        // parser & ast
        let diagnostics_report: DiagnosticsReportCell = Rc::new(RefCell::new(diagnostics::DiagnosticsReport::new()));
        let mut ast: Ast = Ast::new();
        let mut parser = Parser::new(
            tokens, 
            Rc::clone(&diagnostics_report)
        );

        while let Some(statement) = parser.next_statement() {
            ast.add_statement(statement);
        }

        ast.visualise();

        // error handling (todo: improve)
        if Self::check_diagnostics(&text, &diagnostics_report).is_err() {
            return Self::create_compilation_unit(ast, diagnostics_report);
        }

        // symbol check
        let mut symbol_check = SymbolCheck::new(Rc::clone(&diagnostics_report));
        ast.visit(&mut symbol_check);

        if Self::check_diagnostics(&text, &diagnostics_report).is_err() {
            return Self::create_compilation_unit(ast, diagnostics_report);
        }
        Self::create_compilation_unit(ast, diagnostics_report)
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
    fn run_compiler(&self) {
        // evaluator (temp)
        let mut eval = ASTEvaluator::new();
        self.ast.visit(&mut eval);
        println!("Result: {:?}", eval.last_value);
    }

    fn create_compilation_unit(ast: Ast, diagnostics_report: DiagnosticsReportCell) -> CompilationUnit {
        // check diagnostics before returning the compilation unit
        CompilationUnit {
            ast,
            diagnostics_report,
        }
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