use std::collections::HashMap;

use crate::ast::lexer::{Lexer, TextSpan};
use crate::ast::{ASTBinaryExpression, ASTLetStatement, ASTNumberExpression, ASTParenthesisedExpression, ASTVariableExpression, Ast, ASTVisitor};
use crate::ast::parser::Parser;
use crate::ast::eval::ASTEvaluator;
use crate::diagnostics::DiagnosticsReportCell;
use crate::diagnostics::printer::DiagnosticsPrinter;
use crate::text::SourceText;
use std::rc::Rc;
use std::cell::RefCell;

mod ast;
mod diagnostics;
mod text;

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

fn check_diagnostics(text: &SourceText, diagnostics_report: &DiagnosticsReportCell) -> Result<(), ()> {
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

fn main() -> Result<(), ()> {
    let input = "
        let a =2 + 3
        let b = 9
        let c = 42 + e
        let d = (a + b) * c
    ";
    let text = text::SourceText::new(input.to_string());

    // lexer
    let mut lexer = Lexer::new(input);
    let mut tokens = Vec::new();

    while let Some(token) = lexer.next_token() {
        tokens.push(token);
    }

    // println!("{:?}", tokens); // uncomment to see tokens

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

    //symbol check
    let mut symbol_check = SymbolCheck::new(Rc::clone(&diagnostics_report));
    ast.visit(&mut symbol_check);

    // error handler
    check_diagnostics(&text, &diagnostics_report)?;

    // evaluator (temp)
    let mut eval = ASTEvaluator::new();
    ast.visit(&mut eval);
    println!("Result: {:?}", eval.last_value);

    Ok(())
}