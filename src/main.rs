use crate::ast::lexer::Lexer;
use crate::ast::Ast;
use crate::ast::parser::Parser;
use crate::ast::eval::ASTEvaluator;
use crate::diagnostics::DiagnosticsReportCell;
use crate::diagnostics::printer::DiagnosticsPrinter;
use std::rc::Rc;
use std::cell::RefCell;

mod ast;
mod diagnostics;
mod text;


fn main() {
    let input = "
        let a = 10
        let b = 20
        let c = a + b
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

    // error handler
    let diagnostics_binding = diagnostics_report.borrow();
    if diagnostics_binding.diagnostics.len() > 0 {
        let diagnostics_printer = DiagnosticsPrinter::new(
            &text,
            &diagnostics_binding.diagnostics
        );

        diagnostics_printer.print();
        return;
    }

    // evaluator (temp)
    let mut eval = ASTEvaluator::new();
    ast.visit(&mut eval);
    println!("Result: {:?}", eval.last_value);
}