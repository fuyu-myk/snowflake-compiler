/*
 * this program contains error message handling
 *  there are 2 types of diagnostics: warnings and errors
 *  the goal here is to be able to generate messages when such diagnostics are spotted
 */
pub mod printer;

use crate::ast::lexer::{Token, TokenKind, TextSpan};
use std::cell::RefCell;
use std::rc::Rc;


#[derive(Clone, Copy, Debug)]
pub enum DiagnosticKind {
    Error,
    Warning,
}

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub message: String,
    pub span: TextSpan,
    pub kind: DiagnosticKind,
}

impl Diagnostic {
    pub fn new(message: String, span: TextSpan, kind: DiagnosticKind) -> Self {
        Diagnostic { message, span, kind }
    }
}

pub type DiagnosticsReportCell = Rc<RefCell<DiagnosticsReport>>;

// for consistent error reporting
pub struct DiagnosticsReport {
    pub diagnostics: Vec<Diagnostic>,
}

impl DiagnosticsReport {
    pub fn new() -> Self {
        DiagnosticsReport { diagnostics: vec![] }
    }

    pub fn report_error(&mut self, message: String, span: TextSpan) {
        let error = Diagnostic::new(message, span, DiagnosticKind::Error);
        self.diagnostics.push(error);
    }

    pub fn report_warning(&mut self, message: String, span: TextSpan) {
        let warning = Diagnostic::new(message, span, DiagnosticKind::Warning);
        self.diagnostics.push(warning);
    }

    pub fn report_unexpected_token(&mut self, expected: &TokenKind, token: &Token) {
        self.report_error(format!("Expected <{}>, found <{}>", expected, token.kind), token.span.clone());
    }

    pub fn report_expected_expression(&mut self, token: &Token) {
        self.report_error(format!("Expected expression, found <{}>", token.kind), token.span.clone());
    }

    pub fn report_undeclared_variable(&mut self, token: &Token) {
        self.report_error(format!("Undeclared variable '{}'", token.span.literal), token.span.clone());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{compilation_unit::CompilationUnit};


    struct DiagnosticsVerifier {
        expected: Vec<Diagnostic>,
        actual: Vec<Diagnostic>,
    }

    impl DiagnosticsVerifier {
        pub fn new(input: &str, messages: Vec<&str>) -> Self {
            let expected = Self::parse_input(input, messages);
            let actual = Self::compile(input);

            Self { expected, actual }
        }

        fn compile(input: &str) -> Vec<Diagnostic> {
            let raw_text = Self::get_raw_text(input);
            let compilation_unit = CompilationUnit::compile(&raw_text);
            let diagnostics = compilation_unit.diagnostics_report.borrow();
            diagnostics.diagnostics.clone()
        }

        fn get_raw_text(input: &str) -> String {
            input.replace("«", "").replace("»", "")
        }

        fn parse_input(input: &str, messages: Vec<&str>) -> Vec<Diagnostic> {
            let raw_text = Self::get_raw_text(input);
            let mut start_index_stack = vec![];
            let mut current_position = 0;
            let mut diagnostics = vec![];

            for c in input.chars() {
                match c {
                    '«' => {
                        start_index_stack.push(current_position);
                    }
                    '»' => {
                        let start_index = start_index_stack.pop().unwrap();
                        let end_index = current_position;
                        let literal = &raw_text[start_index..end_index];
                        let span = TextSpan::new(start_index, end_index, literal.to_string());
                        let message = messages[diagnostics.len()].to_string();
                        let diagnostic = Diagnostic::new(message, span, DiagnosticKind::Error);
                        diagnostics.push(diagnostic);
                    }
                    _ => {
                        current_position += 1;
                    }
                };
            }
            diagnostics
        }

        fn verify (&self) {
            assert_eq!(self.actual.len(), self.expected.len(), "Expected {} diagnostics, found {}", self.expected.len(), self.actual.len());

            for (actual, expected) in self.actual.iter().zip(self.expected.iter()) {
                assert_eq!(actual.message, expected.message, "Expected message '{}', found '{}'", expected.message, actual.message);
                assert_eq!(actual.span.start, expected.span.start, "Expected start index {}, found {}", expected.span.start, actual.span.start);
                assert_eq!(actual.span.end, expected.span.end, "Expected end index {}, found {}", expected.span.end, actual.span.end);
                assert_eq!(actual.span.literal, expected.span.literal, "Expected literal {:?}, found {:?}", expected.span.literal, actual.span.literal);
            }
        }
    }

    #[test]
    fn test_undeclared_variable() {
        let input = "let a = «b»";
        let expected = vec![
            "Undeclared variable 'b'"
        ];

        let verifier = DiagnosticsVerifier::new(input, expected);
        verifier.verify();
    }

    #[test]
    fn test_expected_expression() {
        let input = "let a = «+»";
        let expected = vec![
            "Expected expression, found <+>"
        ];

        let verifier = DiagnosticsVerifier::new(input, expected);
        verifier.verify();
    }

    #[test]
    fn test_bad_token() {
        let input = "let a = 8 «@» 6";
        let expected = vec![
            "Expected expression, found <Bad>"
        ];

        let verifier = DiagnosticsVerifier::new(input, expected);
        verifier.verify();
    }

    #[test]
    fn test_undeclared_variable_when_variable_was_declared_in_another_scope() {
        let input = "\
        let a = 0
        let b = -1

        if b > a {
            a = 10
            b = 2
            let c = 10
        }
        else 
            a = 5
        a
        b
        «c»
        ";

        let expected = vec![
            "Undeclared variable 'c'"
        ];

        let verifier = DiagnosticsVerifier::new(input, expected);
        verifier.verify();
    }

    #[test]
    fn test_shadowing_variable() { // should not report errors
        let input = "\
        let a = 0
        {
            let a = 10
        }
        ";

        let expected = vec![];

        let verifier = DiagnosticsVerifier::new(input, expected);
        verifier.verify();
    }
}