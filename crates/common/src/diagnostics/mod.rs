/*
 * this program contains error message handling
 *  there are 2 types of diagnostics: warnings and errors
 *  the goal here is to be able to generate messages when such diagnostics are spotted
 */
pub mod printer;

use crate::text::span::TextSpan;
use crate::token::{Token, TokenKind};
use crate::typings::Type;
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
#[derive(Debug)]
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

    pub fn report_uncallable_expression(&mut self, callee_span: &TextSpan, callee_type: &Type) {
        self.report_error(format!("Unable to call non-callable expression of type '{}'", callee_type), callee_span.clone());
    }

    pub fn report_invalid_arg_count(&mut self, callee_span: &TextSpan, expected: usize, actual: usize) {
        self.report_error(
            format!("Function '{}' expects {} {}, but{} {} {} found",
            callee_span.literal,
            expected, if expected == 1 {"argument"} else {"arguments"},
            if actual < expected {" only"} else {""},
            actual, if actual == 1 {"was"} else {"were"}), callee_span.clone());
    }

    pub fn report_function_already_declared(&mut self, token: &Token) {
        self.report_error(format!("Function '{}' already declared", token.span.literal), token.span.clone());
    }

    pub fn report_type_mismatch(&mut self, expected: &Type, actual: &Type, span: &TextSpan) {
        if matches!(expected, Type::Array(_, _)) {
            self.report_array_error(expected, actual, span);
            return;
        } else if matches!(expected, Type::Tuple(_)) {
            self.report_tuple_error(expected, actual, span);
            return;
        } else {
            self.report_error(format!("Expected type '{}', found '{}'", expected, actual), span.clone());
        }
    }

    pub fn report_undeclared_type(&mut self, token: &Token) {
        self.report_error(format!("Undeclared type '{}'", token.span.literal), token.span.clone());
    }

    pub fn report_return_outside_function(&mut self, token: &Token) {
        self.report_error(format!("Cannot use 'return' outside of a function"), token.span.clone());
    }

    pub fn report_rec_outside_function(&mut self, token: &Token) {
        self.report_error(format!("Cannot use 'rec' outside of a function"), token.span.clone());
    }

    pub fn report_undeclared_function(&mut self, token: &Token) {
        self.report_error(format!("Undeclared function '{}'", token.span.literal), token.span.clone());
    }

    pub fn report_invalid_assignment_target(&mut self, operator: &str, span: &TextSpan) {
        self.report_error(format!("Invalid left-hand side in assignment operation '{}'", operator), span.clone());
    }

    pub fn report_division_by_zero(&mut self, operator: &str, span: &TextSpan) {
        self.report_error(format!("Division by zero in '{}' operation", operator), span.clone());
    }

    pub fn report_loop_keyword_outside_loop(&mut self, token: &Token) {
        self.report_error(format!("Cannot use '{}' outside of a loop", token.span.literal), token.span.clone());
    }

    pub fn report_array_error(&mut self, expected: &Type, actual: &Type, span: &TextSpan) {
        if let (Type::Array(expected_type, expected_size), Type::Array(actual_type, actual_size)) = (expected, actual) {
            if !actual_type.is_assignable_to(expected_type) {
                self.report_error(format!("Expected '{}', found '{}'", expected_type, actual_type), span.clone());
                return;
            } else if expected_size != actual_size {
                self.report_error(format!("Expected array of size {}, found one of size {}", expected_size, actual_size), span.clone());
                return;
            } else {
                self.report_error(format!("Expected array of type '{}', found one of type '{}'", expected_type, actual_type), span.clone());
            }
        }
    }

    pub fn report_tuple_error(&mut self, expected: &Type, actual: &Type, span: &TextSpan) {
        if let (Type::Tuple(expected_types), Type::Tuple(actual_types)) = (expected, actual) {
            if expected_types.len() != actual_types.len() {
                self.report_error(format!("Expected tuple of size {}, found one of size {}", expected_types.len(), actual_types.len()), span.clone());
                return;
            }

            for (i, (exp_ty, act_ty)) in expected_types.iter().zip(actual_types.iter()).enumerate() {
                if !act_ty.is_assignable_to(exp_ty) {
                    self.report_error(format!("Type mismatch at tuple index {}: expected '{}', found '{}'", i, exp_ty, act_ty), span.clone());
                    return;
                }
            }

            self.report_error(format!("Expected tuple of type '{}', found one of type '{}'", expected, actual), span.clone());
        }
    }

    pub fn report_array_index_out_of_bounds(&mut self, index: &TextSpan, arr_size: String, array: &TextSpan) {
        self.report_error(format!("Index out of bounds: the length of array `{}` is {} but the index is {}", array.literal, arr_size, index.literal), index.clone());
    }

    pub fn report_tuple_unknown_field(&mut self, field: &TextSpan, wrong_ty: String) {
        self.report_error(format!("Unknown field: no field {} on type {}", field.literal, wrong_ty), field.clone());
    }
    
    pub fn report_cannot_index_type(&mut self, ty: &Type, span: &TextSpan) {
        self.report_error(format!("Cannot index type '{}'", ty), span.clone());
    }

    pub fn report_no_fields_to_access(&mut self, ty: &Type, tuple_span: &TextSpan, index_span: &TextSpan) {
        match ty {
            Type::Array(ty, size) => {
                self.report_tuple_unknown_field(index_span, format!("[{}; {}]", ty, size));
            }
            _ => {
                self.report_error(format!("'{}' is a primitive type and therefore doesn't have any fields", ty), tuple_span.clone());
            }
        }
    }

    pub fn report_index_type_mismatch(&mut self, expected: Type, actual: &Type, span: &TextSpan) {
        self.report_error(format!("Cannot be indexed by '{}' (slice indices are of type '{}')", actual, expected), span.clone());
    }

    pub fn report_negative_array_index(&mut self, span: &TextSpan) {
        self.report_error(format!("Negative integers cannot be used to index on arrays"), span.clone());
    }
}