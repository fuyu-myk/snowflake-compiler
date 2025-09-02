/*
 * this program contains error message handling
 *  there are 2 types of diagnostics: warnings and errors
 *  the goal here is to be able to generate messages when such diagnostics are spotted
 */
pub mod printer;

use crate::text::span::{TextSpan};
use crate::token::{Token, TokenKind};
use crate::typings::{ObjectKind, Type};
use std::cell::RefCell;
use std::rc::Rc;


#[derive(Clone, Copy, Debug)]
pub enum DiagnosticKind {
    Error,
    Warning,
}

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub message_brief: String,
    pub message_full: String,
    pub span: TextSpan,
    pub kind: DiagnosticKind,
}

impl Diagnostic {
    pub fn new(message_brief: String, message_full: String, span: TextSpan, kind: DiagnosticKind) -> Self {
        Diagnostic { message_brief, message_full, span, kind }
    }
}

pub type DiagnosticsReportCell = Rc<RefCell<DiagnosticsReport>>;

// for consistent error reporting
#[derive(Debug)]
pub struct DiagnosticsReport {
    pub errors: Vec<Diagnostic>,
    pub warnings: Vec<Diagnostic>,
}

impl DiagnosticsReport {
    pub fn new() -> Self {
        DiagnosticsReport { errors: vec![], warnings: vec![] }
    }

    pub fn report_error(&mut self, message_brief: String, message_full: String, span: TextSpan) {
        let error = Diagnostic::new(message_brief, message_full, span, DiagnosticKind::Error);
        self.errors.push(error);
    }

    pub fn report_warning(&mut self, message_brief: String, message_full: String, span: TextSpan) {
        let warning = Diagnostic::new(message_brief, message_full, span, DiagnosticKind::Warning);
        self.warnings.push(warning);
    }

    // Errors
    pub fn report_unexpected_token(&mut self, expected: &TokenKind, token: &Token) {
        self.report_error(
            format!("unexpected token"),
            format!("Expected token <{}>, found <{}>", expected, token.kind),
            token.span.clone(),
        );
    }

    /// Same as `DiagnosticsReport::report_unexpected_token` but with two expected tokens
    pub fn report_unexpected_token_two(
        &mut self, first_expected: &TokenKind, second_expected: &TokenKind, token: &Token
    ) {
        self.report_error(
            format!("unexpected token"),
            format!("Expected token <{}> or <{}>, found <{}>", first_expected, second_expected, token.kind),
            token.span.clone(),
        );
    }

    pub fn report_expected_expression(&mut self, token: &Token) {
        self.report_error(
            format!("expected expression"),
            format!("Expected expression, found <{}>", token.kind),
            token.span.clone(),
        );
    }

    pub fn report_undeclared_variable(&mut self, var: &str, span: &TextSpan) {
        self.report_error(
            format!("undeclared variable"),
            format!("Undeclared variable `{}`", var),
            span.clone(),
        );
    }

    pub fn report_uncallable_expression(&mut self, callee_span: &TextSpan, callee_type: &Type) {
        self.report_error(
            format!("calling non-callable expression"),
            format!("Unable to call non-callable expression of type `{}`", callee_type),
            callee_span.clone()
        );
    }

    pub fn report_invalid_arg_count(&mut self, callee_span: &TextSpan, expected: usize, actual: usize) {
        self.report_error(
            format!("invalid argument count"),
            format!("Function `{}` expects {} {}, but{} {} {} found",
                callee_span.literal,
                expected, if expected == 1 {"argument"} else {"arguments"},
                if actual < expected {" only"} else {""},
                actual, if actual == 1 {"was"} else {"were"}),
            callee_span.clone()
        );
    }

    pub fn report_function_already_declared(&mut self, token: &Token) {
        // TODO: print previous declaration
        self.report_error(
            format!("multiple function declarations"),
            format!("Function `{}` already declared", token.span.literal),
            token.span.clone()
        );
    }

    pub fn report_type_mismatch(&mut self, expected: &Type, actual: &Type, span: &TextSpan) {
        if matches!(expected, Type::Array(_, _)) {
            self.report_array_error(expected, actual, span);
            return;
        } else if matches!(expected, Type::Object(obj) if matches!(obj.kind, ObjectKind::Tuple)) {
            self.report_tuple_error(expected, actual, span);
            return;
        } else {
            self.report_error(
                format!("mismatched types"),
                format!("Expected type `{}`, found `{}`", expected, actual),
                span.clone()
            );
        }
    }

    pub fn report_undeclared_type(&mut self, token: &Token) {
        self.report_error(
            format!("undeclared type"),
            format!("Undeclared type `{}`", token.span.literal),
            token.span.clone()
        );
    }

    pub fn report_return_outside_function(&mut self, token: &Token) {
        self.report_error(
            format!("return outside function"),
            format!("Cannot use `return` outside of a function"),
            token.span.clone()
        );
    }

    pub fn report_undeclared_function(&mut self, token: &Token) {
        self.report_error(
            format!("undeclared function"),
            format!("Undeclared function `{}`", token.span.literal),
            token.span.clone()
        );
    }

    pub fn report_invalid_assignment_target(&mut self, operator: &str, span: &TextSpan) {
        self.report_error(
            format!("invalid left-hand side in assignment"),
            format!("Invalid left-hand side in assignment operation `{}`", operator),
            span.clone()
        );
    }

    pub fn report_division_by_zero(&mut self, operator: &str, span: &TextSpan) {
        self.report_error(
            format!("division by zero"),
            format!("Division by zero in `{}` operation", operator),
            span.clone()
        );
    }

    pub fn report_loop_keyword_outside_loop(&mut self, token: &Token) {
        self.report_error(
            format!("loop keyword used outside of loop"),
            format!("Cannot use `{}` outside of a loop", token.span.literal),
            token.span.clone()
        );
    }

    pub fn report_array_error(&mut self, expected: &Type, actual: &Type, span: &TextSpan) {
        if let (Type::Array(expected_type, expected_size), Type::Array(actual_type, actual_size)) = (expected, actual) {
            if !actual_type.is_assignable_to(expected_type) {
                self.report_error(
                    format!("mismatched types"),
                    format!("Expected `{}`, found `{}`", expected_type, actual_type),
                    span.clone()
                );
                return;
            } else if expected_size != actual_size {
                self.report_error(
                    format!("mismatched types"),
                    format!("Expected array of size {}, found one of size {}", expected_size, actual_size),
                    span.clone()
                );
                return;
            } else {
                self.report_error(
                    format!("mismatched types"),
                    format!("Expected array of type `{}`, found one of type `{}`", expected_type, actual_type),
                    span.clone()
                );
            }
        }
    }

    pub fn report_tuple_error(&mut self, expected: &Type, actual: &Type, span: &TextSpan) {
        if let (Type::Object(expected_obj), Type::Object(actual_obj)) = (expected, actual) {
            if matches!(expected_obj.kind, ObjectKind::Tuple) && 
               matches!(actual_obj.kind, ObjectKind::Tuple) {
                if expected_obj.fields.len() != actual_obj.fields.len() {
                    self.report_error(
                        format!("mismatched types"),
                        format!(
                            "Expected tuple with {} elements, found one with {} elements",
                            expected_obj.fields.len(), actual_obj.fields.len()
                        ),
                        span.clone()
                    );
                    return;
                }

                for (i, (exp_field, act_field)) in expected_obj.fields.iter().zip(actual_obj.fields.iter()).enumerate() {
                    if !act_field.ty.is_assignable_to(&exp_field.ty) {
                        self.report_error(
                            format!("mismatched types"),
                            format!("Type mismatch at tuple field {}: expected `{}`, found `{}`", i, exp_field.ty, act_field.ty),
                            span.clone()
                        );
                        return;
                    }
                }
            }
        }

        self.report_error(
            format!("mismatched types"),
            format!("Expected tuple of type `{}`, found one of type `{}`", expected, actual),
            span.clone()
        );
    }

    pub fn report_array_index_out_of_bounds(&mut self, index: &TextSpan, arr_size: String, array: &TextSpan) {
        self.report_error(
            format!("this operation will panic at runtime"),
            format!(
                "Index out of bounds: the length of array `{}` is {} but the index is {}",
                array.literal, arr_size, index.literal
            ),
            index.clone()
        );
    }

    pub fn report_tuple_unknown_field(&mut self, field: &TextSpan, wrong_ty: String) {
        self.report_error(
            format!("unknown field on {}", wrong_ty),
            format!("Unknown field: no field {} on type {}", field.literal, wrong_ty),
            field.clone()
        );
    }
    
    pub fn report_cannot_index_type(&mut self, ty: &Type, span: &TextSpan) {
        self.report_error(
            format!("inappropriate index operation"),
            format!("Cannot index type `{}`", ty),
            span.clone()
        );
    }

    pub fn report_no_fields_to_access(&mut self, ty: &Type, tuple_span: &TextSpan, index_span: &TextSpan) {
        match ty {
            Type::Array(ty, size) => {
                self.report_tuple_unknown_field(index_span, format!("[{}; {}]", ty, size));
            }
            _ => {
                self.report_error(
                    format!("{} has no fields", ty),
                    format!("`{}` is a primitive type and therefore doesn't have any fields", ty),
                    tuple_span.clone()
                );
            }
        }
    }

    pub fn report_index_type_mismatch(&mut self, expected: Type, actual: &Type, span: &TextSpan) {
        self.report_error(
            format!("index type mismatch"),
            format!("Cannot be indexed by `{}` (slice indices are of type `{}`)", actual, expected),
            span.clone()
        );
    }

    pub fn report_negative_array_index(&mut self, span: &TextSpan) {
        self.report_error(
            format!("negative array index"),
            format!("Negative integers cannot be used to index on arrays"),
            span.clone()
        );
    }

    pub fn report_immutable_assignment_error(&mut self, expression: String, object: Option<String>, span: &TextSpan) {
        if let Some(object) = object {
            self.report_error(
                format!("assignment to immutable variable"),
                format!("Cannot assign to `{}` because `{}` is not declared as mutable", expression, object),
                span.clone()
            );
        } else {
            self.report_error(
                format!("assignment to immutable variable"),
                format!("Cannot assign to immutable variable `{}`", expression),
                span.clone()
            );
        }
    }

    pub fn report_multiple_assignment_error(&mut self, variable: String, span: &TextSpan) {
        self.report_error(
            format!("multiple assignment to immutable variable"),
            format!("Cannot assign to immutable variable `{}` more than once", variable),
            span.clone()
        );
    }

    pub fn report_const_missing_type(&mut self, identifier: &Token) {
        self.report_error(
            format!("missing type for `const` item"),
            format!("Missing type annotation for `const` item `{}`", identifier.span.literal),
            identifier.span.clone()
        );
    }

    pub fn report_assignment_error(&mut self, variable: String, span: &TextSpan) {
        self.report_error(
            format!("invalid left-hand side of assignment"),
            format!("Cannot assign to constant variable `{}`", variable),
            span.clone()
        );
    }

    pub fn report_expected_item(&mut self, token: &Token) {
        self.report_error(
            format!("expected item"),
            format!("Expected item, found {}", token.kind),
            token.span.clone()
        );
    }

    pub fn report_duplicate_local_struct(&mut self, name: String, span: &TextSpan) {
        self.report_error(
            format!("multiple struct declarations"),
            format!("Struct `{}` already declared in this scope", name),
            span.clone()
        );
    }

    pub fn report_duplicate_global_struct(&mut self, name: String, span: &TextSpan) {
        self.report_error(
            format!("multiple struct declarations"),
            format!("Struct `{}` already declared globally", name),
            span.clone()
        );
    }

    pub fn report_unknown_field_in_object(&mut self, field: String, object: String, span: &TextSpan) {
        self.report_error(
            format!("unknown field in object"),
            format!("Object `{}` does not have a field `{}`", object, field),
            span.clone()
        );
    }

    pub fn report_undefined_struct(&mut self, name: String, span: &TextSpan) {
        self.report_error(
            format!("undefined struct"),
            format!("Struct `{}` is not defined", name),
            span.clone()
        );
    }

    pub fn report_invalid_field_kind(&mut self, invalid_field: String, span: &TextSpan) {
        self.report_error(
            format!("invalid field kind"),
            format!("Expected field name, found `{}`", invalid_field),
            span.clone()
        );
    }

    // Warnings
    pub fn warn_non_upper_case(&mut self, variable: &str, span: &TextSpan) {
        self.report_warning(
            format!("constant `{}` should have an upper case name", variable),
            format!("constant `{}` should have an upper case name", variable),
            span.clone()
        );
    }

    pub fn warn_non_upper_camel_case(&mut self, variable: &str, span: &TextSpan) {
        self.report_warning(
            format!("constant `{}` should have an upper camel case name", variable),
            format!("constant `{}` should have an upper camel case name", variable),
            span.clone()
        );
    }
}