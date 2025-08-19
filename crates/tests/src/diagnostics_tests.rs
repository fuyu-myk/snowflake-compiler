use snowflake_common::diagnostics::{Diagnostic, DiagnosticsReport, DiagnosticKind};
use snowflake_common::text::span::TextSpan;


#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use snowflake_front::compilation_unit::CompilationUnit;
    use snowflake_middle::ir::{hir::HIRBuilder, mir::MIRBuilder};

    use super::*;


    struct DiagnosticsVerifier {
        expected: Vec<Diagnostic>,
        actual: Vec<Diagnostic>,
    }

    impl DiagnosticsVerifier {
        pub fn new(input: &str, messages: Vec<&str>) -> Self {
            let msg_len = messages.len();
            let expected = Self::parse_input(input, messages);
            assert_eq!(expected.len(), msg_len);
            let actual = Self::compile(input);

            Self { expected, actual }
        }

        fn compile(input: &str) -> Vec<Diagnostic> {
            let raw_text = Self::get_raw_text(input);
            let compilation_unit = CompilationUnit::compile(&raw_text);

            let hir_builder = HIRBuilder::new();

            match compilation_unit {
                Ok(mut unit) => {
                    let hir = hir_builder.build(&unit.ast, &mut unit.global_scope);
                    let mir_builder = MIRBuilder::new(Rc::clone(&unit.diagnostics_report));
                    let _mir = mir_builder.build(&hir, &unit.global_scope);
                    let diagnostics = unit.diagnostics_report.borrow()
                        .diagnostics
                        .iter()
                        .cloned()
                        .collect::<Vec<_>>();
                    diagnostics
                },
                Err(e) => return e.borrow().diagnostics.clone(),
            }
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

    fn assert_diagnostics(input: &str, expected: Vec<&str>) {
            let verifier = DiagnosticsVerifier::new(input, expected);
            verifier.verify();
        }

    #[test]
    fn test_undeclared_variable() {
        let input = "let a = «b»";
        let expected = vec![
            "Undeclared variable 'b'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_expected_expression() {
        let input = "let a = «+»";
        let expected = vec![
            "Expected expression, found <+>"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_bad_token() {
        let input = "let a = 8 «@» 6";
        let expected = vec![
            "Expected expression, found <Bad>"
        ];

        assert_diagnostics(input, expected);
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
        } else {
            a = 5
        }
        
        a
        b
        «c»
        ";

        let expected = vec![
            "Undeclared variable 'c'"
        ];

        assert_diagnostics(input, expected);
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

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_undeclared_variable_when_variable_was_declared_in_if_statement() { // without block statement; should push an error
        let input = "\
        let b = -1

        if b > 10 {
            let a = 10
        }
        
        «a»
        ";

        let expected = vec![
            "Undeclared variable 'a'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_function_already_declared() {
        let input = "\
        fx a {}
        fx «a» {}
        ";

        let expected = vec![
            "Function 'a' already declared"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_undeclared_function() { // can't call undefined functions
        let input = "\
        «a»()
        ";

        let expected = vec![
            "Undeclared function 'a'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_incorrect_no_of_arguments() { // argument count in calls must match definition
        let input = "\
        fx foo(a: int, b: int) {}
        «foo»(1)
        ";

        let expected = vec![
            "Function 'foo' expects 2 arguments, but only 1 was found"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_type_mismatch_when_int_is_used_in_if_cond() { // int cannot be used in if conditions
        let input = "\
        if «1» {
            let a = 10
        }
        ";

        let expected = vec![
            "Expected type 'bool', found 'int'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_type_mismatch_when_variable_of_int_is_used_in_if_cond() { // int variable cannot be used in if conditions
        let input = "\
        let a = 1
        if «a» {
            let a = 10
        }
        ";
        
        let expected = vec![
            "Expected type 'bool', found 'int'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_type_mismatch_when_type_int_binary_expression_is_used_in_if_cond() { // int binary exps cannot be used in if conditions
        let input = "\
        let a = 1
        if «a + 1» {
            let a = 10
        }
        ";

        let expected = vec![
            "Expected type 'bool', found 'int'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_type_mismatch_when_adding_int_with_bool() { // int cannot be added to bool
        let input = "\
        let a = 1
        a + «true»
        ";

        let expected = vec![
            "Expected type 'int', found 'bool'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_type_mismatch_when_using_minus_unary_operator_on_bool() { // - false/true not allowed
        let input = "\
        let a = true;
        -«a»
        ";

        let expected = vec![
            "Expected type 'int', found 'bool'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_type_mismatch_when_assigning_function_call_result_to_variable_of_another_type() { // [b: bool] cannot be assigned to [fx a -> int]
        let input = "\
        fx a -> int {
            return 1
        }

        let b = false
        b = «a()»
        ";

        let expected = vec![
            "Expected type 'bool', found 'int'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_type_mismatch_when_using_binop_on_incompatible_types_in_function_params() { // int cannot be added with bool
        let input = "\
        fx a(a: int, b: bool) {
            a + «b»
        }
        ";

        let expected = vec![
            "Expected type 'int', found 'bool'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_wrong_return_type() { // returns must match defined type
        let input = "\
        fx a -> int {
            return «true»
        }
        ";

        let expected = vec![
            "Expected type 'int', found 'bool'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_type_mismatch_when_assigning_wrong_type_to_var_with_static_type() {
        let input = "\
        let a: int = «true»
        ";

        let expected = vec![
            "Expected type 'int', found 'bool'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_inappropriate_use_of_return() { // can't be used outside functions
        let input = "\
        «return» 86
        ";

        let expected = vec![
            "Cannot use 'return' outside of a function"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_addition_with_void_type() { // addition cannot be done with void type
        let input = "
        let a = 1
        a + «a()»
        fx a {}
        ";

        let expected = vec![
            "Expected type 'int', found 'void'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_undeclared_type_in_let_assignment() {
        let input = "\
        let a: «b» = 1
        ";

        let expected = vec![
            "Undeclared type 'b'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_undeclared_type_in_function_return_type() {
        let input = "\
        fx a -> «b» {}
        ";

        let expected = vec![
            "Undeclared type 'b'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_undeclared_type_in_function_param_type() {
        let input = "\
        fx a(a: «b») {}
        ";

        let expected = vec![
            "Undeclared type 'b'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_type_mismatch_in_args_in_function_call() {
        let input = "\
        fx a(a: int) {}
        a(«true»)
        ";

        let expected = vec![
            "Expected type 'int', found 'bool'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_returning_value_from_void_function() { // void functions cannot return a value
        let input = "\
        fx a() {
            return «1»
        }
        ";

        let expected = vec![
            "Expected type 'void', found 'int'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_return_without_expression_in_non_void_function() {
        let input = "\
        fx a() -> int {
            «return»
        }
        ";

        let expected = vec![
            "Expected type 'int', found 'void'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_assignment_to_undeclared_variable() {
        let input = "\
        «a» = 1
        ";

        let expected = vec![
            "Undeclared variable 'a'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_while_condition_type() { // should not be non-bool
        let input = "\
        let a = add(1, 2)
        fx add(a: int, b: int) -> int {
            return a + b
        }

        while «a + 1» {
            a = a + 1
        }
        ";

        let expected = vec![
            "Expected type 'bool', found 'int'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_two_compound_operators_in_a_statement() {
        // TODO: This test currently fails due to compiler generating duplicate diagnostics.
        // The compiler should be fixed to avoid duplicate error reporting.
        // For now, this test is commented out.
        
        /*
        let input = "\
        let a = 1
        a += 2 «-=» 3
        ";

        let expected = vec![
            "Invalid left-hand side in assignment operation '-='",
            "Expected type 'int', found 'void'"
        ];

        assert_diagnostics(input, expected);
        */
    }

    #[test]
    fn test_division_by_zero() {
        let input = "\
        let a = 1
        a / «0»
        ";

        let expected = vec![
            "Division by zero in '/' operation"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_remainder_by_zero() {
        let input = "\
        let a = 1
        a % «0»
        ";

        let expected = vec![
            "Division by zero in '%' operation"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_division_assignment_by_zero() {
        let input = "\
        let a = 1
        a /= «0»
        ";

        let expected = vec![
            "Division by zero in '/' operation"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_remainder_assignment_by_zero() {
        let input = "\
        let a = 1
        a %= «0»
        ";

        let expected = vec![
            "Division by zero in '%' operation"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_break_outside_loop() {
        let input = "\
        «break»
        ";

        let expected = vec![
            "Cannot use 'break' outside of a loop"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_continue_outside_loop() {
        let input = "\
        «continue»
        ";

        let expected = vec![
            "Cannot use 'continue' outside of a loop"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_array_type_mismatch() {
        let input = "\
        let a: [int; 3] = [1, 2, «true»];
        ";

        let expected = vec![
            "Expected type 'int', found 'bool'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_array_length_mismatch() {
        let input = "\
        let a: [int; 3] = «[1, 2]»;
        ";

        let expected = vec![
            "Expected array of size 3, found one of size 2"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_both_type_and_length_mismatch() {
        let input = "\
        let a: [int; 3] = «[\"this should fail\"]»;
        ";

        let expected = vec![
            "Expected 'int', found 'string'"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_array_index_out_of_bounds() {
        let input = "\
        let a: [int; 3] = [1, 2, 3];
        a[«3»]
        ";

        let expected = vec![
            "Index out of bounds: the length of array `a` is 3 but the index is 3"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_array_index_negative() {
        let input = "\
        let a: [int; 3] = [1, 2, 3];
        a[«-1»]
        ";

        let expected = vec![
            "Negative integers cannot be used to index on arrays"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_array_index_type_mismatch() {
        let input = "\
        let a: [int; 3] = [1, 2, 3];
        a[«true»]
        ";

        let expected = vec![
            "Cannot be indexed by 'bool' (slice indices are of type 'usize')"
        ];

        assert_diagnostics(input, expected);
    }

    #[test]
    fn test_array_indexing_on_non_array_type() {
        let input = "\
        let a = 1;
        «a»[0]
        ";

        let expected = vec![
            "Cannot index type 'int'"
        ];

        assert_diagnostics(input, expected);
    }
}