#[cfg(test)]
mod tests {
    use snowflake_front::ast::*;
    use snowflake_front::ast::visitor::ASTVisitor;
    use snowflake_front::compilation_unit::CompilationUnit;
    use snowflake_common::text::span::TextSpan;


    #[derive(Debug, PartialEq)]
    enum TestASTNode {
        Number(i64),
        Float(f64),
        Usize(usize),
        Boolean(bool),
        String(String),
        Binary,
        Unary,
        Parenthesised,
        Let,
        Assignment,
        Block,
        Variable(String),
        If,
        Else,
        While,
        Function,
        Return,
        Call,
        Break,
        Continue,
        Array,
        Index,
        Tuple,
        TupleIndex,
        Struct,
        StructExpression,
        Enum,
        Variant(String),
        Constant,
    }

    struct ASTVerifier {
        expected: Vec<TestASTNode>,
        actual: Vec<TestASTNode>,
        ast: Ast,
    }

    impl ASTVerifier {
        pub fn new(input: &str, expected: Vec<TestASTNode>) -> Self {
            let compilation_unit = CompilationUnit::compile(input).expect("Failed to compile");

            let mut verifier = ASTVerifier { expected, actual: Vec::new(), ast: compilation_unit.ast };
            verifier.flatten_ast();

            verifier
        }

        fn flatten_ast(&mut self) {
            self.actual.clear();
            let mut ast = self.ast.clone();

            ast.visit(&mut *self);
        }

        pub fn verify(&self) {
            // ensure the expected and actual AST nodes match
            assert_eq!(self.expected.len(), self.actual.len(), "Expected {} nodes, but got {}.\nActual nodes: {:?}", self.expected.len(), self.actual.len(), self.actual);

            for (index, (expected, actual)) in self.expected.iter().zip(self.actual.iter()).enumerate() {
                assert_eq!(expected, actual, "Expected {:?} at index {}, but got {:?}", expected, index, actual);
            }
        }
    }

    impl ASTVisitor for ASTVerifier {
        fn visit_let_statement(&mut self, ast: &mut Ast, let_statement: &LetStatement, _statement: &Statement) {
            self.actual.push(TestASTNode::Let);
            self.visit_expression(ast, let_statement.initialiser);
        }

        fn visit_variable_expression(&mut self, _ast: &mut Ast, variable_expression: &VarExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Variable(variable_expression.identifier().to_string()));
        }

        fn visit_number_expression(&mut self, _ast: &mut Ast, number: &NumberExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Number(number.number));
        }

        fn visit_float_expression(&mut self, _ast: &mut Ast, float: &FloatExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Float(float.number));
        }

        fn visit_usize_expression(&mut self, _ast: &mut Ast, usize_expression: &UsizeExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Usize(usize_expression.number));
        }

        fn visit_string_expression(&mut self, _ast: &mut Ast, string: &StringExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::String(string.string.clone()));
        }

        fn visit_error(&mut self, _ast: &mut Ast, _span: &TextSpan) {
            // do nothing
        }

        fn visit_parenthesised_expression(&mut self, ast: &mut Ast, parenthesised_expression: &ParenExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Parenthesised);
            self.visit_expression(ast, parenthesised_expression.expression);
        }

        fn visit_binary_expression(&mut self, ast: &mut Ast, binary_expression: &BinaryExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Binary);
            self.visit_expression(ast, binary_expression.left);
            self.visit_expression(ast, binary_expression.right);
        }

        fn visit_unary_expression(&mut self, ast: &mut Ast, unary_expression: &UnaryExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Unary);
            self.visit_expression(ast, unary_expression.operand);
        }

        fn visit_if_expression(&mut self, ast: &mut Ast, if_statement: &IfExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::If);
            self.visit_expression(ast, if_statement.condition);
            self.visit_body(ast, &if_statement.then_branch);

            if let Some(else_branch) = &if_statement.else_branch {
                self.actual.push(TestASTNode::Else);
                
                self.visit_body(ast, &else_branch.body);
            }
        }

        fn visit_boolean_expression(&mut self, _ast: &mut Ast, boolean: &BoolExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Boolean(boolean.value));
        }

        fn visit_block_expression(&mut self, ast: &mut Ast, block_statement: &BlockExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Block);

            for statement in &block_statement.statements {
                self.visit_statement(ast, *statement);
            }
        }

        fn visit_assignment_expression(&mut self, ast: &mut Ast, assignment_expression: &AssignExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Assignment);
            self.visit_expression(ast, assignment_expression.expression);
        }

        fn visit_while_expression(&mut self, ast: &mut Ast, while_statement: &WhileExpression) {
            self.actual.push(TestASTNode::While);
            self.visit_expression(ast, while_statement.condition);
            self.visit_body(ast, &while_statement.body);
        }

        fn visit_fx_decl(&mut self, ast: &mut Ast, fx_decl: &FxDeclaration, _item_id: ItemIndex) {
            self.actual.push(TestASTNode::Function);
            for statement in fx_decl.body.iter() {
                self.visit_statement(ast, *statement);
            }
        }

        fn visit_return_statement(&mut self, ast: &mut Ast, return_statement: &ReturnStatement) {
            self.actual.push(TestASTNode::Return);
            if let Some(expression) = &return_statement.return_value {
                self.visit_expression(ast, *expression);
            }
        }

        fn visit_call_expression(&mut self, ast: &mut Ast, call_expression: &CallExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Call);
            for argument in &call_expression.arguments {
                self.visit_expression(ast, *argument);
            }
        }

        fn visit_break_expression(&mut self, _ast: &mut Ast, _break_expression: &BreakExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Break);
        }

        fn visit_continue_expression(&mut self, _ast: &mut Ast, _continue_expression: &ContinueExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Continue);
        }

        fn visit_array_expression(&mut self, ast: &mut Ast, array_expression: &ArrayExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Array);
            for element in &array_expression.elements {
                self.visit_expression(ast, *element);
            }
        }

        fn visit_index_expression(&mut self, ast: &mut Ast, index_expression: &IndexExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Index);
            self.visit_expression(ast, index_expression.object);
            self.visit_expression(ast, index_expression.index.idx_no);
        }

        fn visit_tuple_expression(&mut self, ast: &mut Ast, tuple_expression: &TupleExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Tuple); // represent tuple with parenthesis
            for element in &tuple_expression.elements {
                self.visit_expression(ast, *element);
            }
        }

        fn visit_field_expression(&mut self, ast: &mut Ast, field_expression: &FieldExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::TupleIndex);
            self.visit_expression(ast, field_expression.object);
            self.visit_expression(ast, field_expression.field.idx_no);
        }

        fn visit_constant_item(&mut self, _ast: &mut Ast, _constant_item: &ConstantItem, _item_id: ItemIndex) {
            self.actual.push(TestASTNode::Constant);
        }

        fn visit_struct_expression(&mut self, _ast: &mut Ast, _struct_expression: &StructExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::StructExpression);
        }

        fn visit_struct_item(&mut self, _ast: &mut Ast, _generics: &Generics, _variant_data: &VariantData, _item_id: ItemIndex) {
            self.actual.push(TestASTNode::Struct);
        }

        fn visit_enum_item(&mut self, _ast: &mut Ast, _generics: &Generics, enum_definition: &EnumDefinition, _item_id: ItemIndex) {
            self.actual.push(TestASTNode::Enum);
            for variant in &enum_definition.variants {
                self.actual.push(TestASTNode::Variant(variant.identifier.span.literal.clone()));
            }
        }

        fn visit_path_expression(&mut self, _ast: &mut Ast, path_expression: &PathExpression, _expr: &Expression) {
            self.actual.push(TestASTNode::Variable(path_expression.path.span.literal.clone()));
        }
    }

    fn assert_tree(input: &str, expected: Vec<TestASTNode>) {
        let verifier = ASTVerifier::new(input, expected);
        verifier.verify();
    }

    #[test]
    pub fn test_string_literal() {
        let input = r#"
            fx main() {
                let message = "hello world"
            }
        "#;

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::String("hello world".to_string()),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_string_literal_with_escapes() {
        let input = r#"
            fx main() {
                let message = "hello\nworld\t!"
            }
        "#;

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::String("hello\nworld\t!".to_string()),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_basic_binary_expression() {
        let input = "
            fx main() {
                let a = 1 + 2
            }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Number(1),
            TestASTNode::Number(2),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_parenthesised_binary_expression() {
        let input = "
            fx main() {
                let a = (6 + 9) * 42
            }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Parenthesised,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
            TestASTNode::Number(42),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_parenthesised_binary_expression_with_variable() {
        let input = "
            fx main() {
                let b = 2
                let a = (6 + 9) * b
            }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Number(2),
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Parenthesised,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
            TestASTNode::Variable("b".to_string()),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_nested_parenthesised_binary_expression() {
        let input = "
            fx main() {
                let b = 1
                let c = 2
                let a = (b + (c * 2)) / 3
            }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Number(1),
            TestASTNode::Let,
            TestASTNode::Number(2),
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Parenthesised,
            TestASTNode::Binary,
            TestASTNode::Variable("b".to_string()),
            TestASTNode::Parenthesised,
            TestASTNode::Binary,
            TestASTNode::Variable("c".to_string()),
            TestASTNode::Number(2),
            TestASTNode::Number(3),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_parenthesised_binary_expression_with_variable_and_number() {
        let input = "
        fx main() {
            let b = 1
            let a = (6 + 9) * b + 42
        }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Number(1),
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Binary,
            TestASTNode::Parenthesised,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
            TestASTNode::Variable("b".to_string()),
            TestASTNode::Number(42),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_bitwise_and() {
        let input = "
            fx main() {
                let a = 6 & 9
            }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_bitwise_or() {
        let input = "
            fx main() {
                let a = 6 | 9
            }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_bitwise_xor() {
        let input = "
            fx main() {
                let a = 6 ^ 9
            }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Number(6),
            TestASTNode::Number(9),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_bitwise_not() {
        let input = "
            fx main() {
                let a = ~1
            }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Unary,
            TestASTNode::Number(1),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_negation() {
        let input = "
            fx main() {
                let a = -1
            }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Unary,
            TestASTNode::Number(1),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_power() {
        let input = "
            fx main() {
                let a = 2 ** 3
            }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Number(2),
            TestASTNode::Number(3),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_loooong_unary_exps() {
        let input = "
            fx main() {
                let a = -1 + -2 * -3 ** ------4
            }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Unary,
            TestASTNode::Number(1),
            TestASTNode::Binary,
            TestASTNode::Unary,
            TestASTNode::Number(2),
            TestASTNode::Binary,
            TestASTNode::Unary,
            TestASTNode::Number(3),
            TestASTNode::Unary,
            TestASTNode::Unary,
            TestASTNode::Unary,
            TestASTNode::Unary,
            TestASTNode::Unary,
            TestASTNode::Unary,
            TestASTNode::Number(4),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_if_statement() {
        let input = "\
        fx main() {
            let a = 1
            
            if a > 0 {
                a = 86
            }
        }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Number(1),
            TestASTNode::If,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Number(0),
            TestASTNode::Assignment,
            TestASTNode::Number(86),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_if_else_statement() {
        let input = "\
        fx main() {
            let a = 1
            
            if a > 0 {
                a = 86
            } else {
                a = 23
            }
        }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Number(1),
            TestASTNode::If,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Number(0),
            TestASTNode::Assignment,
            TestASTNode::Number(86),
            TestASTNode::Else,
            TestASTNode::Assignment,
            TestASTNode::Number(23),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_while_statement() {
        let input = "\
        fx main() {
            let a = 1

            while a < 10 {
                a = a + 1
            }
        }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Number(1),
            TestASTNode::While,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Number(10),
            TestASTNode::Assignment,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Number(1),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_function_declaration() { // parses function declaration properly
        let input = "\
        fx add(a: int, b: int) -> int {
            return a + b
        }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Return,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Variable("b".to_string()),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_call_expression() { // parses call expressions properly
        let input = "\
        fx add(a: int, b: int) -> int {
            return a + b
        }

        fx main() {
            add(2 * 3, 4 + 5)
        }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Return,
            TestASTNode::Binary,
            TestASTNode::Variable("a".to_string()),
            TestASTNode::Variable("b".to_string()),
            TestASTNode::Function,
            TestASTNode::Call,
            TestASTNode::Binary,
            TestASTNode::Number(2),
            TestASTNode::Number(3),
            TestASTNode::Binary,
            TestASTNode::Number(4),
            TestASTNode::Number(5),
        ];

        assert_tree(input, expected);
    }

    #[test]
    pub fn test_shift_operator_precedence() {
        let input = "
        fx main() {
            let a = 8 << 2
        }
        ";

        let expected = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Number(8),
            TestASTNode::Number(2),
        ];

        assert_tree(input, expected);

        let input2 = "
        fx main() {
            let b = 4 << 1 & 2
        }
        ";

        let expected2 = vec![
            TestASTNode::Function,
            TestASTNode::Let,
            TestASTNode::Binary,
            TestASTNode::Binary,
            TestASTNode::Number(4),
            TestASTNode::Number(1),
            TestASTNode::Number(2),
        ];

        assert_tree(input2, expected2);
    }
}