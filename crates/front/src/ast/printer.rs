use termion::color;
use termion::color::{Fg, Reset};
use crate::ast::*;


pub struct ASTPrinter {
    indent: usize,
    pub result: String,
}

impl ASTPrinter {
    const NUMBER_COLOUR: color::Cyan = color::Cyan;
    const TEXT_COLOUR: color::LightWhite = color::LightWhite;
    const KEYWORD_COLOUR: color::Magenta = color::Magenta;
    const VARIABLE_COLOUR: color::Green = color::Green;
    const BOOL_COLOUR: color::Yellow = color::Yellow;
    const TYPE_COLOUR: color::LightBlue = color::LightBlue;
    const STRING_COLOUR: color::LightGreen = color::LightGreen;
    const SIZE_COLOUR: color::Rgb = color::Rgb(255, 165, 0); // Orange

    pub fn new() -> Self {
        Self { indent: 0, result: String::new() }
    }

    fn add_whitespace(&mut self) {
        self.result.push_str(" ");
    }

    fn add_newline(&mut self) {
        self.result.push_str("\n");
    }

    fn add_keyword(&mut self, keyword: &str) {
        self.result.push_str(&format!("{}{}", Self::KEYWORD_COLOUR.fg_str(), keyword));
    }

    fn add_text(&mut self, text: &str) {
        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), text));
    }

    fn add_variable(&mut self, variable: &str) {
        self.result.push_str(&format!("{}{}", Self::VARIABLE_COLOUR.fg_str(), variable));
    }

    fn add_padding(&mut self) {
        for _ in 0..self.indent {
            self.result.push_str("    ");
        }
    }

    fn add_bool(&mut self, boolean: bool) {
        self.result.push_str(&format!("{}{}", Self::BOOL_COLOUR.fg_str(), boolean));
    }

    fn add_type(&mut self, type_: &str) {
        self.result.push_str(&format!("{}{}", Self::TYPE_COLOUR.fg_str(), type_));
    }

    fn add_size(&mut self, size: &str) {
        self.result.push_str(&format!("{}{}", Self::SIZE_COLOUR.fg_string(), size));
    }

    fn add_type_annot(&mut self, type_annotation: &StaticTypeAnnotation) {
        self.add_text(":");
        self.add_whitespace();
        self.add_type_kind(&type_annotation.type_kind);
    }

    fn add_type_kind(&mut self, type_kind: &TypeKind) {
        match type_kind {
            TypeKind::Simple { type_name } => {
                self.add_type(&type_name.span.literal);
            }
            TypeKind::Array { element_type, length, .. } => {
                self.add_text("[");
                self.add_type_kind(element_type);
                self.add_text("; ");
                self.add_size(&length.span.literal);
                self.add_text("]");
            }
            TypeKind::Slice { element_type, .. } => {
                self.add_text("[");
                self.add_type_kind(element_type);
                self.add_text("]");
            }
            TypeKind::Tuple { element_types, .. } => {
                self.add_text("(");
                for (i, elem_type) in element_types.iter().enumerate() {
                    self.add_type_kind(elem_type);

                    if i == 0 ||i != element_types.len() - 1 {
                        self.add_text(", ");
                    }
                }
                self.add_text(")");
            }
        }
    }
}

impl ASTVisitor for ASTPrinter {
    fn visit_statement(&mut self, ast: &mut Ast, statement: StatementId) {
        self.add_padding();
        Self::do_visit_statement(self, ast, statement);

        self.result.push_str(&format!("{}\n", Fg(Reset)));
    }

    fn visit_number_expression(&mut self, _ast: &mut Ast, number: &NumberExpression, _expr: &Expression) {
        self.result.push_str(&format!("{}{}", Self::NUMBER_COLOUR.fg_str(), number.number));
    }

    fn visit_float_expression(&mut self, _ast: &mut Ast, float: &FloatExpression, _expr: &Expression) {
        self.result.push_str(&format!("{}{}", Self::NUMBER_COLOUR.fg_str(), float.number));
    }

    fn visit_usize_expression(&mut self, _ast: &mut Ast, number: &UsizeExpression, _expr: &Expression) {
        self.result.push_str(&format!("{}{}", Self::NUMBER_COLOUR.fg_str(), number.number));
    }

    fn visit_string_expression(&mut self, _ast: &mut Ast, string: &StringExpression, _expr: &Expression) {
        self.result.push_str(&format!("{}\"{}\"", Self::STRING_COLOUR.fg_str(), string.string));
        self.result.push_str(&format!("{}", Fg(Reset)));
    }

    fn visit_binary_expression(&mut self, ast: &mut Ast, binary_expression: &BinaryExpression, _expr: &Expression) {
        self.visit_expression(ast, binary_expression.left);
        self.add_whitespace();

        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), 
                             binary_expression.operator.token.span.literal));
        self.add_whitespace();

        self.visit_expression(ast, binary_expression.right);
    }

    fn visit_unary_expression(&mut self, ast: &mut Ast, unary_expression: &UnaryExpression, _expr: &Expression) {
        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), unary_expression.operator.token.span.literal));

        self.visit_expression(ast, unary_expression.operand);
    }

    fn visit_parenthesised_expression(&mut self, ast: &mut Ast, parenthesised_expression: &ParenExpression, _expr: &Expression) {
        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), "("));

        self.visit_expression(ast, parenthesised_expression.expression);

        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), ")"));
    }

    fn visit_let_statement(&mut self, ast: &mut Ast, let_statement: &LetStatement, _statement: &Statement) {
        self.add_keyword("let"); // let keyword in magenta
        self.add_whitespace();

        match &let_statement.pattern.kind {
            PatternKind::Identifier(binding_mode, _) => {
                if let Mutability::Mutable = binding_mode.0 {
                    self.add_keyword("mut");
                    self.add_whitespace();
                }
            }
            _ => {}
        }

        self.add_text(let_statement.identifier.span.literal.as_str()); // variable name in white
        if let Some(type_annotation) = &let_statement.type_annotation {
            self.add_type_annot(type_annotation);
            self.add_whitespace();
        } else {
            self.add_whitespace();
        }

        self.add_text("="); // '=' in white
        self.add_whitespace();

        self.visit_expression(ast, let_statement.initialiser);
    }

    fn visit_variable_expression(&mut self, _ast: &mut Ast, variable_expression: &VarExpression, _expr: &Expression) {
        self.result.push_str(&format!("{}{}", Self::VARIABLE_COLOUR.fg_str(), variable_expression.identifier.span.literal));
    }

    fn visit_if_expression(&mut self, ast: &mut Ast, if_statement: &IfExpression, _expr: &Expression) {
        self.indent += 1;
        self.add_keyword("if");
        self.add_whitespace();

        self.add_text("(");
        self.visit_expression(ast, if_statement.condition);
        self.add_text(") {\n");

        for statement in &if_statement.then_branch.statements {
            self.visit_statement(ast, *statement);
        }

        self.indent -= 1;
        self.add_padding();
        self.add_text("}");
        self.indent += 1;

        if let Some(else_branch) = &if_statement.else_branch {
            self.add_whitespace();
            self.add_keyword("else");
            self.add_whitespace();
            self.add_text("{\n");

            for statement in else_branch.body.iter() {
                self.visit_statement(ast, *statement);
            }

            self.indent -= 1;
            self.add_padding();
            self.add_text("}\n");
            self.indent += 1;
        }
        self.indent -=1;
    }

    fn visit_assignment_expression(&mut self, ast: &mut Ast, assignment_expression: &AssignExpression, _expr: &Expression) {
        self.visit_expression(ast, assignment_expression.lhs);
        self.add_whitespace();

        self.add_text("=");
        self.add_whitespace();
        self.visit_expression(ast, assignment_expression.expression);
    }

    fn visit_block_expression(&mut self, ast: &mut Ast, block_statement: &BlockExpression, _expr: &Expression) {
        self.add_text("{");
        self.add_newline();
        self.indent += 1;

        for statement in &block_statement.statements {
            self.visit_statement(ast, *statement);
        }

        self.indent -= 1;
        self.add_padding();
        self.add_text("}");
    }

    fn visit_boolean_expression(&mut self, _ast: &mut Ast, boolean: &BoolExpression, _expr: &Expression) {
        self.add_bool(boolean.value);
    }

    fn visit_while_statement(&mut self, ast: &mut Ast, while_statement: &WhileStatement) {
        self.indent += 1;
        self.add_keyword("while");
        self.add_whitespace();

        self.add_text("(");
        self.visit_expression(ast, while_statement.condition);
        self.add_text(") {\n");

        self.visit_body(ast, &while_statement.body);
        self.indent -= 1;
        self.add_padding();
        self.add_text("}");
    }

    fn visit_error(&mut self, _ast: &mut Ast, span: &TextSpan) {
        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), span.literal));
    }

    fn visit_fx_decl(&mut self, ast: &mut Ast, fx_decl: &FxDeclaration, _item_id: ItemId) {
        self.indent += 1;
        self.add_keyword("fx");
        self.add_whitespace();
        self.add_text(&fx_decl.identifier.span.literal);

        let are_parameters_empty = fx_decl.parameters.is_empty();
        if !are_parameters_empty {
            self.add_text("(");
        } else {
            self.add_whitespace();
        }

        for (i, parameter) in fx_decl.parameters.iter().enumerate() {
            if i != 0 {
                self.add_text(",");
                self.add_whitespace();
            }

            self.add_text(&parameter.identifier.span.literal);
            self.add_type_annot(&parameter.type_annotation);
        }

        if !are_parameters_empty {
            self.add_text(")");
            self.add_whitespace();
        }

        self.add_text("{\n");
        for statement in fx_decl.body.iter() {
            self.visit_statement(ast, *statement);
        }
        self.add_text("}\n");
        self.add_newline();
        self.indent -= 1;
    }

    fn visit_return_statement(&mut self, ast: &mut Ast, return_statement: &ReturnStatement) {
        self.add_keyword("return");
        
        if let Some(expression) = &return_statement.return_value {
            self.add_whitespace();
            self.visit_expression(ast, *expression);
        }
    }

    fn visit_call_expression(&mut self, ast: &mut Ast, call_expression: &CallExpression, _expr: &Expression) {
        self.add_text(&call_expression.callee.span.literal);
        self.add_text("(");

        for (i, argument) in call_expression.arguments.iter().enumerate() {
            if i != 0 {
                self.add_text(",");
                self.add_whitespace();
            }

            self.visit_expression(ast, *argument);
        }

        self.add_text(")");
    }

    fn visit_break_expression(&mut self, _ast: &mut Ast, _break_expression: &BreakExpression, _expr: &Expression) {
        self.result.push_str(&format!("{}break{}", Self::TEXT_COLOUR.fg_str(), Fg(Reset)));
    }

    fn visit_continue_expression(&mut self, _ast: &mut Ast, _continue_expression: &ContinueExpression, _expr: &Expression) {
        self.result.push_str(&format!("{}continue{}", Self::TEXT_COLOUR.fg_str(), Fg(Reset)));
    }

    fn visit_array_expression(&mut self, ast: &mut Ast, array_expression: &ArrayExpression, _expr: &Expression) {
        self.add_text("[");
        for (i, element) in array_expression.elements.iter().enumerate() {
            if i != 0 {
                self.add_text(",");
                self.add_whitespace();
            }
            self.visit_expression(ast, *element);
        }
        self.add_text("]");
    }

    fn visit_index_expression(&mut self, ast: &mut Ast, index_expression: &IndexExpression, _expr: &Expression) {
        self.visit_expression(ast, index_expression.object);
        self.add_text("[");
        self.visit_expression(ast, index_expression.index.idx_no);
        self.add_text("]");
    }

    fn visit_tuple_expression(&mut self, ast: &mut Ast, tuple_expression: &TupleExpression, _expr: &Expression) {
        self.add_text("(");
        for (i, element) in tuple_expression.elements.iter().enumerate() {
            self.visit_expression(ast, *element);

            if i == 0 || i != tuple_expression.elements.len() - 1 {
                self.add_text(",");
                self.add_whitespace();
            }
        }
        self.add_text(")");
    }

    fn visit_tuple_index_expression(&mut self, ast: &mut Ast, tuple_index_expression: &TupleIndexExpression, _expr: &Expression) {
        self.visit_expression(ast, tuple_index_expression.tuple);
        self.add_text(".");
        self.visit_expression(ast, tuple_index_expression.index.idx_no);
    }
}