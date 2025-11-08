use std::path;

use termion::color;
use termion::color::{Fg, Reset};
use crate::ast::*;


pub struct ASTPrinter {
    indent: usize,
    pub result: String,
    is_visiting_top_level: bool,
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
        Self { indent: 0, result: String::new(), is_visiting_top_level: true }
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
        self.result.push_str(&format!("{}{}{}", Self::BOOL_COLOUR.fg_str(), boolean, Fg(Reset)));
    }

    fn add_type(&mut self, type_: &str) {
        self.result.push_str(&format!("{}{}{}", Self::TYPE_COLOUR.fg_str(), type_, Fg(Reset)));
    }

    fn add_size(&mut self, size: &str) {
        self.result.push_str(&format!("{}{}{}", Self::SIZE_COLOUR.fg_string(), size, Fg(Reset)));
    }

    fn add_type_annot(&mut self, type_annotation: &StaticTypeAnnotation) {
        self.add_text(":");
        self.add_whitespace();
        self.add_type_kind(&type_annotation.type_kind);
    }

    fn add_type_kind(&mut self, type_kind: &AstType) {
        match type_kind {
            AstType::Simple { type_name } => {
                self.add_type(&type_name.span.literal);
            }
            AstType::Array { element_type, length, .. } => {
                self.add_text("[");
                self.add_type_kind(element_type);
                self.add_text("; ");
                self.add_size(&length.span.literal);
                self.add_text("]");
            }
            AstType::Slice { element_type, .. } => {
                self.add_text("[");
                self.add_type_kind(element_type);
                self.add_text("]");
            }
            AstType::Tuple { element_types, .. } => {
                self.add_text("(");
                for (i, elem_type) in element_types.iter().enumerate() {
                    self.add_type_kind(elem_type);

                    if i == 0 ||i != element_types.len() - 1 {
                        self.add_text(", ");
                    }
                }
                self.add_text(")");
            }
            AstType::Path(_, path) => {
                for (i, segment) in path.segments.iter().enumerate() {
                    if i > 0 {
                        self.add_text("::");
                    }
                    self.add_type(&segment.identifier.span.literal);
                }
            }
            AstType::ImplTrait(_, _) => {
                self.add_keyword("impl");
                self.add_whitespace();
                self.add_text("Trait");
            }
        }
    }
    
    fn add_variant_data(&mut self, variant_data: &VariantData) {
        match variant_data {
            VariantData::Struct{ fields } => {
                self.add_text(" {\n");
                self.indent += 1;
    
                for field in fields {
                    self.add_padding();
                    if let Some(identifier) = &field.identifier {
                        self.add_text(&identifier.span.literal);
                        self.add_text(": ");
                        self.add_type_kind(&field.ty);
                        self.result.push_str(&format!(",\n"));
                    } else {
                        // Tuple struct field
                        self.add_type_kind(&field.ty);
                        self.result.push_str(&format!(",\n"));
                    }
                }
    
                self.indent -= 1;
                self.add_padding();
                self.add_text("}");
            }
            VariantData::Tuple(fields) => {
                self.add_text("(");
    
                for field in fields {
                    if let Some(identifier) = &field.identifier {
                        self.add_text(&identifier.span.literal);
                    } else {
                        // Tuple struct field
                        self.add_type_kind(&field.ty);
                    }
    
                    if field != fields.last().unwrap() {
                        self.add_text(",");
                        self.add_whitespace();
                    }
                }
    
                self.add_text(");");
            }
            VariantData::Unit => self.add_text(";"),
        }
    }

    fn print_pattern(&mut self, pattern: &Pattern) {
        match &pattern.kind {
            PatternKind::Identifier(binding_mode, token) => {
                if let Mutability::Mutable = binding_mode.0 {
                    self.add_keyword("mut");
                    self.add_whitespace();
                }
                self.add_variable(&token.span.literal);
            }
            PatternKind::Wildcard => self.add_text("_"),
            PatternKind::Tuple(fields) => {
                self.add_text("(");
                for (i, field) in fields.iter().enumerate() {
                    self.print_pattern(field);

                    if i != fields.len() - 1 {
                        self.add_text(",");
                        self.add_whitespace();
                    }
                }
                self.add_text(")");
            }
            PatternKind::Struct(_, path, fields) => {
                self.add_text(&path.span.literal);
                self.add_text(" { ");
                for (i, field) in fields.iter().enumerate() {
                    self.print_pattern(&field.pattern);

                    if i != fields.len() - 1 {
                        self.add_text(",");
                        self.add_whitespace();
                    }
                }
                self.add_text(" }");
            }
            PatternKind::TupleStruct(_, path, fields) => {
                self.add_text(&path.span.literal);
                self.add_text("(");
                for (i, field) in fields.iter().enumerate() {
                    self.print_pattern(field);

                    if i != fields.len() - 1 {
                        self.add_text(",");
                        self.add_whitespace();
                    }
                }
                self.add_text(")");
            }
            PatternKind::Rest => self.add_text(".."),
            _ => {}
        }
    }
}

impl ASTVisitor for ASTPrinter {
    fn visit_item(&mut self, ast: &mut Ast, item: ItemIndex) {
        let item_ref = ast.query_item(item);
        if self.is_visiting_top_level && item_ref.is_local {
            return;
        }
        self.visit_item_default(ast, item);
        self.add_newline();
    }

    fn visit_statement(&mut self, ast: &mut Ast, statement: StmtIndex) {
        self.add_padding();
        let was_top_level = self.is_visiting_top_level;
        self.is_visiting_top_level = false;
        
        Self::do_visit_statement(self, ast, statement);
        
        self.is_visiting_top_level = was_top_level;

        match &ast.query_statement(statement).kind {
            StatementKind::SemiExpression(_) => self.add_text(";"),
            _ => {}
        }
        self.result.push_str(&format!("{}\n", Fg(Reset)));
    }

    fn visit_let_statement(&mut self, ast: &mut Ast, let_statement: &LetStatement, _statement: &Statement) {
        self.add_keyword("let"); // let keyword in magenta
        self.add_whitespace();
        self.print_pattern(&let_statement.pattern);

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

    fn visit_const_statement(&mut self, ast: &mut Ast, const_statement: &ConstStatement, _statement: &Statement) {
        self.add_keyword("const"); // const keyword in magenta
        self.add_whitespace();

        self.add_text(&const_statement.identifier.span.literal); // variable name in white
        self.add_type_annot(&const_statement.type_annotation);
        self.add_whitespace();

        self.add_text("="); // '=' in white
        self.add_whitespace();

        self.visit_expression(ast, const_statement.expr);
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

    fn visit_if_expression(&mut self, ast: &mut Ast, if_statement: &IfExpression, _expr: &Expression) {
        self.indent += 1;
        self.add_keyword("if");
        self.add_whitespace();

        self.visit_expression(ast, if_statement.condition);
        self.add_text(" {\n");

        for statement in &if_statement.then_branch.statements {
            self.visit_statement(ast, *statement);
        }

        self.indent -= 1;
        self.add_padding();
        self.add_text("}");

        if let Some(else_branch) = &if_statement.else_branch {
            self.add_whitespace();
            self.add_keyword("else");
            self.add_whitespace();

            self.visit_expression(ast, *else_branch);
        }
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

    fn visit_while_expression(&mut self, ast: &mut Ast, while_statement: &WhileExpression, expr: &Expression) {
        self.indent += 1;
        self.add_keyword("while");
        self.add_whitespace();

        self.add_text("(");
        self.visit_expression(ast, while_statement.condition);
        self.add_text(") {\n");

        self.visit_block_expression(ast, &while_statement.body, expr);
        self.indent -= 1;
        self.add_padding();
        self.add_text("}");
    }

    fn visit_error(&mut self, _ast: &mut Ast, span: &TextSpan) {
        self.result.push_str(&format!("{}{}", Self::TEXT_COLOUR.fg_str(), span.literal));
    }

    fn visit_return_expression(&mut self, ast: &mut Ast, return_expression: &ReturnExpression, _expr: &Expression) {
        self.add_keyword("return");

        if let Some(expression) = &return_expression.return_value {
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

    fn visit_method_call_expression(&mut self, ast: &mut Ast, method_call: &MethodCallExpression, _expr: &Expression) {
        self.visit_expression(ast, method_call.receiver);
        self.add_text(".");
        self.add_text(&method_call.method_name.span.literal);
        self.add_text("(");

        for (i, argument) in method_call.arguments.iter().enumerate() {
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

    fn visit_field_expression(&mut self, ast: &mut Ast, field_expression: &FieldExpression, _expr: &Expression) {
        self.visit_expression(ast, field_expression.object);
        self.add_text(".");
        self.visit_expression(ast, field_expression.field.idx_no);
    }

    fn visit_struct_expression(&mut self, ast: &mut Ast, struct_expression: &StructExpression, _expr: &Expression) {
        self.add_text(&struct_expression.path.span.literal);
        self.add_text(" { ");

        for (i, field) in struct_expression.fields.iter().enumerate() {
            if field.is_shorthand {
                self.add_text(&field.expr.span.literal);
            } else {
                self.add_text(&field.identifier.span.literal);
                self.add_text(": ");
                self.visit_expression(ast, field.expr.id);
            }

            if i != struct_expression.fields.len() - 1 {
                self.add_text(",");
                self.add_whitespace();
            }
        }

        self.add_text(" }");
    }

    fn visit_path_expression(&mut self, _ast: &mut Ast, path_expression: &PathExpression, _expr: &Expression) {
        self.add_variable(&path_expression.path.span.literal);
    }

    fn visit_item_default(&mut self, ast: &mut Ast, item: ItemIndex) {
        let item = ast.query_item(item).clone();

        match &item.kind {
            ItemKind::Function(fx_decl) => {
                self.visit_fx_decl(ast, fx_decl, item.id);
            }
            ItemKind::Const(constant_item) => {
                self.visit_constant_item(ast, constant_item, item.id);
            }
            ItemKind::Struct(identifier, generics, variant_data) => {
                self.add_keyword("struct");
                self.add_whitespace();
                self.add_type(&identifier.span.literal);

                self.visit_struct_item(ast, generics, variant_data, item.id);
            }
            ItemKind::Enum(identifier, generics, enum_definition) => {
                self.add_keyword("enum");
                self.add_whitespace();
                self.add_type(&identifier.span.literal);

                self.visit_enum_item(ast, generics, enum_definition, item.id);
            }
            ItemKind::Impl(impl_block) => {
                self.visit_impl_item(ast, impl_block, item.id);
            }
        }
    }

    fn visit_fx_decl(&mut self, ast: &mut Ast, fx_decl: &FxDeclaration, _item_id: ItemIndex) {
        self.indent += 1;
        self.add_keyword("fx");
        self.add_whitespace();
        self.add_text(&fx_decl.identifier.span.literal);

        self.add_text("(");
        
        let mut has_printed_param = false;
        
        if let Some(ref self_param) = fx_decl.self_param {
            if self_param.mutability == Mutability::Mutable {
                self.add_keyword("mut");
                self.add_whitespace();
            }
            self.add_keyword("self");
            has_printed_param = true;
        }

        for (i, parameter) in fx_decl.generics.iter().enumerate() {
            if has_printed_param || i > 0 {
                self.add_text(",");
                self.add_whitespace();
            }

            self.add_text(&parameter.identifier.span.literal);
            match &parameter.kind {
                crate::ast::GenericParamKind::Const { ty, .. } => {
                    self.add_text(": ");
                    self.add_type_kind(ty);
                }
                crate::ast::GenericParamKind::Type { ty, .. } => {
                    self.add_text(": ");
                    self.add_type_kind(ty);
                }
            }
            has_printed_param = true;
        }

        self.add_text(")");
        
        // Print return type if it exists
        if let Some(ref return_type) = fx_decl.return_type {
            self.add_whitespace();
            self.add_text("->");
            self.add_whitespace();
            self.add_type_kind(&return_type.ty);
        }
        
        self.add_whitespace();
        self.add_text("{\n");
        for statement in fx_decl.body.statements.iter() {
            self.visit_statement(ast, *statement);
        }
        self.indent -= 1;
        self.add_padding();
        self.add_text("}");
        self.add_newline();
    }

    fn visit_constant_item(&mut self, ast: &mut Ast, constant_item: &ConstantItem, _item_id: ItemIndex) {
        self.add_keyword("const");
        self.add_whitespace();

        self.add_text(&constant_item.identifier.span.literal);
        self.add_type_annot(&constant_item.type_annotation);
        self.add_whitespace();

        self.add_text("=");
        self.add_whitespace();

        if let Some(expr) = &constant_item.expr {
            self.visit_expression(ast, **expr);
        }
        self.result.push_str(&format!("{}\n", Fg(Reset)));
    }

    fn visit_struct_item(&mut self, _ast: &mut Ast, generics: &Generics, variant_data: &VariantData, _item_id: ItemIndex) {
        if !generics.params.is_empty() {
            self.add_text("<");

            for (i, param) in generics.params.iter().enumerate() {
                self.add_text(&param.identifier.span.literal);
                if i < generics.params.len() - 1 {
                    self.add_text(", ");
                }
            }

            self.add_text(">");
        }
        
        self.add_variant_data(variant_data);
        self.add_text("\n");
    }

    fn visit_enum_item(&mut self, _ast: &mut Ast, generics: &Generics, enum_definition: &EnumDefinition, _item_id: ItemIndex) {
        if !generics.params.is_empty() {
            self.add_text("<");

            for (i, param) in generics.params.iter().enumerate() {
                self.add_text(&param.identifier.span.literal);
                if i < generics.params.len() - 1 {
                    self.add_text(", ");
                }
            }

            self.add_text(">");
        }

        self.add_text(" {\n");
        self.indent += 1;

        for variant in &enum_definition.variants {
            self.add_padding();
            self.add_text(&variant.identifier.span.literal);
            self.add_variant_data(&variant.data);
            self.add_text(",\n");
        }

        self.indent -= 1;
        self.add_padding();
        self.add_text("}\n");
    }

    fn visit_impl_item(&mut self, ast: &mut Ast, impl_item: &Impl, _item_id: ItemIndex) {
        self.add_keyword("impl");
        self.add_whitespace();
        self.add_type_kind(&impl_item.self_type);
        self.add_whitespace();
        self.add_text("{\n");
        self.indent += 1;

        for item in &impl_item.items {
            self.add_padding();
            match &item.kind {
                AssociatedItemKind::Function(decl) => {
                    self.visit_fx_decl(ast, &decl, item.id);
                }
                AssociatedItemKind::Const(decl) => {
                    self.visit_constant_item(ast, &decl, item.id);
                }
            }
        }

        self.indent -= 1;
        self.add_text("}\n");
    }
}