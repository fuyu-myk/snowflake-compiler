use std::io::Write;

use anyhow::Result;
use snowflake_common::Idx;
use snowflake_front::{ast::{AstType, ItemKind, VariantData}, compilation_unit::GlobalScope};

use crate::ir::hir::{HIR, HIRExprKind, HIRExpression, HIRItemId, HIRItemKind, HIRStatement, HIRStmtKind, HIRStructTailExpr, QualifiedPath};


const INDENT: &str = "    ";

pub struct HIRWriter<W> {
    _phantom: std::marker::PhantomData<W>,
}

impl <W> HIRWriter<W> where W: Write {
    pub fn write(writer: &mut W, hir: &HIR, global_scope: &GlobalScope, indent: usize) -> Result<()> {
        for (_, statements) in &hir.top_statements {
            for stmt in statements {
                Self::write_statement(writer, stmt, hir, global_scope, indent)?;
            }
        }
        for (fx_idx, body) in &hir.functions {
            // Check if this function exists in global scope (skip synthetic functions)
            let fx_opt = global_scope.functions.indexed_iter()
                .find(|(idx, _)| *idx == *fx_idx)
                .map(|(_, fx)| fx);
            
            if let Some(fx) = fx_opt {
                if fx.name.contains("::") {
                    continue;
                }
                
                // Regular function with declaration
                write!(writer, "fx {}(", fx.name)?;

                for param_id in fx.parameters.iter() {
                    let param = global_scope.variables.get(*param_id);
                    write!(writer, "{}: {}", param.name.tokens.last().unwrap().span.literal, param.ty)?;
                    
                    if param_id.as_index() != fx.parameters.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }
                writeln!(writer, ") -> {} {{", fx.return_type)?;
            } else {
                // Synthetic function (e.g., global init), handle it specially
                writeln!(writer, "// Global initialization statements")?;
            }

            for statement in body {
                Self::write_indent(writer, indent + 1)?;
                Self::write_statement(writer, statement, hir, global_scope, indent + 1)?;
            }
            
            if fx_opt.is_some() {
                writeln!(writer, "}}\n")?;
            } else {
                writeln!(writer)?;
            }
        }

        Ok(())
    }

    fn write_statement(writer: &mut W, statement: &HIRStatement, hir: &HIR, global_scope: &GlobalScope, indent: usize) -> Result<()> {
        match &statement.kind {
            HIRStmtKind::Expression { expr } => {
                Self::write_expression(writer, expr, hir, global_scope, indent)?;
                write!(writer, ";")?;
                writeln!(writer)?;
            }
            HIRStmtKind::TailExpression { expr } => {
                Self::write_expression(writer, expr, hir, global_scope, indent)?;
                writeln!(writer)?;
            }
            HIRStmtKind::Declaration { var_idx, init_expr, is_mutable } => {
                let var = &global_scope.variables[*var_idx];
                let mut_keyword = if *is_mutable { "mut " } else { "" };
                write!(writer, "let {}{}: {}", mut_keyword, var.name.tokens.last().unwrap().span.literal, var.ty)?;

                if let Some(init) = init_expr {
                    write!(writer, " = ")?;
                    Self::write_expression(writer, init, hir, global_scope, indent)?;
                }

                writeln!(writer)?;
            }
            HIRStmtKind::Const { var_idx, init_expr } => {
                let var = &global_scope.variables[*var_idx];
                write!(writer, "const {}: {}", var.name.tokens.last().unwrap().span.literal, var.ty)?;

                if let Some(init) = init_expr {
                    write!(writer, " = ")?;
                    Self::write_expression(writer, init, hir, global_scope, indent)?;
                }

                writeln!(writer)?;
            }
            HIRStmtKind::Assignment { target, value } => {
                // Handle different types of assignment targets
                match &target.kind {
                    HIRExprKind::Var { var_idx } => {
                        let var = &global_scope.variables[*var_idx];
                        write!(writer, "{} = ", var.name.tokens.last().unwrap().span.literal)?;
                    }
                    _ => {
                        Self::write_expression(writer, target, hir, global_scope, indent)?;
                        write!(writer, " = ")?;
                    }
                }

                Self::write_expression(writer, value, hir, global_scope, indent)?;
                writeln!(writer)?;
            }
            HIRStmtKind::Item { item_id } => {
                Self::write_item(writer, item_id, hir, global_scope, indent)?;
            }
        }
        Ok(())
    }

    fn write_expression(writer: &mut W, expression: &HIRExpression, hir: &HIR, global_scope: &GlobalScope, indent: usize) -> Result<()> {
        match &expression.kind {
            HIRExprKind::Number(number) => {
                write!(writer, "{}", number)?;
            }
            HIRExprKind::Float(float) => {
                write!(writer, "{}", float)?;
            }
            HIRExprKind::Usize(number) => {
                write!(writer, "{}", number)?;
            }
            HIRExprKind::String(string) => {
                write!(writer, "\"{}\"", string)?;
            }
            HIRExprKind::Bool(bool) => {
                write!(writer, "{}", bool)?;
            }
            HIRExprKind::Unit => {
                write!(writer, "()")?;
            }
            HIRExprKind::Var { var_idx } => {
                let var = &global_scope.variables[*var_idx];
                write!(writer, "{}", var.name.tokens.last().unwrap().span.literal)?;
            }
            HIRExprKind::Array { elements, element_type: _, alloc_type: _ } => {
                write!(writer, "[")?;
                for (i, elem) in elements.iter().enumerate() {
                    Self::write_expression(writer, elem, hir, global_scope, indent)?;
                    if i != elements.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }
                write!(writer, "]")?;
            }
            HIRExprKind::Index { object, index, bounds_check: _, length: _ } => {
                Self::write_expression(writer, object, hir, global_scope, indent)?;
                write!(writer, "[")?;
                Self::write_expression(writer, index, hir, global_scope, indent)?;
                write!(writer, "]")?;
            }
            HIRExprKind::Tuple { elements, .. } => {
                write!(writer, "(")?;
                for (i, elem) in elements.iter().enumerate() {
                    Self::write_expression(writer, elem, hir, global_scope, indent)?;
                    if i == 0 || i != elements.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }
                write!(writer, ")")?;
            }
            HIRExprKind::Field { object: tuple, field: index } => {
                Self::write_expression(writer, tuple, hir, global_scope, indent)?;
                write!(writer, ".")?;
                Self::write_expression(writer, index, hir, global_scope, indent)?;
            }
            HIRExprKind::Struct { path, fields, tail_expr } => {
                let (struct_name, is_tuple_struct) = if let QualifiedPath::ResolvedType(struct_idx) = path {
                    let struct_item = global_scope.structs.get(*struct_idx);
                    if let ItemKind::Struct(name_token, _, variant_data) = &struct_item.kind {
                        let is_tuple = matches!(variant_data, VariantData::Tuple(_));
                        (name_token.span.literal.clone(), is_tuple)
                    } else {
                        (String::from("UnknownStruct"), false)
                    }
                } else {
                    (String::from("UnknownPath"), false)
                };
                
                if is_tuple_struct {
                    write!(writer, "{}(", struct_name)?;
                    for (i, field) in fields.iter().enumerate() {
                        Self::write_expression(writer, &field.expr, hir, global_scope, indent)?;
                        if i != fields.len() - 1 {
                            write!(writer, ", ")?;
                        }
                    }
                    write!(writer, ")")?;
                } else {
                    write!(writer, "{} {{ ", struct_name)?;
                    for (i, field) in fields.iter().enumerate() {
                        if field.is_shorthand {
                            write!(writer, "{}", field.identifier.span.literal)?;
                        } else {
                            write!(writer, "{}: ", field.identifier.span.literal)?;
                            Self::write_expression(writer, &field.expr, hir, global_scope, indent)?;
                        }
                        
                        if i != fields.len() - 1 || !matches!(tail_expr, HIRStructTailExpr::None) {
                            write!(writer, ", ")?;
                        }
                    }
                    match tail_expr {
                        HIRStructTailExpr::None => {}
                        HIRStructTailExpr::Default(_) => {
                            write!(writer, "..")?;
                        }
                    }
                    write!(writer, " }}")?;
                }
            }
            HIRExprKind::Binary { operator, left, right } => {
                Self::write_expression(writer, left.as_ref(), hir, global_scope, indent)?;
                write!(writer, " {} ", operator)?;
                Self::write_expression(writer, right.as_ref(), hir, global_scope, indent)?;
            }
            HIRExprKind::Unary { operator, operand } => {
                write!(writer, "{}", operator)?;
                Self::write_expression(writer, operand.as_ref(), hir, global_scope, indent)?;
            }
            HIRExprKind::If { condition, then_block, else_block } => {
                write!(writer, "if ")?;
                Self::write_expression(writer, condition, hir, global_scope, indent)?;
                writeln!(writer, " {{")?;

                Self::write_expression(writer, then_block, hir, global_scope, indent + 1)?;
                
                if let Some(else_block) = else_block {
                    Self::write_indent(writer, indent)?;
                    writeln!(writer, "}} else {{")?;
                    Self::write_expression(writer, else_block, hir, global_scope, indent + 1)?;
                }
                
                Self::write_indent(writer, indent)?;
                writeln!(writer, "}}")?;
            }
            HIRExprKind::Block { body, scope_id: _ } => {
                Self::write_indent(writer, indent)?;
                writeln!(writer, "{{")?;
                
                for statement in body.statements.iter() {
                    Self::write_indent(writer, indent + 1)?;
                    Self::write_statement(writer, statement, hir, global_scope, indent + 1)?;
                }

                Self::write_indent(writer, indent)?;
                writeln!(writer, "}}")?;
            }
            HIRExprKind::Call { fx_idx, args } => {
                let fx = global_scope.functions.get(*fx_idx);
                write!(writer, "{}(", fx.name)?;

                for (param_idx, param) in args.iter().enumerate() {
                    Self::write_expression(writer, param, hir, global_scope, indent)?;
                    if param_idx != args.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }

                write!(writer, ")")?;
            }
            HIRExprKind::Return { expr } => {
                write!(writer, "return ")?;
                Self::write_expression(writer, expr, hir, global_scope, indent)?;
            }
            HIRExprKind::Loop { body } => {
                writeln!(writer, "loop {{ ")?;
                for statement in body {
                    Self::write_indent(writer, indent + 1)?;
                    Self::write_statement(writer, statement, hir, global_scope, indent + 1)?;
                }

                Self::write_indent(writer, indent)?;
                writeln!(writer, "}}")?;
            }
            HIRExprKind::Break => {
                write!(writer, "break")?;
            }
            HIRExprKind::Continue => {
                write!(writer, "continue")?;
            }
            HIRExprKind::Path(qualified_path) => {
                match &qualified_path {
                    QualifiedPath::ResolvedVariable(var_idx) => {
                        let var = &global_scope.variables[*var_idx];
                        write!(writer, "{}", var.name.tokens.last().unwrap().span.literal)?;
                    }
                    QualifiedPath::ResolvedType(item_idx) => {
                        // Get struct name from the item
                        let struct_item = &global_scope.structs[*item_idx];
                        if let ItemKind::Struct(name, _, _) = &struct_item.kind {
                            write!(writer, "{}", name.span.literal)?;
                        }
                    }
                    QualifiedPath::ResolvedEnumVariant(enum_idx, _discriminant) => {
                        let enum_def = &global_scope.enums[*enum_idx];
                        write!(writer, "{}::<variant>", enum_def.name)?;
                    }
                }
            }
        }

        Ok(())
    }

    fn write_item(writer: &mut W, item: &HIRItemId, hir: &HIR, global_scope: &GlobalScope, _indent: usize) -> Result<()> {
        match item.kind {
            HIRItemKind::Struct => {
                let ast_item = global_scope.structs.get(item.from);
                if let ItemKind::Struct(name, generics, variant_data) = &ast_item.kind {
                    write!(writer, "struct {}", name.span.literal)?;
                    
                    if !generics.params.is_empty() {
                        write!(writer, "<")?;
                        for (i, param) in generics.params.iter().enumerate() {
                            write!(writer, "{}", param.identifier.span.literal)?;
                            if i < generics.params.len() - 1 {
                                write!(writer, ", ")?;
                            }
                        }
                        write!(writer, ">")?;
                    }
                    
                    match variant_data {
                        VariantData::Struct { fields } => {
                            writeln!(writer, " {{")?;
                            for field in fields {
                                if let Some(ref field_name) = field.identifier {
                                    write!(writer, "    {}: ", field_name.span.literal)?;
                                    Self::write_type_kind(writer, &field.ty)?;
                                    writeln!(writer, ",")?;
                                }
                            }
                            writeln!(writer, "}}\n")?;
                        }
                        VariantData::Tuple(elements) => {
                            write!(writer, "(")?;
                            for (i, element) in elements.iter().enumerate() {
                                Self::write_type_kind(writer, &element.ty)?;
                                if i < elements.len() - 1 {
                                    write!(writer, ", ")?;
                                }
                            }
                            writeln!(writer, ");\n")?;
                        }
                        VariantData::Unit => {
                            writeln!(writer, ";\n")?;
                        }
                    }
                }
            }
            HIRItemKind::Enum => {
                let enum_info = global_scope.enums.get(item.from);
                writeln!(writer, "enum {} {{", enum_info.name)?;
                
                for variant in &enum_info.variants {
                    write!(writer, "    {}", variant.name)?;
                    
                    match &variant.data {
                        VariantData::Struct { fields } => {
                            writeln!(writer, " {{")?;
                            for field in fields {
                                if let Some(ref field_name) = field.identifier {
                                    write!(writer, "        {}: ", field_name.span.literal)?;
                                    Self::write_type_kind(writer, &field.ty)?;
                                    writeln!(writer, ",")?;
                                }
                            }
                            writeln!(writer, "    }}")?;
                        }
                        VariantData::Tuple(elements) => {
                            write!(writer, "(")?;
                            for (i, element) in elements.iter().enumerate() {
                                Self::write_type_kind(writer, &element.ty)?;
                                if i < elements.len() - 1 {
                                    write!(writer, ", ")?;
                                }
                            }
                            writeln!(writer, "),")?;
                        }
                        VariantData::Unit => {
                            writeln!(writer, ",")?;
                        }
                    }
                }
                
                writeln!(writer, "}}\n")?;
            }
            HIRItemKind::Impl => {
                let impl_info = global_scope.impls.get(item.from);
                write!(writer, "impl")?;
                
                if !impl_info.generics.params.is_empty() {
                    write!(writer, "<")?;
                    for (i, param) in impl_info.generics.params.iter().enumerate() {
                        write!(writer, "{}", param.identifier.span.literal)?;
                        if i < impl_info.generics.params.len() - 1 {
                            write!(writer, ", ")?;
                        }
                    }
                    write!(writer, ">")?;
                }
                
                write!(writer, " ")?;
                Self::write_type_kind(writer, &impl_info.self_type)?;
                writeln!(writer, " {{")?;
                
                // Associated items
                for assoc_item in &impl_info.items {
                    match &assoc_item.kind {
                        snowflake_front::ast::AssociatedItemKind::Function(fx_decl) => {
                            let type_name = match &*impl_info.self_type {
                                AstType::Simple { type_name } => type_name.span.literal.clone(),
                                AstType::Path(_, path) => path.segments.last().unwrap().identifier.span.literal.clone(),
                                _ => continue,
                            };
                            
                            let method_name = fx_decl.identifier.span.literal.clone();
                            let path = format!("{}::{}", type_name, method_name);
                            
                            if let Some((fx_idx, fx)) = global_scope.functions.indexed_iter()
                                .find(|(_, fx)| fx.name == path)
                            {
                                write!(writer, "    fx {}(", method_name)?;
                                
                                for (i, param_id) in fx.parameters.iter().enumerate() {
                                    let param = global_scope.variables.get(*param_id);

                                    if param.name.segments.last().unwrap().identifier.span.literal == "self" {
                                        write!(writer, "self")?;
                                    } else {
                                        write!(
                                            writer,
                                            "{}: {}",
                                            param.name.segments.last().unwrap().identifier.span.literal, param.ty,
                                        )?;
                                    }

                                    if i < fx.parameters.len() - 1 {
                                        write!(writer, ", ")?;
                                    }
                                }
                                writeln!(writer, ") -> {} {{", fx.return_type)?;
                                
                                if let Some(body) = hir.functions.get(&fx_idx) {
                                    for statement in body {
                                        Self::write_indent(writer, _indent + 2)?;
                                        Self::write_statement(writer, statement, hir, global_scope, _indent + 2)?;
                                    }
                                }
                                
                                writeln!(writer, "    }}")?;
                            }
                        }
                        snowflake_front::ast::AssociatedItemKind::Const(const_item) => {
                            write!(writer, "    const ")?;
                            if let snowflake_front::ast::PatternKind::Identifier(_, ident) = &const_item.identifier.kind {
                                write!(writer, "{}", ident.span.literal)?;
                            }
                            write!(writer, ": ")?;
                            Self::write_type_kind(writer, &const_item.type_annotation.type_kind)?;
                            writeln!(writer)?;
                        }
                    }
                }
                
                writeln!(writer, "}}\n")?;
            }
        }

        Ok(())
    }

    fn write_type_kind(writer: &mut W, type_kind: &AstType) -> Result<()> {
        match type_kind {
            AstType::Simple { type_name } => {
                write!(writer, "{}", type_name.span.literal)?;
            }
            AstType::Array { element_type, length, .. } => {
                write!(writer, "[")?;
                Self::write_type_kind(writer, element_type)?;
                write!(writer, "; {}]", length.span.literal)?;
            }
            AstType::Slice { element_type, .. } => {
                write!(writer, "[")?;
                Self::write_type_kind(writer, element_type)?;
                write!(writer, "]")?;
            }
            AstType::Tuple { element_types, .. } => {
                write!(writer, "(")?;
                for (i, elem) in element_types.iter().enumerate() {
                    Self::write_type_kind(writer, elem)?;
                    if i < element_types.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }
                write!(writer, ")")?;
            }
            AstType::Path(_, path) => {
                let type_name = path.segments.last().unwrap().identifier.span.literal.clone();
                write!(writer, "{}", type_name)?;
            }
            AstType::ImplTrait(_, _) => {
                write!(writer, "impl Trait")?;
            }
        }
        Ok(())
    }

    fn write_indent(writer: &mut W, indent: usize) -> Result<()> {
        for _ in 0..indent {
            write!(writer, "{}", INDENT)?;
        }

        Ok(())
    }
}