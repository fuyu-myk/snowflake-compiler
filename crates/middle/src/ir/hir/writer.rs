use std::io::Write;

use anyhow::Result;
use snowflake_common::Idx;
use snowflake_front::{ast::{ItemKind, TypeKind, VariantData}, compilation_unit::GlobalScope};

use crate::ir::hir::{HIRExprKind, HIRExpression, HIRItemId, HIRStatement, HIRStmtKind, HIRStructTailExpr, HIR};


const INDENT: &str = "    ";

pub struct HIRWriter<W> {
    _phantom: std::marker::PhantomData<W>,
}

impl <W> HIRWriter<W> where W: Write {
    pub fn write(writer: &mut W, hir: &HIR, global_scope: &GlobalScope, indent: usize) -> Result<()> {
        for (_, statements) in &hir.top_statements {
            for stmt in statements {
                Self::write_statement(writer, stmt, global_scope, indent)?;
            }
        }
        for (fx_idx, body) in &hir.functions {
            // Check if this function exists in global scope (skip synthetic functions)
            let fx_opt = global_scope.functions.indexed_iter()
                .find(|(idx, _)| *idx == *fx_idx)
                .map(|(_, fx)| fx);
            
            if let Some(fx) = fx_opt {
                // Regular function with declaration
                write!(writer, "fx {}(", fx.name)?;

                for param_id in fx.parameters.iter() {
                    let param = global_scope.variables.get(*param_id);
                    write!(writer, "{}: {}", param.name, param.ty)?;
                    
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
                Self::write_statement(writer, statement, global_scope, indent + 1)?;
            }
            
            if fx_opt.is_some() {
                writeln!(writer, "}}\n")?;
            } else {
                writeln!(writer)?;
            }
        }

        Ok(())
    }

    fn write_statement(writer: &mut W, statement: &HIRStatement, global_scope: &GlobalScope, indent: usize) -> Result<()> {
        match &statement.kind {
            HIRStmtKind::Expression { expr } => {
                Self::write_expression(writer, expr, global_scope, indent)?;
                writeln!(writer)?;
            }
            HIRStmtKind::Declaration { var_idx, init_expr, is_mutable } => {
                let var = &global_scope.variables[*var_idx];
                let mut_keyword = if *is_mutable { "mut " } else { "" };
                write!(writer, "let {}{}: {}", mut_keyword, var.name, var.ty)?;

                if let Some(init) = init_expr {
                    write!(writer, " = ")?;
                    Self::write_expression(writer, init, global_scope, indent)?;
                }

                writeln!(writer)?;
            }
            HIRStmtKind::Const { var_idx, init_expr } => {
                let var = &global_scope.variables[*var_idx];
                write!(writer, "const {}: {}", var.name, var.ty)?;

                if let Some(init) = init_expr {
                    write!(writer, " = ")?;
                    Self::write_expression(writer, init, global_scope, indent)?;
                }

                writeln!(writer)?;
            }
            HIRStmtKind::Assignment { target, value } => {
                // Handle different types of assignment targets
                match &target.kind {
                    HIRExprKind::Var { var_idx } => {
                        let var = &global_scope.variables[*var_idx];
                        write!(writer, "{} = ", var.name)?;
                    }
                    _ => {
                        Self::write_expression(writer, target, global_scope, indent)?;
                        write!(writer, " = ")?;
                    }
                }

                Self::write_expression(writer, value, global_scope, indent)?;
                writeln!(writer)?;
            }
            HIRStmtKind::If { condition, then_block, else_block } => {
                write!(writer, "if ")?;
                Self::write_expression(writer, condition, global_scope, indent)?;
                writeln!(writer, " {{")?;

                for statement in then_block {
                    Self::write_indent(writer, indent + 1)?;
                    Self::write_statement(writer, statement, global_scope, indent + 1)?;
                }
                Self::write_indent(writer, indent)?;
                writeln!(writer, "}} else {{")?;

                for statement in else_block {
                    Self::write_indent(writer, indent + 1)?;
                    Self::write_statement(writer, statement, global_scope, indent + 1)?;
                }
                Self::write_indent(writer, indent)?;
                writeln!(writer, "}}")?;
            }
            HIRStmtKind::Block { body, scope_id: _ } => {
                Self::write_indent(writer, indent)?;
                writeln!(writer, "{{")?;
                for statement in body {
                    Self::write_indent(writer, indent + 1)?;
                    Self::write_statement(writer, statement, global_scope, indent + 1)?;
                }

                Self::write_indent(writer, indent)?;
                writeln!(writer, "}}")?;
            }
            HIRStmtKind::Return { expr } => {
                write!(writer, "return ")?;
                Self::write_expression(writer, expr, global_scope, indent)?;

                writeln!(writer)?;
            }
            HIRStmtKind::Loop { body } => {
                writeln!(writer, "loop {{ ")?;
                for statement in body {
                    Self::write_indent(writer, indent + 1)?;
                    Self::write_statement(writer, statement, global_scope, indent + 1)?;
                }

                Self::write_indent(writer, indent)?;
                writeln!(writer, "}}")?;
            }
            HIRStmtKind::Item { item_id } => {
                Self::write_item(writer, item_id, global_scope, indent)?;
            }
        }
        Ok(())
    }

    fn write_expression(writer: &mut W, expression: &HIRExpression, global_scope: &GlobalScope, indent: usize) -> Result<()> {
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
                let var = global_scope.variables.get(*var_idx);
                write!(writer, "{}", var.name)?;
            }
            HIRExprKind::Array { elements, element_type: _, alloc_type: _ } => {
                write!(writer, "[")?;
                for (i, elem) in elements.iter().enumerate() {
                    Self::write_expression(writer, elem, global_scope, indent)?;
                    if i != elements.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }
                write!(writer, "]")?;
            }
            HIRExprKind::Index { object, index, bounds_check: _, length: _ } => {
                Self::write_expression(writer, object, global_scope, indent)?;
                write!(writer, "[")?;
                Self::write_expression(writer, index, global_scope, indent)?;
                write!(writer, "]")?;
            }
            HIRExprKind::Tuple { elements, .. } => {
                write!(writer, "(")?;
                for (i, elem) in elements.iter().enumerate() {
                    Self::write_expression(writer, elem, global_scope, indent)?;
                    if i == 0 || i != elements.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }
                write!(writer, ")")?;
            }
            HIRExprKind::Field { object: tuple, field: index } => {
                Self::write_expression(writer, tuple, global_scope, indent)?;
                write!(writer, ".")?;
                Self::write_expression(writer, index, global_scope, indent)?;
            }
            HIRExprKind::Struct { fields, tail_expr } => {
                write!(writer, "{{ ")?;
                for (i, field) in fields.iter().enumerate() {
                    if field.is_shorthand {
                        write!(writer, "{}", field.identifier.span.literal)?;
                    } else {
                        write!(writer, "{}: ", field.identifier.span.literal)?;
                        Self::write_expression(writer, &field.expr, global_scope, indent)?;
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
            HIRExprKind::Binary { operator, left, right } => {
                Self::write_expression(writer, left.as_ref(), global_scope, indent)?;
                write!(writer, " {} ", operator)?;
                Self::write_expression(writer, right.as_ref(), global_scope, indent)?;
            }
            HIRExprKind::Unary { operator, operand } => {
                write!(writer, "{}", operator)?;
                Self::write_expression(writer, operand.as_ref(), global_scope, indent)?;
            }
            HIRExprKind::Call { fx_idx, args } => {
                let fx = global_scope.functions.get(*fx_idx);
                write!(writer, "{}(", fx.name)?;

                for (param_idx, param) in args.iter().enumerate() {
                    Self::write_expression(writer, param, global_scope, indent)?;
                    if param_idx != args.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }

                write!(writer, ")")?;
            }
            HIRExprKind::Break => {
                write!(writer, "break")?;
            }
            HIRExprKind::Continue => {
                write!(writer, "continue")?;
            }
        }

        Ok(())
    }

    fn write_item(writer: &mut W, item: &HIRItemId, global_scope: &GlobalScope, _indent: usize) -> Result<()> {
        // Get the actual item from global scope using the ItemIndex
        let ast_item = global_scope.get_struct(item.from);
        
        match &ast_item.kind {
            ItemKind::Struct(name, generics, variant_data) => {
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
                        writeln!(writer, "}}")?;
                    }
                }
            }
            ItemKind::Function(_) => {
                // This shouldn't happen
                writeln!(writer, "// Function item referenced as struct")?;
            }
            ItemKind::Const(_) => {
                // This shouldn't happen
                writeln!(writer, "// Const item referenced as struct")?;
            }
        }

        Ok(())
    }

    fn write_type_kind(writer: &mut W, type_kind: &TypeKind) -> Result<()> {
        match type_kind {
            TypeKind::Simple { type_name } => {
                write!(writer, "{}", type_name.span.literal)?;
            }
            TypeKind::Array { element_type, length, .. } => {
                write!(writer, "[")?;
                Self::write_type_kind(writer, element_type)?;
                write!(writer, "; {}]", length.span.literal)?;
            }
            TypeKind::Slice { element_type, .. } => {
                write!(writer, "[")?;
                Self::write_type_kind(writer, element_type)?;
                write!(writer, "]")?;
            }
            TypeKind::Tuple { element_types, .. } => {
                write!(writer, "(")?;
                for (i, elem) in element_types.iter().enumerate() {
                    Self::write_type_kind(writer, elem)?;
                    if i < element_types.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }
                write!(writer, ")")?;
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