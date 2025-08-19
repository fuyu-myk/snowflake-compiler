use std::io::Write;

use anyhow::Result;
use snowflake_common::Idx;
use snowflake_front::compilation_unit::GlobalScope;

use crate::ir::hir::{HIRExprKind, HIRExpression, HIRStatement, HIRStmtKind, HIR};


const INDENT: &str = "    ";

pub struct HIRWriter<W> {
    _phantom: std::marker::PhantomData<W>,
}

impl <W> HIRWriter<W> where W: Write {
    pub fn write(writer: &mut W, hir: &HIR, global_scope: &GlobalScope, indent: usize) -> Result<()> {
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
            HIRStmtKind::Declaration { var_idx, init } => {
                let var = global_scope.variables.get(*var_idx);
                write!(writer, "let {}: {}", var.name, var.ty)?;

                if let Some(init) = init {
                    write!(writer, " = ")?;
                    Self::write_expression(writer, init, global_scope, indent)?;
                }

                writeln!(writer)?;
            }
            HIRStmtKind::Assignment { var_idx, expr } => {
                let var = global_scope.variables.get(*var_idx);
                write!(writer, "{} = ", var.name)?;

                Self::write_expression(writer, expr, global_scope, indent)?;
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
            HIRExprKind::Var(var_idx) => {
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
            HIRExprKind::Index { object, index, bounds_check: _ } => {
                Self::write_expression(writer, object, global_scope, indent)?;
                write!(writer, "[")?;
                Self::write_expression(writer, index, global_scope, indent)?;
                write!(writer, "]")?;
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

    fn write_indent(writer: &mut W, indent: usize) -> Result<()> {
        for _ in 0..indent {
            write!(writer, "{}", INDENT)?;
        }

        Ok(())
    }
}