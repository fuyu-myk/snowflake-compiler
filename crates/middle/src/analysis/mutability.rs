/*
 * Mutability checking for the snowflake compiler
 * This module implements mutability analysis similar to rustc's borrowck
 */

use std::collections::HashSet;
use anyhow::Result;
use snowflake_common::diagnostics::DiagnosticsReportCell;
use snowflake_front::{ast::ItemIndex, compilation_unit::{GlobalScope, VariableIndex}};
use crate::ir::hir::{HIRExprKind, HIRExpression, HIRStatement, HIRStmtKind, QualifiedPath, HIR};

pub struct MutabilityChecker {
    diagnostics: DiagnosticsReportCell,
    /// Track which variables are mutable in the current scope
    mutable_variables: HashSet<VariableIndex>,
    /// Track variable assignments to detect multiple assignments to immutable variables
    assigned_variables: HashSet<VariableIndex>,
    /// Track which variables are declared as const
    const_variables: HashSet<VariableIndex>,
}

impl MutabilityChecker {
    pub fn new(diagnostics: DiagnosticsReportCell) -> Self {
        Self {
            diagnostics,
            mutable_variables: HashSet::new(),
            assigned_variables: HashSet::new(),
            const_variables: HashSet::new(),
        }
    }

    pub fn check(&mut self, hir: &HIR, global_scope: &GlobalScope) -> Result<(), ()> {
        let mut has_errors = false;

        // Check each function
        for (function_index, statements) in &hir.functions {
            if let Err(_) = self.check_function(*function_index, statements, global_scope, hir) {
                has_errors = true;
            }
        }

        if has_errors {
            Err(())
        } else {
            Ok(())
        }
    }

    fn check_function(
        &mut self, 
        _function_index: ItemIndex, 
        statements: &[HIRStatement], 
        global_scope: &GlobalScope,
        hir: &HIR
    ) -> Result<(), ()> {
        // Reset state for each function
        self.mutable_variables.clear();
        self.assigned_variables.clear();
        self.const_variables.clear();

        let mut has_errors = false;

        for statement in statements {
            if let Err(_) = self.check_statement(statement, global_scope, hir) {
                has_errors = true;
            }
        }

        if has_errors { Err(()) } else { Ok(()) }
    }

    fn check_statement(
        &mut self, 
        statement: &HIRStatement, 
        global_scope: &GlobalScope,
        hir: &HIR
    ) -> Result<(), ()> {
        match &statement.kind {
            HIRStmtKind::Declaration { var_idx, init_expr, is_mutable } => {
                if *is_mutable {
                    self.mutable_variables.insert(*var_idx);
                }

                if let Some(expr) = init_expr {
                    self.check_expression(expr, global_scope, hir)?;
                }

                self.assigned_variables.insert(*var_idx);

                Ok(())
            }
            HIRStmtKind::Const { var_idx, init_expr } => {
                self.const_variables.insert(*var_idx);

                if let Some(expr) = init_expr {
                    self.check_expression(expr, global_scope, hir)?;
                }

                self.assigned_variables.insert(*var_idx);

                Ok(())
            }
            HIRStmtKind::Assignment { target, value } => {
                match &target.kind {
                    HIRExprKind::Var { var_idx } => {
                        // Const check
                        if self.const_variables.contains(var_idx) {
                            let variable = &global_scope.variables[*var_idx].name.tokens.last().unwrap().span.literal;
                            self.diagnostics.borrow_mut().report_assignment_error(variable.to_string(), &target.span);
                            return Err(());
                        }
                        
                        // Mut check
                        if !self.mutable_variables.contains(var_idx) {
                            let variable = &global_scope.variables[*var_idx].name.tokens.last().unwrap().span.literal;
                            self.diagnostics.borrow_mut().report_immutable_assignment_error(variable.to_string(), None, &target.span);
                            return Err(());
                        }

                        if !self.mutable_variables.contains(var_idx) && self.assigned_variables.contains(var_idx) {
                            let variable = &global_scope.variables[*var_idx].name.tokens.last().unwrap().span.literal;
                            self.diagnostics.borrow_mut().report_multiple_assignment_error(variable.to_string(), &target.span);
                            return Err(());
                        }

                        self.assigned_variables.insert(*var_idx);
                    }
                    HIRExprKind::Path(path_expr) => {
                        // Handle ResolvedVariable paths
                        if let QualifiedPath::ResolvedVariable(var_idx) = path_expr {
                            // Const check
                            if self.const_variables.contains(var_idx) {
                                let variable = &global_scope.variables[*var_idx].name.tokens.last().unwrap().span.literal;
                                self.diagnostics.borrow_mut().report_assignment_error(variable.to_string(), &target.span);
                                return Err(());
                            }
                            
                            // Mut check
                            if !self.mutable_variables.contains(var_idx) {
                                let variable = &global_scope.variables[*var_idx].name.tokens.last().unwrap().span.literal;
                                self.diagnostics.borrow_mut().report_immutable_assignment_error(variable.to_string(), None, &target.span);
                                return Err(());
                            }

                            if !self.mutable_variables.contains(var_idx) && self.assigned_variables.contains(var_idx) {
                                let variable = &global_scope.variables[*var_idx].name.tokens.last().unwrap().span.literal;
                                self.diagnostics.borrow_mut().report_multiple_assignment_error(variable.to_string(), &target.span);
                                return Err(());
                            }

                            self.assigned_variables.insert(*var_idx);
                        }
                    }
                    HIRExprKind::Index { object, index, .. } => {
                        // Check if root object is mutable
                        if let Some(root_var_idx) = self.extract_root_variable(object) {
                            if !self.mutable_variables.contains(&root_var_idx) {
                                let variable = &global_scope.variables[root_var_idx].name.tokens.last().unwrap().span.literal;
                                let index_literal = index.span.literal.clone();
                                self.diagnostics.borrow_mut().report_immutable_assignment_error(
                                    format!("{}[{}]", variable, index_literal),
                                    Some(variable.to_string()), 
                                    &target.span
                                );
                                return Err(());
                            }
                        }
                    }
                    HIRExprKind::Field { object: tuple, field } => {
                        // Check if root object is mutable
                        if let Some(root_var_idx) = self.extract_root_variable(tuple) {
                            if !self.mutable_variables.contains(&root_var_idx) {
                                let variable = &global_scope.variables[root_var_idx].name.tokens.last().unwrap().span.literal;
                                let field_name = field.span.literal.clone();
                                self.diagnostics.borrow_mut().report_immutable_assignment_error(
                                    format!("{}.{}", variable, field_name),
                                    Some(variable.to_string()),
                                    &target.span
                                );
                                return Err(());
                            }
                        }
                    }
                    HIRExprKind::Binary { operator, left, right } => {
                        // Check if left operand is mutable
                        if let Some(left_var_idx) = self.extract_root_variable(left) {
                            if !self.mutable_variables.contains(&left_var_idx) {
                                let variable = &global_scope.variables[left_var_idx].name.tokens.last().unwrap().span.literal;
                                self.diagnostics.borrow_mut().report_immutable_assignment_error(
                                    format!("{} {}", variable, operator),
                                    Some(variable.to_string()),
                                    &target.span
                                );
                                return Err(());
                            }
                        }

                        // Check if right operand is mutable
                        if let Some(right_var_idx) = self.extract_root_variable(right) {
                            if !self.mutable_variables.contains(&right_var_idx) {
                                let variable = &global_scope.variables[right_var_idx].name.tokens.last().unwrap().span.literal;
                                self.diagnostics.borrow_mut().report_immutable_assignment_error(
                                    format!("{} {}", variable, operator),
                                    Some(variable.to_string()),
                                    &target.span
                                );
                                return Err(());
                            }
                        }
                    }
                    _ => {
                        // For other assignment targets, no mutability checking yet
                    }
                }

                // Check the target and value expressions
                self.check_expression(target, global_scope, hir)?;
                self.check_expression(value, global_scope, hir)?;

                Ok(())
            }
            HIRStmtKind::Expression{ expr } => {
                self.check_expression(expr, global_scope, hir)
            }
            HIRStmtKind::TailExpression { expr } => {
                self.check_expression(expr, global_scope, hir)
            }
            HIRStmtKind::Item { item_id: _ } => {
                Ok(())
            }
        }
    }

    fn check_expression(
        &mut self, 
        expression: &HIRExpression, 
        global_scope: &GlobalScope,
        hir: &HIR
    ) -> Result<(), ()> {
        match &expression.kind {
            HIRExprKind::Call { args, .. } => {
                for arg in args {
                    self.check_expression(arg, global_scope, hir)?;
                }
                Ok(())
            }
            HIRExprKind::Return { expr } => {
                self.check_expression(expr, global_scope, hir)
            }
            HIRExprKind::Binary { left, right, .. } => {
                self.check_expression(left, global_scope, hir)?;
                self.check_expression(right, global_scope, hir)
            }
            HIRExprKind::Unary { operand, .. } => {
                self.check_expression(operand, global_scope, hir)
            }
            HIRExprKind::If { then_block, else_block, .. } => {
                self.check_expression(&then_block, global_scope, hir)?;
                if let Some(else_expr) = else_block {
                    self.check_expression(else_expr, global_scope, hir)?;
                }
                Ok(())
            }
            HIRExprKind::Block { body, .. } => {
                for stmt in &body.statements {
                    self.check_statement(stmt, global_scope, hir)?;
                }
                Ok(())
            }
            HIRExprKind::Loop { body } => {
                for statement in body {
                    self.check_statement(statement, global_scope, hir)?;
                }

                Ok(())
            }
            HIRExprKind::Index { object, index, .. } => {
                self.check_expression(object, global_scope, hir)?;
                self.check_expression(index, global_scope, hir)
            }
            HIRExprKind::Field { object: tuple, field } => {
                self.check_expression(tuple, global_scope, hir)?;
                self.check_expression(field, global_scope, hir)
            }
            HIRExprKind::Array { elements, .. } => {
                for element in elements {
                    self.check_expression(element, global_scope, hir)?;
                }
                Ok(())
            }
            HIRExprKind::Tuple { elements, .. } => { 
                for element in elements {
                    self.check_expression(element, global_scope, hir)?;
                }
                Ok(())
            }
            // Literals don't need mutability checking
            HIRExprKind::Number(_) | HIRExprKind::Bool(_) | HIRExprKind::String(_) 
            | HIRExprKind::Float(_) | HIRExprKind::Usize(_) | HIRExprKind::Unit => Ok(()),
            _ => Ok(())
        }
    }

    /// Extract the root variable from a potentially nested expression chain.
    /// For example:
    /// - `var` -> Some(var_idx)
    /// - `arr[i]` -> Some(arr_var_idx)  
    /// - `tuple.0` -> Some(tuple_var_idx)
    /// - `arr[i].field` -> Some(arr_var_idx)
    /// - `complex_expr()` -> None
    fn extract_root_variable(&self, expr: &HIRExpression) -> Option<VariableIndex> {
        match &expr.kind {
            HIRExprKind::Var { var_idx } => Some(*var_idx),
            HIRExprKind::Path(path_expr) => match path_expr {
                QualifiedPath::ResolvedVariable(var_idx) => Some(*var_idx),
                QualifiedPath::ResolvedType(_) => None, // Type paths don't resolve to variables
                QualifiedPath::ResolvedEnumVariant(_, _) => None, // Enum variant constructors don't resolve to variables
            },
            HIRExprKind::Index { object, .. } => self.extract_root_variable(object),
            HIRExprKind::Field { object: tuple, .. } => self.extract_root_variable(tuple),
            _ => None,
        }
    }
}