/*
 * Semantic analysis module for the snowflake compiler
 * This module performs mutability checking and other semantic validations
 */

pub mod mutability;

use std::rc::Rc;

use anyhow::Result;
use snowflake_common::{diagnostics::{printer::DiagnosticsPrinter, DiagnosticsReportCell}, text};
use snowflake_front::compilation_unit::GlobalScope;
use crate::ir::hir::HIR;

pub struct SemanticAnalyzer {
    diagnostics: DiagnosticsReportCell,
}

impl SemanticAnalyzer {
    pub fn new(diagnostics: DiagnosticsReportCell) -> Self {
        Self { diagnostics }
    }

    /// Run all semantic analysis passes on the HIR
    pub fn analyze(&mut self, input: &str,hir: &HIR, global_scope: &mut GlobalScope) -> Result<(), DiagnosticsReportCell> {
        // Mutability checking pass
        let _ = self.run_mutability_checking(hir, global_scope);
        let text = text::SourceText::new(input.to_string());

        Self::check_diagnostics(&text, &self.diagnostics).map_err(|_| Rc::clone(&self.diagnostics))?;

        Ok(())
    }

    fn run_mutability_checking(&mut self, hir: &HIR, global_scope: &mut GlobalScope) -> Result<(), DiagnosticsReportCell> {
        let mut mutability_checker = mutability::MutabilityChecker::new(self.diagnostics.clone());
        mutability_checker.check(hir, global_scope).map_err(|_| Rc::clone(&self.diagnostics))
    }

    fn check_diagnostics(text: &text::SourceText, diagnostics_report: &DiagnosticsReportCell) -> Result<(), ()> {
        let diagnostics_binding = diagnostics_report.borrow();
        if diagnostics_binding.errors.len() > 0 {
            let diagnostics_printer = DiagnosticsPrinter::new(
                &text,
                &diagnostics_binding.errors
            );

            diagnostics_printer.print_error();
            println!("");
            
            return Err(());
        }
        
        Ok(())
    }
}
