/*
 * this program functions as a printer for diagnostic errors/warnings
 */

use super::Diagnostic;
use crate::text::SourceText;
use std::cmp;
use termion::color::{Fg, Red, Reset};


pub struct DiagnosticsPrinter<'a> {
    text: &'a SourceText,
    diagnostics: &'a [Diagnostic],
}

const PREFIX_LENGTH: usize = 8;

impl <'a> DiagnosticsPrinter<'a> {
    pub fn new(text: &'a SourceText, diagnostics: &'a [Diagnostic]) -> Self {
        Self {
            text,
            diagnostics,
        }
    }

    /// Converts diagnostic to a string
    /// 
    /// It utilises the following format:
    /// 
    /// let <red>x<reset> = 5;
    ///          ^
    ///          |
    ///          +-- Error message here (<line>:<column>)
    pub fn diagnostic_to_str(&self, diagnostic: &Diagnostic) -> String {
        // variables def
        let line_index = self.text.line_index(diagnostic.span.start);
        let line = self.text.fetch_line(line_index);
        let line_start = self.text.line_start(line_index);

        let column = diagnostic.span.start - line_start;
        
        let (prefix, span, suffix) = self.get_text_vars(diagnostic, &line, column);

        // actual msg
        let indent = cmp::min(PREFIX_LENGTH, column);
        
        let (arrow_pointers, arrow_line) = Self::format_arrow(diagnostic, indent);

        let error_message = Self::format_error_msg(diagnostic, indent, column, line_index);

        format!("{}{}{}{}{}\n{}\n{}\n{}", prefix, Fg(Red), span, Fg(Reset), suffix, arrow_pointers, arrow_line, error_message)
    }

    fn get_text_vars(&'a self, diagnostic: &Diagnostic, line: &'a str, column: usize) -> (&'a str, &'a str, &'a str) {
        let prefix_start = cmp::max(0, column as isize - PREFIX_LENGTH as isize) as usize;
        let prefix_end = column;
        let suffix_start = cmp::min(column + diagnostic.span.length(), line.len());
        let suffix_end = cmp::min(suffix_start + PREFIX_LENGTH, line.len());

        let prefix = &line[prefix_start..prefix_end];
        let span = &line[prefix_end..suffix_start];
        let suffix = &line[suffix_start..suffix_end];

        (prefix, span, suffix)
    }

    fn format_arrow(diagnostic: &Diagnostic, indent: usize) -> (String, String) {
        let arrow_pointers = format!("{:indent$}{}", "", std::iter::repeat( // formats preceding whitespace
            '^'
        ).take(
            diagnostic.span.length() // repeats ^ over span len
        ).collect::<String>(), indent = indent);
        let arrow_line = format!("{:indent$}|", "", indent = indent);

        (arrow_pointers, arrow_line)
    }

    fn format_error_msg(diagnostic: &Diagnostic, indent: usize, column: usize, line_index: usize) -> String {
        format!("{:indent$}+-- {} ({}:{})", "", diagnostic.message, column + 1, line_index + 1, indent = indent)
    }

    pub fn print(&self) {
        for diagnostic in self.diagnostics {
            println!("{}", self.diagnostic_to_str(diagnostic));
        }
    }
}