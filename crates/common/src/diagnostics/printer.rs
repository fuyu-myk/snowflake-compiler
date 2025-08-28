/*
 * this program functions as a printer for diagnostic errors/warnings
 */

use super::Diagnostic;
use crate::{diagnostics::DiagnosticKind, text::SourceText};
use std::cmp;
use termion::{color::{Fg, Blue, Red, Yellow, Reset},
    style::{Bold, Reset as StyleReset}
};


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
    /// ```shell
    /// error: <error message brief>
    ///        |
    /// <line> | let <red>x<reset> = 5;
    ///        |          ^
    ///        |          |
    ///        |          +-- Error message here (<line>:<column>)
    /// ```
    pub fn error_to_str(&self, diagnostic: &Diagnostic) -> String {
        // variables def
        let line_index = self.text.line_index(diagnostic.span.start);
        let line = self.text.fetch_line(line_index);
        let line_start = self.text.line_start(line_index);
        let padding = " ".repeat(line_index.to_string().len() + 1);

        let column = diagnostic.span.start - line_start;
        
        let (prefix, span, suffix) = self.get_text_vars(diagnostic, &line, column);

        // actual msg
        let indent = cmp::min(PREFIX_LENGTH, column);
        let (arrow_pointers, arrow_line) = Self::format_arrow(diagnostic, indent, padding.clone());
        let error_brief = Self::format_error_brief(diagnostic);
        let error_message = Self::format_error_msg(diagnostic, indent, column, line_index, padding.clone());
        let empty_line = Self::format_message_empty_line(padding.clone());

        format!(
            "{}\n{}{}{}{} |{}{}{}{}{}{}{}\n{}\n{}\n{}\n{}",
            error_brief,
            empty_line,
            Fg(Blue), Bold, line_index + 1, StyleReset, Fg(Reset),
            prefix,
            Fg(Red), span, Fg(Reset),
            suffix,
            arrow_pointers,
            arrow_line,
            error_message,
            empty_line,
        )
    }

    /// Converts warning diagnostic to a string
    /// 
    /// It utilises the following format:
    /// 
    /// ```shell
    /// warning: <warning message brief>
    ///        |
    /// <line> | const pi: float = 3.14;
    ///        |       ~~
    /// ```
    /// Note: The wave used to highlight the warning target is in yellow
    pub fn warning_to_str(&self, diagnostic: &Diagnostic) -> String {
        // variables def
        let line_index = self.text.line_index(diagnostic.span.start);
        let line = self.text.fetch_line(line_index);
        let line_start = self.text.line_start(line_index);
        let padding = " ".repeat(line_index.to_string().len() + 1);

        let column = diagnostic.span.start - line_start;

        let (prefix, span, suffix) = self.get_text_vars(diagnostic, &line, column);

        // actual msg
        let indent = cmp::min(PREFIX_LENGTH, column);
        let wave = Self::format_wave(diagnostic, indent, padding.clone());
        let warning_message = Self::format_warning_msg(diagnostic);
        let empty_line = Self::format_message_empty_line(padding);

        format!(
            "{}{}{}\n{}{}{}{} |{}{}{}{}{}\n{}",
            Bold, warning_message, StyleReset,
            empty_line,
            Fg(Blue), Bold, line_index + 1, StyleReset, Fg(Reset),
            prefix, span, suffix,
            wave,
        )
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

    fn format_arrow(diagnostic: &Diagnostic, indent: usize, padding: String) -> (String, String) {
        let arrow_pointers = format!("{}{}{}|{}{}{:indent$}{}",
            padding,
            Fg(Blue), Bold, StyleReset, Fg(Reset),
            "", std::iter::repeat( // formats preceding whitespace
                '^'
            ).take(
                diagnostic.span.length() // repeats ^ over span len
            ).collect::<String>(), indent = indent
        );

        let arrow_line = format!("{}{}{}|{}{}{:indent$}|",
            padding,
            Fg(Blue), Bold, StyleReset, Fg(Reset),
            "", indent = indent
        );

        (arrow_pointers, arrow_line)
    }

    fn format_message_empty_line(padding: String) -> String {
        format!("{}{}{}|{}{}\n", padding, Fg(Blue), Bold, StyleReset, Fg(Reset))
    }

    fn format_wave(diagnostic: &Diagnostic, indent: usize, padding: String) -> String {
        format!("{}{}{}|{}{}{:indent$}{}{}{}",
            padding,
            Fg(Blue), Bold, StyleReset, Fg(Reset),
            "", Fg(Yellow), std::iter::repeat( // formats preceding whitespace
                '~'
            ).take(
                diagnostic.span.length() // repeats ~ over span len
            ).collect::<String>(), StyleReset, indent = indent
        )
    }

    fn format_error_brief(diagnostic: &Diagnostic) -> String {
        format!("{}{}error{}: {}{}", Bold, Fg(Red), Fg(Reset),diagnostic.message_brief, StyleReset)
    }

    fn format_error_msg(diagnostic: &Diagnostic, indent: usize, column: usize, line_index: usize, padding: String) -> String {
        format!("{}{}{}|{}{}{:indent$}+-- {} ({}:{})",
            padding,
            Fg(Blue), Bold, StyleReset, Fg(Reset),
            "", diagnostic.message_full, line_index + 1, column + 1, 
            indent = indent
        )
    }

    fn format_warning_msg(diagnostic: &Diagnostic) -> String {
        format!("{}{}warning{}: {}{}", Bold, Fg(Yellow), Fg(Reset),diagnostic.message_full, StyleReset)
    }

    pub fn print_error(&self) {
        for diagnostic in self.diagnostics {
            match diagnostic.kind {
                DiagnosticKind::Error => println!("{}", self.error_to_str(diagnostic)),
                _ => {}
            }
        }
    }

    pub fn print_warning(&self) {
        for diagnostic in self.diagnostics {
            match diagnostic.kind {
                DiagnosticKind::Warning => println!("{}", self.warning_to_str(diagnostic)),
                _ => {}
            }
        }
    }
}