use crate::compilation_unit::CompilationUnit;

mod ast;
mod diagnostics;
mod text;
mod compilation_unit;

fn main() {
    let input = "
        let a = (1 + 2) * b + 3
    ";

    // Compile the input code ^0^
    let compilation_unit = CompilationUnit::compile(input);
    compilation_unit.run_errorless();
}