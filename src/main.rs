use crate::compilation_unit::CompilationUnit;

mod ast;
mod diagnostics;
mod text;
mod compilation_unit;

fn main() {
    let input = "
        let a = -1 + 2 * 3 - 4 / 5 | 6 + ~6 ^ 7 ** 2
    ";

    // Compile the input code ^0^
    let compilation_unit = CompilationUnit::compile(input);
    compilation_unit.run_errorless();
}