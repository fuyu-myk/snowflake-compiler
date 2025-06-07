use crate::compilation_unit::CompilationUnit;

mod ast;
mod diagnostics;
mod text;
mod compilation_unit;

fn main() {
    let input = "
        let a =2 + 3
        let b = 9
        let c = 42 + e
        let d = (a + b) * c
    ";

    // Compile the input code ^0^
    let compilation_unit = CompilationUnit::compile(input);
    compilation_unit.run_compiler();
}