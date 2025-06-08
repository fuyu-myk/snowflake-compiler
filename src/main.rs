use crate::compilation_unit::CompilationUnit;

mod ast;
mod diagnostics;
mod text;
mod compilation_unit;

fn main() {
    let input = "
        let a = 0
        let b = 1

        if b > a
            a = 10
         else 
            a = 5
        a
    ";

    // Compile the input code ^0^
    let compilation_unit = CompilationUnit::compile(input);
    compilation_unit.run_errorless();
}