use crate::compilation_unit::CompilationUnit;

mod ast;
mod diagnostics;
mod text;
mod compilation_unit;

fn main() -> Result<(), ()> {
    let input = "\
        fx foo {
        }

        let a = add(1, 2)

        fx add(a, b) {
            return a + b
        }

        while a < 10 {
            a = a + 1
        }

        if a >= 10 {
            a = 25
        } else {
            a = 20
            let a = 10
            a = 15
        }

        let b = 10
        if true {
            b = 1
        }

        a
        b
    ";

    // Compile the input code ^0^
    let compilation_unit = CompilationUnit::compile(input).map_err(|_| ())?;
    compilation_unit.run_compiler();
    Ok(())
}