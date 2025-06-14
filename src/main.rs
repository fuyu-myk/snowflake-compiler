use crate::compilation_unit::CompilationUnit;

mod ast;
mod diagnostics;
mod text;
mod compilation_unit;
mod typings;


fn main() -> Result<(), ()> {
    let input = "\
        let a: int = add(1, 2)
        fx add(a: int, b: int) -> int {
            return a + b
        }

        while a + 1 {
            a = a + 1
        }

        a
    ";

    // Compile the input code ^0^
    let compilation_unit = CompilationUnit::compile(input).map_err(|_| ())?;
    compilation_unit.run_compiler();
    Ok(())
}