use crate::compilation_unit::CompilationUnit;

mod ast;
mod diagnostics;
mod text;
mod compilation_unit;
mod typings;


fn main() -> Result<(), ()> {
    let input = "\
        let a = 10
        let b = 20

        fx add(a: int, b: int) -> int {
            return a + b
        }

        let c = add(a, b)

        let d = if a == b {
            10
        } else {
            20
        }

        let e = c + d
        e
    ";

    // Compile the input code ^0^
    let mut compilation_unit = CompilationUnit::compile(input).map_err(|_| ())?;
    compilation_unit.run_compiler();
    Ok(())
}