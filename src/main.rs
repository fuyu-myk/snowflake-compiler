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
        let b = b + 20

        fx mul(a: int) -> int {
            return 1 
            }
        let z = mul(a, a)

        fx mul(a: int, b: int) -> int {
            let sum = 0
            while b > 0 {
                sum = sum + a
                b = b - 1
            }
            return sum
        }

        let c = mul(a, b)

        let d = if a == b {
            10
        } else {
            20
        }

        let e = c + d
        z
    ";

    // Compile the input code ^0^
    let mut compilation_unit = CompilationUnit::compile(input).map_err(|_| ())?;
    compilation_unit.run_compiler();
    Ok(())
}