use crate::{compilation_unit::CompilationUnit};

use anyhow::{anyhow, Result};

mod ast;
mod diagnostics;
mod text;
mod compilation_unit;
mod typings;
mod codegen;


fn main() -> Result<()> {
    let input = "\
        let a = 10
        let b = 20
        b = b + 20

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
    let mut compilation_unit = CompilationUnit::compile(input).map_err(|_err| anyhow!("Compilation failed"))?;
    compilation_unit.run_compiler();

    /* // GCC codegen
    let program = codegen::c::CProgram::from_compilation_unit(&compilation_unit);
    let c_return_value = program.run()?;
    println!("C program returned {}", c_return_value);
    */
    
    Ok(())
}