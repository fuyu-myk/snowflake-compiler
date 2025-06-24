use crate::{compilation_unit::CompilationUnit, ir::hir::{HIRBuilder, HIRWriter}};

use anyhow::{anyhow, Result};

mod ast;
mod diagnostics;
mod text;
mod compilation_unit;
mod typings;
mod codegen;
mod ir;


fn main() -> Result<()> {
    let input = "
        fx main() -> int {
            let result = 0;
            let counter = 10;

            while (counter > 0) {
                result = result + 2;
                counter = counter - 1;
            }

            return result;
        }
    ";

    // Compile the input code ^0^
    let mut compilation_unit = CompilationUnit::compile(input).map_err(|_err| anyhow!("Compilation failed"))?;
    compilation_unit.run_compiler();

    /* // GCC codegen
    let program = codegen::c::CProgram::from_compilation_unit(&compilation_unit);
    let c_return_value = program.run()?;
    println!("C program returned {}", c_return_value);
    fx mul(a: int, b: int) -> int {
            let result = 0;
            let counter = b;

            while (counter > 0) {
                result = result + a;
                counter = counter - 1;
            }

            return result;
        }

        fx main() -> int {
            let a = 23;
            let b = 86;

            let c = mul(a, b);
            
            return c;
    */

    // HIR
    let hir_builder = HIRBuilder::new();
    let hir = hir_builder.build(&compilation_unit.ast, &mut compilation_unit.global_scope);
    let mut hir_output = String::new();

    HIRWriter::write(&mut hir_output, &hir, &compilation_unit.global_scope, 0)?;
    println!("{}", hir_output); // display HIR output

    Ok(())
}