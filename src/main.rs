use std::{fs::File, io::Write, process::Command};

use crate::{codegen::CTranspiler, compilation_unit::CompilationUnit};

mod ast;
mod diagnostics;
mod text;
mod compilation_unit;
mod typings;
mod codegen;


fn main() -> Result<(), ()> {
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
    let mut compilation_unit = CompilationUnit::compile(input).map_err(|_| ())?;
    compilation_unit.run_compiler();

    // GCC codegen
    let mut c_transpiler = CTranspiler::new(&compilation_unit.global_scope);
    let transpiled_code = c_transpiler.transpile(&mut compilation_unit.ast);
    println!("{}", transpiled_code);

    // C file creation
    let mut c_file = File::create("out.c").unwrap();
    c_file.write_all(transpiled_code.as_bytes()).unwrap();

    // Compile with clang
    Command::new("clang")
        .arg("out.c")
        .arg("-o")
        .arg("out")
        .status()
        .unwrap();

    // Run compilied binary
    Command::new("./out").status().unwrap();

    Ok(())
}