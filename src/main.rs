use std::{env, fs::File, io::Write};

use crate::{compilation_unit::CompilationUnit, ir::{hir::{HIRBuilder, HIRWriter}, mir::{optimisations::Optimiser, MIRBuilder, MIRWriter}}};

use anyhow::{anyhow, Result};

mod ast;
mod diagnostics;
mod text;
mod compilation_unit;
mod typings;
mod codegen;
mod ir;


fn main() -> Result<()> {
    // Get command line arguments
    let args: Vec<String> = env::args().collect();
    
    // Check if a file path was provided
    if args.len() != 2 {
        eprintln!("Usage: {} <file.snow>", args[0]);
        return Err(anyhow!("Please provide a .snow file to compile"));
    }
    
    let file_path = &args[1];
    
    // Check if the file has the correct extension
    if !file_path.ends_with(".snow") {
        return Err(anyhow!("File must have .snow extension"));
    }
    
    // Read the input file
    let input = std::fs::read_to_string(file_path)
        .map_err(|e| anyhow!("Failed to read file '{}': {}", file_path, e))?;

    // Compile the input code ^0^
    let mut compilation_unit = CompilationUnit::compile(&input).map_err(|_err| anyhow!("Compilation failed"))?;
    compilation_unit.run_compiler();

     // GCC codegen
    //let program = codegen::c::CProgram::from_compilation_unit(&compilation_unit);
    //let c_return_value = program.run()?;
    //println!("C program returned {}", c_return_value);

    // HIR
    let hir_builder = HIRBuilder::new();
    let hir = hir_builder.build(&compilation_unit.ast, &mut compilation_unit.global_scope);
    let mut hir_output = String::new();

    HIRWriter::write(&mut hir_output, &hir, &compilation_unit.global_scope, 0)?;
    println!("{}", hir_output); // display HIR output

    // MIR unoptimised
    let mir_builder = MIRBuilder::new();
    let mut mir = mir_builder.build(&hir, &compilation_unit.global_scope);
    let mut mir_output = String::new();
    let mut mir_graphviz = String::new();

    MIRWriter::write_graphviz(&mut mir_graphviz, &mir)?;
    File::create("mir.dot")?.write_all(mir_graphviz.as_bytes())?;
    MIRWriter::write_txt(&mut mir_output, &mir)?;
    println!("{}", mir_output);

    // MIR optimisations
    let mut optimiser = Optimiser::new();
    optimiser.optimise(&mut mir);
    let mut optimised_mir_graphviz = String::new();
    //let mut optimised_mir_output = String::new();

    MIRWriter::write_graphviz(&mut optimised_mir_graphviz, &mir)?;
    File::create("optimised-mir.dot")?.write_all(optimised_mir_graphviz.as_bytes())?;
    //MIRWriter::write_txt(&mut optimised_mir_output, &mir)?;
    //println!("{}", optimised_mir_output);

    // LIR (todo)

    Ok(())
}