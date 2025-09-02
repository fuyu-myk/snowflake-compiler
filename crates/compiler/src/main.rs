use std::{fs::File, io::Write, process::ExitCode, rc::Rc};
use termion::{
    color::{Fg, Red, Yellow, Reset},
    style::{Bold, Reset as StyleReset},
};

use snowflake_common::text;
use snowflake_front::compilation_unit::CompilationUnit;
use snowflake_middle::ir::{
    hir::{HIRBuilder, HIRWriter}, 
    mir::{optimisations::Optimiser, MIRBuilder, MIRWriter},
    lir::builder::LIRBuilder
};
use snowflake_middle::analysis::SemanticAnalyzer;

use anyhow::{anyhow, Result};

mod cli;
use cli::CliArgs;


fn main() -> ExitCode {
    unsafe {
        std::env::set_var("RUST_BACKTRACE", "1");
    }
    tracing_subscriber::fmt::init();

    if let Err(e) = run() {
        eprintln!("{}", e);
        return ExitCode::FAILURE;
    }

    ExitCode::SUCCESS
}

fn run() -> Result<()> {
    // Parse command line arguments
    let args = CliArgs::parse()?;
    let config = &args.output_config;
    
    // Read the input file
    let input = std::fs::read_to_string(&args.file_path)
        .map_err(|e| anyhow!("Failed to read file '{}': {}", args.file_path, e))?;

    // Compile the input code ^0^
    let mut compilation_unit = CompilationUnit::compile(&input)
        .map_err(|err| {
            let error_count = err.borrow().errors.len();
            if error_count == 1 {
                anyhow!(
                    "{}{}error{}{}: could not compile `{}` due to {} previous error",
                    Fg(Red), Bold, StyleReset, Fg(Reset),
                    args.file_path,
                    error_count
                )
            } else {
                anyhow!(
                    "{}{}error{}{}: could not compile `{}` due to {} previous errors",
                    Fg(Red), Bold, StyleReset, Fg(Reset),
                    args.file_path,
                    error_count
                )
            }
        })?;
    
    //compilation_unit.run_compiler(); // For eval

    // GCC codegen
    //let program = codegen::c::CProgram::from_compilation_unit(&compilation_unit);
    //let c_return_value = program.run()?;
    //println!("C program returned {}", c_return_value);

    // HIR
    let hir_builder = HIRBuilder::new(Rc::clone(&compilation_unit.diagnostics_report));
    let hir = hir_builder.build(&compilation_unit.ast, &mut compilation_unit.global_scope);

    // Semantic Analysis (Mutability checking)
    let mut semantic_analyzer = SemanticAnalyzer::new(Rc::clone(&compilation_unit.diagnostics_report));
    semantic_analyzer.analyze(&input, &hir, &mut compilation_unit.global_scope)
        .map_err(|err| {
            let error_count = err.borrow().errors.len();
            if error_count == 1 {
                anyhow!(
                    "{}{}error{}{}: could not compile `{}` due to {} previous error",
                    Fg(Red), Bold, StyleReset, Fg(Reset),
                    args.file_path,
                    error_count
                )
            } else {
                anyhow!(
                    "{}{}error{}{}: could not compile `{}` due to {} previous errors",
                    Fg(Red), Bold, StyleReset, Fg(Reset),
                    args.file_path,
                    error_count
                )
            }
        })?;

    // MIR (unoptimised)
    let mir_builder = MIRBuilder::new(Rc::clone(&compilation_unit.diagnostics_report));
    let mut mir = mir_builder.build(&hir, &compilation_unit.global_scope);
    let mut mir_graphviz = String::new();

    MIRWriter::write_graphviz(&mut mir_graphviz, &mir)?;
    File::create("mir.dot")?.write_all(mir_graphviz.as_bytes())?;

    // MIR optimisations
    let mut optimiser = Optimiser::new();
    optimiser.optimise(&mut mir);
    let mut optimised_mir_graphviz = String::new();

    MIRWriter::write_graphviz(&mut optimised_mir_graphviz, &mir)?;
    File::create("optimised-mir.dot")?.write_all(optimised_mir_graphviz.as_bytes())?;

    // LIR
    let lir_builder = LIRBuilder::new(&mir, &compilation_unit.global_scope);
    let lir = lir_builder.build();
    //dbg!(&lir);

    // Asm codegen
    //let mut asm = snowflake_codegen::backends::x86_64::X86_64Codegen::new();
    //asm.generate(&lir)?;
    //let asm_output = asm.get_asm_output()?;
    //println!("{}", asm_output);

    // LLVM
    let llvm_ir = snowflake_codegen::compile_with_llvm(&lir, "my_module")?;
    
    // Generate execs based on configuration
    let output_name = args.file_path.replace(".snow", "");

    // Optional LLVM IR file generation
    if config.generate_llvm_file {
        let ir_file = format!("{}.ll", output_name);
        std::fs::write(&ir_file, &llvm_ir)?;
        println!("LLVM IR written to: {}", ir_file);
    }

    CompilationUnit::output_warnings(&text::SourceText::new(input.to_string()), &compilation_unit.diagnostics_report);
    let warning_count = compilation_unit.diagnostics_report.borrow().warnings.len();
    if warning_count == 1 {
        println!(
            "{}{}warning{}{}: `{}` generated 1 warning\n",
            Fg(Yellow), Bold, StyleReset, Fg(Reset),
            args.file_path.replace(".snow", "")
        );
    } else if warning_count > 1 {
        println!(
            "{}{}warning{}{}: `{}` generated {} warnings\n",
            Fg(Yellow), Bold, StyleReset, Fg(Reset),
            args.file_path.replace(".snow", ""),
            warning_count
        );
    }

    if config.show_all_ir || config.show_hir {
        println!("=== HIR ===");
        let mut hir_output = Vec::new();
        HIRWriter::write(&mut hir_output, &hir, &compilation_unit.global_scope, 0)?;
        println!("{}", String::from_utf8(hir_output)?);
    }

    if config.show_all_ir || config.show_mir_unoptimised {
        println!("=== MIR Unoptimised ===");
        let mut mir_output = String::new();
        MIRWriter::write_txt(&mut mir_output, &mir)?;
        println!("{}", mir_output);
    }

    if config.show_all_ir || config.show_mir_optimised {
        println!("=== MIR Optimised ===");
        let mut optimised_mir_output = String::new();
        MIRWriter::write_txt(&mut optimised_mir_output, &mir)?;
        println!("{}", optimised_mir_output);
    }

    if config.show_all_ir || config.show_llvm {
        println!("=== LLVM IR ===");
        println!("{}", llvm_ir);
    }

    if config.generate_executable {
        snowflake_codegen::compile_to_executable(&lir, "my_module", &output_name)?;
        println!("Executable generated: {}\n", output_name);
    }

    Ok(())
}