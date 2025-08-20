pub mod backends;

use anyhow::Result;
use snowflake_middle::ir::lir::LIR;
use std::process::Command;


/// Compile LIR to LLVM IR using the inkwell backend
pub fn compile_with_llvm(lir: &LIR, module_name: &str) -> Result<String> {
    use inkwell::context::Context;
    
    let context = Context::create();
    let mut llvm_backend = backends::llvm::LLVMBackend::new(&context, module_name);
    llvm_backend.compile_lir(lir)?;
    
    Ok(llvm_backend.print_to_string())
}

/// Compile LIR to an executable using LLVM toolchain
pub fn compile_to_executable(lir: &LIR, module_name: &str, output_path: &str) -> Result<()> {
    let llvm_ir = compile_with_llvm(lir, module_name)?;
    
    let ir_file = format!("{}.ll", output_path);
    std::fs::write(&ir_file, &llvm_ir)?;
    
    let output = Command::new("clang")
        .arg(&ir_file)
        .arg("-o")
        .arg(output_path)
        .output()?;
    
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(anyhow::anyhow!("Failed to compile executable: {}", stderr));
    }
    
    std::fs::remove_file(&ir_file).ok();
    
    Ok(())
}