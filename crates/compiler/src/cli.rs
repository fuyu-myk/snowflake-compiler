use anyhow::{anyhow, Result};
use std::env;


/// Configuration for what outputs to show
#[derive(Debug, Clone)]
pub struct OutputConfig {
    pub show_hir: bool,
    pub show_mir_unoptimised: bool,
    pub show_mir_optimised: bool,
    pub show_llvm: bool,
    pub show_all_ir: bool,
    pub generate_llvm_file: bool,
    pub generate_executable: bool,
}

impl Default for OutputConfig {
    fn default() -> Self {
        Self {
            show_hir: false,
            show_mir_unoptimised: false,
            show_mir_optimised: false,
            show_llvm: false,
            show_all_ir: false,
            generate_llvm_file: false,
            generate_executable: true,
        }
    }
}

/// Parsed command line arguments
#[derive(Debug, Clone)]
pub struct CliArgs {
    pub file_path: String,
    pub output_config: OutputConfig,
}

impl CliArgs {
    /// Parse command line arguments
    pub fn parse() -> Result<Self> {
        let args: Vec<String> = env::args().collect();
        
        if args.len() < 2 {
            Self::print_usage(&args[0]);
            return Err(anyhow!("Please provide a .snow file to compile"));
        }

        // Check for help first
        for arg in args.iter().skip(1) {
            if arg == "--help" || arg == "-h" {
                Self::print_usage(&args[0]);
                std::process::exit(0);
            }
        }
        
        let file_path = args[1].clone();
        
        // Check if the file has the correct extension
        if !file_path.ends_with(".snow") {
            return Err(anyhow!("File must have .snow extension"));
        }
        
        let mut output_config = OutputConfig::default();
        
        // Parse flags
        for arg in args.iter().skip(2) {
            match arg.as_str() {
                "--hir" => output_config.show_hir = true,
                "--mir-unoptimised" => output_config.show_mir_unoptimised = true,
                "--mir-optimised" => output_config.show_mir_optimised = true,
                "--llvm" => output_config.show_llvm = true,
                "--all-ir" => output_config.show_all_ir = true,
                "--llvm-file" => output_config.generate_llvm_file = true,
                "--no-exe" => output_config.generate_executable = false,
                flag => {
                    eprintln!("Unknown flag: {}", flag);
                    Self::print_usage(&args[0]);
                    return Err(anyhow!("Unknown command line flag: {}", flag));
                }
            }
        }
        
        Ok(Self {
            file_path,
            output_config,
        })
    }
    
    /// Print usage information
    fn print_usage(program_name: &str) {
        eprintln!("Usage: {} <file.snow> [OPTIONS]", program_name);
        eprintln!();
        eprintln!("OPTIONS:");
        eprintln!("  --hir                 Show HIR (High-level IR)");
        eprintln!("  --mir-unoptimised     Show unoptimised MIR (Mid-level IR)");
        eprintln!("  --mir-optimised       Show optimised MIR");
        eprintln!("  --llvm                Show LLVM IR");
        eprintln!("  --all-ir              Show all IR representations");
        eprintln!("  --llvm-file           Generate .ll file with LLVM IR");
        eprintln!("  --no-exe              Don't generate executable (default: generate)");
        eprintln!("  --help, -h            Show this help message");
        eprintln!();
        eprintln!("EXAMPLES:");
        eprintln!("  {} program.snow                  # Compile to executable", program_name);
        eprintln!("  {} program.snow --all-ir         # Show all IR + compile", program_name);
        eprintln!("  {} program.snow --llvm --no-exe  # Show LLVM IR only", program_name);
    }
}
