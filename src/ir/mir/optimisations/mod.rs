use crate::ir::mir::MIR;

mod global;
mod local;


pub trait MIRPass {
    /// Returns number of optimisations made to the MIR
    fn run(&mut self, mir: &mut MIR) -> u32;
}

pub struct Optimiser {
    passes: Vec<Box<dyn MIRPass>>,
}

impl Optimiser {
    pub fn new() -> Self {
        Self {
            passes: vec![
                Box::new(global::phi_elimination::PhiElimination),
                Box::new(global::branch_elimination::BranchElimination),
                Box::new(global::dead_code_elimination::DeadCodeElimination),
                Box::new(global::unreachable_code_elimination::UnreachableCodeElimination),
                Box::new(local::LocalOptimiser::new()),
            ],
        }
    }

    /// Executes optimisation on the MIR and outputs total time taken.
    pub fn optimise(&mut self, mir: &mut MIR) {
        let start = std::time::Instant::now();

        loop {
            let mut changes = 0;
            for pass in self.passes.iter_mut() {
                changes += pass.run(mir);
            }

            if changes == 0 {
                let end = std::time::Instant::now();
                println!("Optimisation completed in {}s\n", (end - start).as_secs_f64());
                return;
            }
        }
    }
}