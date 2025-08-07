use crate::{ir::mir::{basic_block::BasicBlockIdx, optimisations::MIRPass, FunctionIdx, MIR}};

mod copy_propagation;
mod constants_folding;
mod algebraic_simplification;


pub trait MIRPassLocal {
    fn run_on_bb(&mut self, mir: &mut MIR, fx_idx: FunctionIdx, bb_idx: BasicBlockIdx) -> u32;
}

pub struct LocalOptimiser {
    passes: Vec<Box<dyn MIRPassLocal>>,
}

impl LocalOptimiser {
    pub fn new() -> Self {
        Self {
            passes: vec![
                Box::new(algebraic_simplification::AlgebraicSimplification),
                Box::new(constants_folding::ConstantsFolding),
                Box::new(copy_propagation::CopyPropagation),
            ],
        }
    }
}

impl MIRPass for LocalOptimiser {
    fn run (&mut self, mir: &mut MIR) -> u32 {
        let mut changes = 0;
        let fx_indices: Vec<_> = mir.functions.indices().collect();
        for fx_idx in fx_indices {
            let bb_indices: Vec<_> = mir.functions[fx_idx].basic_blocks.clone();
            for bb_idx in bb_indices {
                if mir.basic_blocks[bb_idx].is_none() {
                    continue;
                }

                for pass in self.passes.iter_mut() {
                    changes += pass.run_on_bb(mir, fx_idx, bb_idx)
                }
            }
        }

        println!("LocalOptimiser executed {} change(s)", changes);
        changes
    }
}