use crate::ir::mir::{basic_block::BasicBlockIdx, optimisations::MIRPass, InstructionKind, MIR};


pub struct UnreachableCodeElimination;

impl MIRPass for UnreachableCodeElimination {
    fn run(&mut self, mir: &mut MIR) -> u32 {
        let mut changes = 0;

        for function in mir.functions.iter_mut() {
            let mut bb_to_remove: Vec<BasicBlockIdx> = vec![];
            let predecessors = function.predecessors(&mir.basic_blocks);
            let successors = function.successors(&mir.basic_blocks);

            // For bb that do not have predecessors, ie unreachable, remove them
            // But never remove the entry block of the function (first basic block in the function)
            for (i, bb) in function.basic_blocks.iter().copied().enumerate() {
                // Skip the entry block (first basic block in this function)
                if i == 0 {
                    continue;
                }

                if predecessors.get(bb).map(|preds| preds.len()).unwrap_or_default() == 0 {
                    tracing::debug!("Found unreachable basic block {}, it will now be removed", bb);
                    bb_to_remove.push(bb);
                    changes += 1;
                }
            }

            // Handling phi nodes that reference the unreachable bb block
            for bb_idx in bb_to_remove.into_iter() {
                if let Some(successors) = successors.get(bb_idx) {
                    for successor in successors {
                        let successor_with_phi = mir.basic_blocks.get_mut_or_panic(*successor);

                        for instruct_idx in successor_with_phi.instructions.iter_mut() {
                            let instruction = function.instructions.get_mut(*instruct_idx);
                            match &mut instruction.kind {
                                InstructionKind::Phi(phi) => {
                                    phi.operands.retain(|(from, _)| *from != bb_idx);
                                }
                                _ => {}
                            }
                        }
                    }
                }

                mir.basic_blocks.remove(bb_idx);
                function.basic_blocks.retain(|bb| *bb != bb_idx);
            }
        }

        changes
    }
}