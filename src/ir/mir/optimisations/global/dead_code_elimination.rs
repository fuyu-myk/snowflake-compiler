use std::collections::HashSet;

use crate::ir::mir::{optimisations::MIRPass, InstructionIdx, InstructionKind, TerminatorKind, Value, MIR};


struct RefInstructions(HashSet<InstructionIdx>);

impl RefInstructions {
    pub fn new() -> Self {
        Self(HashSet::new())
    }

    pub fn insert_instruct_ref(&mut self, value: &Value) {
        if let Some(instruct_ref) = value.as_instruct_ref() {
            self.0.insert(instruct_ref);
        }
    }
}

pub struct DeadCodeElimination;

impl MIRPass for DeadCodeElimination {
    fn run(&mut self, mir: &mut MIR) -> u32 {
        let mut changes = 0;

        for function in mir.functions.iter_mut() {
            let mut referenced_instructions = RefInstructions::new();
            
            for bb in function.basic_blocks.iter().copied() {
                let bb = mir.basic_blocks.get_mut_or_panic(bb);

                for instruct_idx in bb.instructions.iter().copied() {
                    let instruction = &mut function.instructions[instruct_idx];

                    match &mut instruction.kind {
                        InstructionKind::Value(value) => referenced_instructions.insert_instruct_ref(value),
                        InstructionKind::Binary { left, right, .. } => {
                            referenced_instructions.insert_instruct_ref(left);
                            referenced_instructions.insert_instruct_ref(right);
                        }
                        InstructionKind::Unary { operand, .. } => referenced_instructions.insert_instruct_ref(operand),
                        InstructionKind::Call { args, .. } => {
                            for arg in args.iter_mut() {
                                referenced_instructions.insert_instruct_ref(arg);
                            }
                        }
                        InstructionKind::Array(elements) => {
                            for elem in elements.iter_mut() {
                                referenced_instructions.insert_instruct_ref(elem);
                            }
                        }
                        InstructionKind::Index { object, index } => {
                            referenced_instructions.insert_instruct_ref(object);
                            referenced_instructions.insert_instruct_ref(index);
                        }
                        InstructionKind::Phi(phi) => {
                            for (_, instruct_idx) in phi.iter().copied() {
                                referenced_instructions.0.insert(instruct_idx);
                            }
                        }
                    }
                }

                if let Some(terminator) = bb.terminator.as_mut() {
                    match &mut terminator.kind {
                        TerminatorKind::Return { value } => referenced_instructions.insert_instruct_ref(value),
                        TerminatorKind::Goto(_) => {}
                        TerminatorKind::SwitchInt { value, .. } => referenced_instructions.insert_instruct_ref(value),
                        TerminatorKind::Unresolved => {}
                    }
                }
            }

            for bb in function.basic_blocks.iter().copied() {
                let bb = mir.basic_blocks.get_mut_or_panic(bb);

                // Eliminates instructions that are pure && are not under `referenced_instructions`
                // Each elimination increments the number of changes, `changes`
                bb.instructions.retain(|instruct_idx| {
                    if referenced_instructions.0.contains(instruct_idx) || !function.instructions[*instruct_idx].is_pure() {
                        true
                    } else {
                        changes += 1;
                        false
                    }
                });
            }
        }

        changes
    }
}