use std::collections::HashMap;

use crate::ir::mir::{InstructionIdx, InstructionKind, MIR, Value};

use super::super::MIRPass;


pub struct PhiElimination;

impl MIRPass for PhiElimination {
    fn run(&mut self, mir: &mut MIR) -> u32 {
        let mut changes = 0;
        
        for function in mir.functions.iter_mut() {
            let mut phi_replacements: HashMap<InstructionIdx, InstructionIdx> = HashMap::new();
            
            // First pass: Identify trivial phi nodes and collect replacements
            for bb_idx in function.basic_blocks.iter().copied() {
                let bb = mir.basic_blocks.get_or_panic(bb_idx);
                let instructions = bb.instructions.clone();
                
                for &instr_idx in instructions.iter() {
                    let instruction = &function.instructions[instr_idx];
                    
                    if let InstructionKind::Phi(phi) = &instruction.kind {
                        if let Some(replacement) = phi.is_trivial(instr_idx) {
                            phi_replacements.insert(instr_idx, replacement);
                            changes += 1;
                        }
                    }
                }
            }
            
            // Second pass: Replace trivial phi references with their operands
            let instruction_indices: Vec<InstructionIdx> = function.instructions.indices().collect();
            for instr_idx in instruction_indices {
                let instruction = &mut function.instructions[instr_idx];
                
                match &mut instruction.kind {
                    InstructionKind::Binary { left, right, .. } => {
                        Self::replace_value_refs(left, &phi_replacements);
                        Self::replace_value_refs(right, &phi_replacements);
                    }
                    InstructionKind::Unary { operand, .. } => {
                        Self::replace_value_refs(operand, &phi_replacements);
                    }
                    InstructionKind::Call { args, .. } => {
                        for arg in args.iter_mut() {
                            Self::replace_value_refs(arg, &phi_replacements);
                        }
                    }
                    InstructionKind::Value(value) => {
                        Self::replace_value_refs(value, &phi_replacements);
                    }
                    InstructionKind::ArrayAlloc { size, .. } => {
                        Self::replace_value_refs(size, &phi_replacements);
                    }
                    InstructionKind::ArrayInit { elements } => {
                        for element in elements.iter_mut() {
                            Self::replace_value_refs(element, &phi_replacements);
                        }
                    }
                    InstructionKind::ArrayIndex { array, index, .. } => {
                        Self::replace_value_refs(array, &phi_replacements);
                        Self::replace_value_refs(index, &phi_replacements);
                    }
                    InstructionKind::IndexVal { array_len } => {
                        Self::replace_value_refs(array_len, &phi_replacements);
                    }
                    InstructionKind::Tuple { elements } => {
                        for element in elements.iter_mut() {
                            Self::replace_value_refs(element, &phi_replacements);
                        }
                    }
                    InstructionKind::TupleIndex { tuple, index } => {
                        Self::replace_value_refs(tuple, &phi_replacements);
                        Self::replace_value_refs(index, &phi_replacements);
                    }
                    InstructionKind::Phi(phi) => {
                        // Update phi operands to point to replacements
                        for (_, operand_ref) in phi.operands.iter_mut() {
                            if let Some(&replacement) = phi_replacements.get(operand_ref) {
                                *operand_ref = replacement;
                            }
                        }
                    }
                }
            }
            
            // Third pass: Remove trivial phi instructions by converting them to move instructions
            for (&phi_idx, &replacement_idx) in phi_replacements.iter() {
                let new_value = Value::InstructionRef(replacement_idx);
                
                function.instructions[phi_idx].kind = InstructionKind::Value(new_value);
            }
        }
        
        changes
    }
}

impl PhiElimination {
    fn replace_value_refs(value: &mut Value, replacements: &HashMap<InstructionIdx, InstructionIdx>) {
        if let Value::InstructionRef(instr_idx) = value {
            if let Some(&replacement) = replacements.get(instr_idx) {
                *instr_idx = replacement;
            }
        }
    }
}
