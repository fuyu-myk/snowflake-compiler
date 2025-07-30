/**
 * This module handles the logic for copy propagation.
 * 
 * Copy propagation aims to optimise memory utilisation by replacing irrelevant variable assignments with previously calculated values.
 */

use std::collections::HashMap;

use crate::{compilation_unit::FunctionIndex, ir::mir::{basic_block::BasicBlockIdx, optimisations::local::MIRPassLocal, InstructionIdx, InstructionKind, TerminatorKind, MIR}};


pub struct CopyPropagation;

impl MIRPassLocal for CopyPropagation {
    fn run_on_bb(&mut self, mir: &mut MIR, fx_idx: FunctionIndex, bb_idx: BasicBlockIdx) -> u32 {
        let mut changes = 0;
        let mut copies: HashMap<InstructionIdx, InstructionIdx> = HashMap::new();
        let function = mir.functions.get_mut(fx_idx);
        let bb = mir.basic_blocks.get_mut_or_panic(bb_idx);

        for instruct_idx in bb.instructions.iter().copied() {
            let instruction = &mut function.instructions[instruct_idx];
            match &mut instruction.kind {
                InstructionKind::Value(value) => {
                    if let Some(instruct_ref) = value.as_instruct_ref() {
                        copies.insert(instruct_idx, instruct_ref);
                    }
                }
                InstructionKind::Binary { left, right, .. } => {
                    if left.replace_with_copied_ref(&copies) {
                        changes += 1;
                    }

                    if right.replace_with_copied_ref(&copies) {
                        changes += 1;
                    }
                }
                InstructionKind::Unary { operand, .. } => {
                    if operand.replace_with_copied_ref(&copies) {
                        changes += 1;
                    }
                }
                InstructionKind::Call { args, .. } => {
                    for arg in args.iter_mut() {
                        if arg.replace_with_copied_ref(&copies) {
                            changes += 1;
                        }
                    }
                }
                InstructionKind::Phi(_) => {}
            }
        }

        if let Some(terminator) = bb.terminator.as_mut() {
            match &mut terminator.kind {
                TerminatorKind::Return { value } => {
                    if value.replace_with_copied_ref(&copies) {
                        changes += 1;
                    }
                }
                TerminatorKind::Goto(_) => {}
                TerminatorKind::SwitchInt { value, .. } => {
                    if value.replace_with_copied_ref(&copies) {
                        changes += 1;
                    }
                }
                TerminatorKind::Unresolved => {}
            }
        }

        changes
    }
}