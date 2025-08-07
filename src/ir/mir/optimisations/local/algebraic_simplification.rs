use crate::ir::mir::{basic_block::BasicBlockIdx, optimisations::local::MIRPassLocal, BinOp, Constant, FunctionIdx, InstructionKind, Type, Value, MIR};

pub struct AlgebraicSimplification;

impl AlgebraicSimplification {
    fn simplify_binary_instruction_one_side_known(
        &self,
        operator: BinOp,
        op_type: &Type,
        known_value: i32,
    ) -> Option<i32> {
        let computed_value = if known_value == 0 {
            match operator {
                BinOp::Add | BinOp::Sub | BinOp::BitOr | BinOp::BitShl | BinOp::BitShr => Some(known_value),
                BinOp::Mul | BinOp::BitAnd => Some(0),
                BinOp::Div | BinOp::Mod => todo!("Handle division by zero"),
                _ => None,
            }
        } else if known_value == 1 {
            match operator {
                BinOp::Mul | BinOp::Div => Some(known_value),
                BinOp::Mod => Some(0),
                BinOp::BitAnd => {
                    if matches!(op_type, Type::Bool) {
                        Some(known_value)
                    } else {
                        None
                    }
                }
                BinOp::BitOr => {
                    if matches!(op_type, Type::Bool) {
                        Some(1)
                    } else {
                        None
                    }
                }
                _ => None,
            }
        } else {
            None
        };

        computed_value
    }
}

impl MIRPassLocal for AlgebraicSimplification {
    fn run_on_bb(&mut self, mir: &mut MIR, fx_idx: FunctionIdx, bb_idx: BasicBlockIdx) -> u32 {
        let mut changes = 0;
        let function = mir.functions.get_mut(fx_idx);
        let bb = mir.basic_blocks.get_mut_or_panic(bb_idx);
        for instruct_idx in bb.instructions.iter().copied() {
            let instruction = function.instructions.get_mut(instruct_idx);
            match &mut instruction.kind {
                InstructionKind::Binary { operator, left, right } => {
                    let left_int = left.as_i32();
                    let right_int = right.as_i32();
                    match(left_int, right_int) {
                        (None, Some(right_int)) => {
                            if let Some(result) = self.simplify_binary_instruction_one_side_known(
                                *operator, &instruction.ty, right_int)
                            {
                                instruction.kind = InstructionKind::Value(Value::Constant(Constant::Int(result)));
                                changes += 1;
                            }
                        }
                        (Some(left_int), None) => {
                            if let Some(result) = self.simplify_binary_instruction_one_side_known(
                                *operator, &instruction.ty, left_int)
                            {
                                instruction.kind = InstructionKind::Value(Value::Constant(Constant::Int(result)));
                                changes += 1;
                            }
                        }
                        _ => {}
                    }
                }
                InstructionKind::Unary { .. } => {}
                InstructionKind::Value(_) => {}
                InstructionKind::Call { .. } => {}
                InstructionKind::ArrayInit { .. } => {}
                InstructionKind::ArrayAlloc { .. } => {}
                InstructionKind::IndexVal { .. } => {}
                InstructionKind::ArrayIndex { .. } => {}
                InstructionKind::Index { .. } => {}
                InstructionKind::Phi(_) => {}
            }
        }

        changes
    }
}