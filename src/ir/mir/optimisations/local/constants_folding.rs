use std::{collections::HashMap, ops::{Deref, DerefMut}};

use crate::{ir::mir::{basic_block::BasicBlockIdx, optimisations::local::MIRPassLocal, BinOp, Constant, FunctionIdx, Instruction, InstructionIdx, InstructionKind, TerminatorKind, UnOp, Value, MIR}, text::span::TextSpan};


struct ComputedConstants(HashMap<InstructionIdx, Value>);

impl ComputedConstants {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    fn is_constant(&self, value: &Value) -> bool {
        value.is_const() || {
            let instruct_idx = value.as_instruct_ref();
            match instruct_idx.as_ref() {
                Some(idx) => self.0.get(idx).is_some(),
                None => false,
            }
        }
    }

    fn get_constant_int(&self, value: &Value) -> Option<i32> {
        let const_value = self.get_constant_value(value)?;
        const_value.as_i32()
    }

    fn get_constant_value(&self, value: &Value) -> Option<Value> {
        match value {
            Value::Constant(Constant::Int(value)) => Some(Value::Constant(Constant::Int(*value))),
            Value::Constant(Constant::Bool(value)) => Some(Value::Constant(Constant::Bool(*value))),
            Value::Constant(Constant::String(value)) => Some(Value::Constant(Constant::String(value.clone()))),
            Value::Constant(Constant::Usize(value)) => Some(Value::Constant(Constant::Usize(*value))),
            Value::InstructionRef(idx) => match self.0.get(idx) {
                Some(value) => self.get_constant_value(value),
                None => None,
            },
            Value::ParamRef(_) => None,
            Value::Constant(Constant::Void) => Some(Value::Constant(Constant::Void)),
        }
    }
}

impl Deref for ComputedConstants {
    type Target = HashMap<InstructionIdx, Value>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for ComputedConstants {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

pub struct ConstantsFolding;

impl MIRPassLocal for ConstantsFolding {
    fn run_on_bb(&mut self, mir: &mut MIR, fx_idx: FunctionIdx, bb_idx: BasicBlockIdx) -> u32 {
        let mut changes = 0;
        let mut constants = ComputedConstants::new();
        let function = mir.functions.get_mut(fx_idx);
        let bb = mir.basic_blocks.get_mut_or_panic(bb_idx);

        for instruct_idx in bb.instructions.iter().copied() {
            let instruction = function.instructions.get_mut(instruct_idx);
            match &mut instruction.kind {
                InstructionKind::Value(value) => {
                    if constants.is_constant(value) {
                        constants.insert(instruct_idx, value.clone());
                    }
                }
                InstructionKind::Binary { left, right, operator } => {
                    let left_int = constants.get_constant_int(left);
                    let right_int = constants.get_constant_int(right);
                    if let (Some(left_int), Some(right_int)) = (left_int, right_int) {
                        let result = match operator {
                            BinOp::Add => left_int.wrapping_add(right_int),
                            BinOp::Sub => left_int.wrapping_sub(right_int),
                            BinOp::Mul => left_int.wrapping_mul(right_int),
                            BinOp::Div => {
                                if right_int == 0 {
                                    // Division by zero should have been caught at compile time
                                    // Skip optimization for safety
                                    continue;
                                }
                                left_int / right_int
                            },
                            BinOp::Mod => {
                                if right_int == 0 {
                                    // Modulo by zero should have been caught at compile time
                                    // Skip optimization for safety
                                    continue;
                                }
                                left_int % right_int
                            },
                            BinOp::BitAnd => left_int & right_int,
                            BinOp::BitOr => left_int | right_int,
                            BinOp::BitXor => left_int ^ right_int,
                            BinOp::BitShl => left_int << right_int,
                            BinOp::BitShr => left_int >> right_int,
                            BinOp::Eq => (left_int == right_int) as i32,
                            BinOp::Neq => (left_int != right_int) as i32,
                            BinOp::Lt => (left_int < right_int) as i32,
                            BinOp::Gt => (left_int > right_int) as i32,
                            BinOp::Leq => (left_int <= right_int) as i32,
                            BinOp::Geq => (left_int >= right_int) as i32,
                        };

                        let new_value = Value::Constant(Constant::Int(result));
                        constants.insert(instruct_idx, new_value.clone());
                        changes += 1;
                        *instruction = Instruction::new(InstructionKind::Value(new_value), instruction.ty.clone(), TextSpan::default());
                    }
                }
                InstructionKind::Unary { operand, operator } => {
                    let operand_int = constants.get_constant_int(operand);
                    if let Some(operand_int) = operand_int {
                        let result = match operator {
                            UnOp::Neg => operand_int.wrapping_neg(),
                            UnOp::Not => !operand_int,
                        };

                        let new_value = Value::Constant(Constant::Int(result));
                        constants.insert(instruct_idx, new_value.clone());
                        changes += 1;
                        *instruction = Instruction::new(InstructionKind::Value(new_value), instruction.ty.clone(), TextSpan::default());
                    }
                }
                InstructionKind::Call { args, .. } => {
                    for arg in args.iter_mut() {
                        if let Some(value) = constants.get_constant_value(arg) {
                            if arg.replace_if_unequal(value) {
                                changes += 1;
                            }
                        }
                    }
                }
                InstructionKind::ArrayInit { elements } => {
                    for elem in elements.iter_mut() {
                        if let Some(value) = constants.get_constant_value(elem) {
                            if elem.replace_if_unequal(value) {
                                changes += 1;
                            }
                        }
                    }
                }
                InstructionKind::ArrayIndex { array, index } => {
                    if let Some(value) = constants.get_constant_value(array) {
                        if array.replace_if_unequal(value) {
                            changes += 1;
                        }
                    }
                    if let Some(value) = constants.get_constant_value(index) {
                        if index.replace_if_unequal(value) {
                            changes += 1;
                        }
                    }
                }
                InstructionKind::Phi(_) | InstructionKind::IndexVal { .. } | InstructionKind::ArrayAlloc { .. } => {}
            }
        }

        if let Some(terminator) = bb.terminator.as_mut() {
            match &mut terminator.kind {
                TerminatorKind::Return { value } => {
                    if let Some(const_value) = constants.get_constant_value(value) {
                        if value.replace_if_unequal(const_value) {
                            changes += 1;
                        }
                    }
                }
                TerminatorKind::Goto(_) => {}
                TerminatorKind::SwitchInt { value, .. } => {
                    if let Some(const_value) = constants.get_constant_value(value) {
                        if value.replace_if_unequal(const_value) {
                            changes += 1;
                        }
                    }
                }
                TerminatorKind::Assert { condition, .. } => {
                    if let Some(const_value) = constants.get_constant_value(condition) {
                        if condition.replace_if_unequal(const_value) {
                            changes += 1;
                        }
                    }
                }
                TerminatorKind::Unresolved => {}
            }
        }

        changes
    }
}