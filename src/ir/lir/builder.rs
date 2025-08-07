use std::collections::HashMap;

use crate::{compilation_unit::{GlobalScope, VariableIndex}, ir::{lir::{BasicBlock, BasicBlockIdx, ConstValue, Function, InstructionKind, LocationIdx, Operand, OperandKind, Type, LIR}, mir::{self, Constant, FunctionIdx, InstructionIdx, Value, MIR}}};

pub struct LIRBuilder<'mir> {
    mir: &'mir MIR,
    scope: &'mir GlobalScope,
    lir: LIR,
    current_bb: Option<BasicBlockIdx>,
    var_to_location: HashMap<VariableIndex, LocationIdx>,
    instruction_to_location: HashMap<InstructionIdx, LocationIdx>,
    curr_fx_idx: Option<FunctionIdx>, // From MIR
}

impl<'mir> LIRBuilder<'mir> {
    pub fn new(mir: &'mir MIR, scope: &'mir GlobalScope) -> Self {
        Self {
            mir,
            scope,
            lir: LIR::new(),
            current_bb: None,
            var_to_location: HashMap::new(),
            instruction_to_location: HashMap::new(),
            curr_fx_idx: None,
        }
    }

    pub fn build(mut self) -> LIR {
        for (mir_fx_idx, mir_fx) in self.mir.functions.indexed_iter() {
            self.curr_fx_idx = Some(mir_fx_idx);
            let fx_idx = self.lir.functions.push(Function {
                name: mir_fx.name.clone(),
                return_type: mir_fx.return_type.clone().into(),
                basic_blocks: Vec::new(),
                params: Vec::new(),
            });

            for bb_idx in mir_fx.basic_blocks.iter().copied() {
                let bb = self.mir.basic_blocks.get_or_panic(bb_idx);
                let lir_bb = self.set_basic_block();

                for instruct_idx in bb.instructions.iter().copied() {
                    let mir_instruction = &mir_fx.instructions[instruct_idx];
                    

                }
            }
        }
        
        self.lir
    }

    fn set_basic_block(&mut self) -> BasicBlockIdx {
        let bb_idx = self.lir.basic_blocks.push(BasicBlock::default());
        self.current_bb = Some(bb_idx);
        bb_idx
    }

    fn build_operand(&mut self, value: &Value) -> Operand {
        match value {
            Value::Constant(Constant::Int(value)) => Operand {
                ty: Type::Int32,
                kind: OperandKind::Const(ConstValue::Int32(*value)),
            },
            Value::Constant(Constant::Bool(value)) => Operand {
                ty: Type::Bool,
                kind: OperandKind::Const(ConstValue::Int8(if *value { 1 } else { 0 })),
            },
            Value::Constant(Constant::String(value)) => Operand {
                ty: Type::String,
                kind: OperandKind::Const(ConstValue::String(value.clone())),
            },
            Value::Constant(Constant::Usize(value)) => Operand {
                ty: Type::Int8,
                kind: OperandKind::Const(ConstValue::Int8(*value as i8)),
            },
            _ => todo!(),
        }
    }
}