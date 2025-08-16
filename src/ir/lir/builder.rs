use std::collections::HashMap;

use snowflake_compiler::Idx;

use crate::{compilation_unit::{GlobalScope, VariableIndex}, ir::{lir::{BasicBlock, BasicBlockIdx, ConstValue, Function, Instruction, InstructionKind, Location, LocationIdx, Operand, OperandKind, Terminator, Type, LIR, FunctionIdx}, mir::{self, BinOp, Constant, FunctionIdx as MirFunctionIdx, InstructionIdx, Value, MIR}}};

pub struct LIRBuilder<'mir> {
    mir: &'mir MIR,
    scope: &'mir GlobalScope,
    lir: LIR,
    current_bb: Option<BasicBlockIdx>,
    var_to_location: HashMap<VariableIndex, LocationIdx>,
    instruction_to_location: HashMap<InstructionIdx, LocationIdx>,
    param_to_location: HashMap<usize, LocationIdx>,
    curr_fx_idx: Option<MirFunctionIdx>, // From MIR
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
            param_to_location: HashMap::new(),
            curr_fx_idx: None,
        }
    }

    pub fn build(mut self) -> LIR {
        for (mir_fx_idx, mir_fx) in self.mir.functions.indexed_iter() {
            self.curr_fx_idx = Some(mir_fx_idx);
            
            // Clear mappings for new function
            self.var_to_location.clear();
            self.instruction_to_location.clear();
            self.param_to_location.clear();
            
            // Create parameter locations
            let mut param_locations = Vec::new();
            for (param_idx, _param_var) in mir_fx.params.iter().enumerate() {
                let param_type = mir_fx.locals.iter()
                    .find_map(|(param_instruct_idx, _var_idx)| Some(mir_fx.instructions.get(*param_instruct_idx).ty.clone()))
                    .map(|ty| ty.into())
                    .unwrap_or(Type::Int32); // Default to Int32 if type not found
                let location = self.create_location(param_type);
                self.param_to_location.insert(param_idx, location);
                param_locations.push(location);
            }
            
            let fx_idx = self.lir.functions.push(Function {
                name: mir_fx.name.clone(),
                return_type: mir_fx.return_type.clone().into(),
                basic_blocks: Vec::new(),
                params: param_locations,
            });

            for bb_idx in mir_fx.basic_blocks.iter().copied() {
                let bb = self.mir.basic_blocks.get_or_panic(bb_idx);
                let _lir_bb = self.set_basic_block();

                for instruct_idx in bb.instructions.iter().copied() {
                    let mir_instruction = &mir_fx.instructions[instruct_idx];
                    let instruction = match &mir_instruction.kind {
                        mir::InstructionKind::Binary { operator, left, right } => {
                            let left = self.build_operand(left);
                            let right = self.build_operand(right);
                            match operator {
                                BinOp::Add => InstructionKind::Add {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::Sub => InstructionKind::Sub {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::Mul => InstructionKind::Mul {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::Div => InstructionKind::Div {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::Mod => InstructionKind::Mod {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::BitAnd => InstructionKind::And {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::BitOr => InstructionKind::Or {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::BitXor => InstructionKind::Xor {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::BitShl => InstructionKind::Shl {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::BitShr => InstructionKind::Shr {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::Eq => InstructionKind::Eq {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::Neq => InstructionKind::Ne {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::Lt => InstructionKind::Lt {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::Gt => InstructionKind::Gt {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::Leq => InstructionKind::Le {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::Geq => InstructionKind::Ge {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                            }
                        }
                        mir::InstructionKind::Unary { operator, operand } => {
                            let operand = self.build_operand(operand);
                            match operator {
                                mir::UnOp::Neg => InstructionKind::Neg {
                                    target: self.get_ref_location(instruct_idx),
                                    operand,
                                },
                                mir::UnOp::Not => InstructionKind::Not {
                                    target: self.get_ref_location(instruct_idx),
                                    operand,
                                },
                            }
                        }
                        mir::InstructionKind::Call { fx_idx, args } => {
                            let args: Vec<Operand> = args.iter()
                                .map(|arg| self.build_operand(arg))
                                .collect();
                            
                            let target = if mir_instruction.ty != mir::Type::Void {
                                Some(self.get_ref_location(instruct_idx))
                            } else {
                                None
                            };
                            
                            InstructionKind::Call {
                                target,
                                function: FunctionIdx::new(fx_idx.as_index()), // Convert MIR function index to LIR
                                args,
                            }
                        }
                        mir::InstructionKind::Value(value) => InstructionKind::Move {
                            target: self.get_ref_location(instruct_idx),
                            source: self.build_operand(value),
                        },
                        mir::InstructionKind::ArrayAlloc { element_type, size } => {
                            let size_operand = self.build_operand(size);
                            InstructionKind::ArrayAlloc {
                                target: self.get_ref_location(instruct_idx),
                                element_type: element_type.clone().into(),
                                size: size_operand,
                            }
                        }
                        mir::InstructionKind::ArrayInit { elements } => {
                            // For array initialization, we need to allocate space and then store each element
                            // This is a simplified approach
                            let target = self.get_ref_location(instruct_idx);
                            
                            // Create a simple move instruction for now
                            // todo: instructions to initialise each element
                            if let Some(first_element) = elements.first() {
                                InstructionKind::Move {
                                    target,
                                    source: self.build_operand(first_element),
                                }
                            } else {
                                InstructionKind::Nop
                            }
                        }
                        mir::InstructionKind::ArrayIndex { array, index } => {
                            let array_operand = self.build_operand(array);
                            let index_operand = self.build_operand(index);
                            InstructionKind::ArrayIndex {
                                target: self.get_ref_location(instruct_idx),
                                array: array_operand,
                                index: index_operand,
                            }
                        }
                        mir::InstructionKind::IndexVal { array_len } => {
                            let array_operand = self.build_operand(array_len);
                            InstructionKind::ArrayLength {
                                target: self.get_ref_location(instruct_idx),
                                length: array_operand,
                            }
                        }
                        mir::InstructionKind::Phi(phi_node) => {
                            // Phi handled through move instructions at basic block boundaries
                            // For now, just create a move from the first operand if available
                            if let Some((_, first_operand_idx)) = phi_node.operands.first() {
                                InstructionKind::Move {
                                    target: self.get_ref_location(instruct_idx),
                                    source: Operand {
                                        ty: self.get_current_fx().instructions.get(*first_operand_idx).ty.clone().into(),
                                        kind: OperandKind::Location(
                                            self.instruction_to_location.get(first_operand_idx)
                                                .copied()
                                                .unwrap_or_else(|| self.create_temp_location(*first_operand_idx))
                                        ),
                                    },
                                }
                            } else {
                                // No operands, create a no-op
                                InstructionKind::Nop
                            }
                        }
                    };
                    self.current_basic_block().instructions.push(Instruction {
                        kind: instruction,
                    });
                }

                let terminator = match &bb.terminator().kind {
                    mir::TerminatorKind::Return { value } => {
                        let value = match value {
                            Value::Constant(Constant::Void) => None,
                            _ => Some(self.build_operand(&value)),
                        };
                        Terminator::Return { value }
                    }
                    mir::TerminatorKind::Goto(target) => Terminator::Goto {
                        target: BasicBlockIdx::new(target.as_index()),
                    },
                    mir::TerminatorKind::SwitchInt { value, targets, default } => {
                        let value_operand = self.build_operand(value);
                        let switch_targets: Vec<(ConstValue, BasicBlockIdx)> = targets.iter()
                            .map(|(val, bb_idx)| {
                                (ConstValue::Int32(*val), BasicBlockIdx::new(bb_idx.as_index()))
                            })
                            .collect();
                        
                        Terminator::Switch {
                            value: value_operand,
                            targets: switch_targets,
                            default_target: BasicBlockIdx::new(default.as_index()),
                        }
                    }
                    mir::TerminatorKind::Assert { condition, message, default } => {
                        // Convert assert to a conditional branch that either continues or goes to unreachable
                        let condition_operand = self.build_operand(condition);
                        let unreachable_bb = self.lir.basic_blocks.push(BasicBlock {
                            instructions: Vec::new(),
                            terminator: Some(Terminator::Unreachable { error: message.clone() }),
                        });
                        
                        Terminator::Branch {
                            condition: condition_operand,
                            true_target: BasicBlockIdx::new(default.as_index()),
                            false_target: unreachable_bb,
                        }
                    }
                    mir::TerminatorKind::Unresolved => Terminator::Unreachable {
                        error: "Unresolved terminator".to_string(),
                    },
                };

                self.current_basic_block().terminator = Some(terminator);
                let fx = self.lir.functions.get_mut(fx_idx);
                fx.basic_blocks.push(self.current_bb.expect("No current basic block set"));
            }
        }
        
        self.lir
    }

    fn set_basic_block(&mut self) -> BasicBlockIdx {
        let bb_idx = self.lir.basic_blocks.push(BasicBlock::default());
        self.current_bb = Some(bb_idx);
        bb_idx
    }

    fn current_basic_block(&mut self) -> &mut BasicBlock {
        self.lir.basic_blocks.get_mut(self.current_bb.expect("No current basic block set"))
    }

    fn build_operand(&mut self, value: &Value) -> Operand {
        match value {
            Value::Constant(Constant::Int(value)) => Operand {
                ty: Type::Int32,
                kind: OperandKind::Const(ConstValue::Int32(*value)),
            },
            Value::Constant(Constant::Bool(value)) => Operand {
                ty: Type::Bool,
                kind: OperandKind::Const(ConstValue::Bool(*value)),
            },
            Value::Constant(Constant::String(value)) => Operand {
                ty: Type::String,
                kind: OperandKind::Const(ConstValue::String(value.clone())),
            },
            Value::Constant(Constant::Usize(value)) => Operand {
                ty: Type::UInt64,
                kind: OperandKind::Const(ConstValue::UInt64(*value as u64)),
            },
            Value::Constant(Constant::Void) => Operand {
                ty: Type::Void,
                kind: OperandKind::Const(ConstValue::Null),
            },
            Value::InstructionRef(instr_idx) => {
                let instruction = self.get_current_fx().instructions.get(*instr_idx);
                let ty = instruction.ty.clone().into();
                let location = self.instruction_to_location.get(instr_idx)
                    .copied()
                    .unwrap_or_else(|| self.create_temp_location(*instr_idx));
                
                Operand {
                    ty,
                    kind: OperandKind::Location(location),
                }
            },
            Value::ParamRef(param_idx) => {
                // Use the pre-allocated parameter location
                let location = self.param_to_location.get(param_idx)
                    .copied()
                    .expect("Parameter location should have been created");
                let param_loc_idx = self.param_to_location.get(param_idx)
                    .copied()
                    .unwrap_or_else(|| {
                        panic!("Parameter index {} not found in param_to_location", param_idx);
                    });
                let ty = self.lir.locations.get(param_loc_idx).ty.clone().into();

                Operand {
                    ty,
                    kind: OperandKind::Location(location),
                }
            },
        }
    }

    fn get_ref_location(&mut self, instruction_idx: InstructionIdx) -> LocationIdx {
        let instruction = self.get_current_fx().instructions.get(instruction_idx);
        let ty = instruction.ty.clone().into();
        let aliased_var = self.get_current_fx().locals.get(&instruction_idx).copied();

        match aliased_var {
            Some(aliased_var) => match self.var_to_location.get(&aliased_var) {
                Some(location) => *location,
                None => {
                    let location = self.create_location(ty);
                    self.instruction_to_location.insert(instruction_idx, location);
                    location
                }
            }
            None => match self.instruction_to_location.get(&instruction_idx) {
                Some(location) => *location,
                None => {
                    let location = self.create_location(ty);
                    self.instruction_to_location.insert(instruction_idx, location);
                    location
                }
            }
        }
    }

    fn get_current_fx(&self) -> &mir::Function {
        self.mir.functions.get(self.curr_fx_idx.expect("No current function found"))
    }
    
    fn create_location(&mut self, ty: Type) -> LocationIdx {
        self.lir.locations.push_with_index(|idx| Location { ty, idx })
    }
    
    fn create_temp_location(&mut self, instruction_idx: InstructionIdx) -> LocationIdx {
        let instruction = self.get_current_fx().instructions.get(instruction_idx);
        let ty = instruction.ty.clone().into();
        let location = self.create_location(ty);
        self.instruction_to_location.insert(instruction_idx, location);
        location
    }
}