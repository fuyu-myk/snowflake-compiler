use std::collections::HashMap;

use snowflake_common::Idx;
use snowflake_front::compilation_unit::{GlobalScope, VariableIndex};

use crate::{ir::{lir::{BasicBlock, BasicBlockIdx, ConstValue, Function, Instruction, InstructionKind, Location, LocationIdx, Operand, OperandKind, Terminator, Type, LIR, FunctionIdx}, mir::{self, BinOp, Constant, FunctionIdx as MirFunctionIdx, InstructionIdx, Value, MIR}}};

pub struct LIRBuilder<'mir> {
    mir: &'mir MIR,
    scope: &'mir GlobalScope,
    lir: LIR,
    current_bb: Option<BasicBlockIdx>,
    var_to_location: HashMap<VariableIndex, LocationIdx>,
    instruction_to_location: HashMap<InstructionIdx, LocationIdx>,
    param_to_location: HashMap<usize, LocationIdx>,
    mir_to_lir_bb: HashMap<usize, BasicBlockIdx>,
    curr_fx_idx: Option<MirFunctionIdx>, // From MIR
    panic_blocks: Vec<BasicBlockIdx>,
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
            mir_to_lir_bb: HashMap::new(),
            curr_fx_idx: None,
            panic_blocks: Vec::new(),
        }
    }

    pub fn build(mut self) -> LIR {
        for (mir_fx_idx, mir_fx) in self.mir.functions.indexed_iter() {
            self.curr_fx_idx = Some(mir_fx_idx);
            
            // Clear mappings for new function
            self.var_to_location.clear();
            self.instruction_to_location.clear();
            self.param_to_location.clear();
            self.mir_to_lir_bb.clear();
            self.panic_blocks.clear();
            
            // Create parameter locations
            let mut param_locations = Vec::new();
            for (param_idx, param_var) in mir_fx.params.iter().enumerate() {
                let param_type = self.scope.get_variable_type(param_var)
                    .map(|common_ty| {
                        let mir_ty: mir::Type = common_ty.into();
                        mir_ty.into()
                    })
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

            // PASS 1: Create all basic blocks and build mapping
            for bb_idx in mir_fx.basic_blocks.iter().copied() {
                let lir_bb = self.set_basic_block();
                self.mir_to_lir_bb.insert(bb_idx.index, lir_bb);
            }

            // PASS 2: Process non-phi instructions
            let mut phi_instructions = Vec::new(); // Collect phi instructions for later processing
            
            for bb_idx in mir_fx.basic_blocks.iter().copied() {
                let bb = self.mir.basic_blocks.get_or_panic(bb_idx);
                let lir_bb = *self.mir_to_lir_bb.get(&bb_idx.index).unwrap();
                self.current_bb = Some(lir_bb);

                for instruct_idx in bb.instructions.iter().copied() {
                    let mir_instruction = &mir_fx.instructions[instruct_idx];
                    
                    if let mir::InstructionKind::Phi(_) = &mir_instruction.kind {
                        let _phi_loc = self.get_ref_location(instruct_idx);
                        phi_instructions.push((bb_idx, instruct_idx, lir_bb));
                        continue;
                    }
                    
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
                                BinOp::LogicalAnd => InstructionKind::And {
                                    target: self.get_ref_location(instruct_idx),
                                    left,
                                    right,
                                },
                                BinOp::LogicalOr => InstructionKind::Or {
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
                        mir::InstructionKind::Value(value) => {
                            let source = self.build_operand(value);
                            let target = self.get_ref_location_for_move(instruct_idx, &source);
                            InstructionKind::Move {
                                target,
                                source,
                            }
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
                            let target = self.get_ref_location_for_array_init(instruct_idx, elements.len());
                            
                            if elements.is_empty() {
                                // Empty array initialization
                                InstructionKind::Nop
                            } else {
                                // Determine element type from first element
                                let element_type = match elements.first() {
                                    Some(first_element) => {
                                        match first_element {
                                            mir::Value::Constant(constant) => {
                                                match constant {
                                                    mir::Constant::Int(_) => Type::Int32,
                                                    mir::Constant::Float(_) => Type::Float32,
                                                    mir::Constant::Bool(_) => Type::Bool,
                                                    mir::Constant::String(_) => Type::String,
                                                    mir::Constant::Usize(_) => Type::UInt64,
                                                    mir::Constant::Void => Type::Void,
                                                }
                                            }
                                            _ => Type::Int32, // Default fallback
                                        }
                                    }
                                    None => Type::Int32, // Default fallback
                                };
                                
                                for (index, element) in elements.iter().enumerate() {
                                    let index_operand = Operand {
                                        ty: Type::UInt64,
                                        kind: OperandKind::Const(ConstValue::UInt64(index as u64)),
                                    };
                                    
                                    let array_operand = Operand {
                                        ty: Type::Array { 
                                            element_type: Box::new(element_type.clone()), 
                                            size: elements.len() 
                                        },
                                        kind: OperandKind::Location(target),
                                    };
                                    
                                    let value_operand = self.build_operand(element);
                                    
                                    let store_instruction = InstructionKind::ObjectStore {
                                        object: array_operand,
                                        index: index_operand,
                                        value: value_operand,
                                    };
                                    
                                    self.current_basic_block().instructions.push(Instruction {
                                        kind: store_instruction,
                                    });
                                }
                                
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
                        mir::InstructionKind::ArrayStore { array, index, value } => {
                            let array_operand = self.build_operand(array);
                            let index_operand = self.build_operand(index);
                            let value_operand = self.build_operand(value);
                            InstructionKind::ObjectStore {
                                object: array_operand,
                                index: index_operand,
                                value: value_operand,
                            }
                        }
                        mir::InstructionKind::IndexVal { array_len } => {
                            let array_operand = self.build_operand(array_len);
                            InstructionKind::ArrayLength {
                                target: self.get_ref_location(instruct_idx),
                                length: array_operand,
                            }
                        }
                        mir::InstructionKind::Object { fields, .. } => {
                            let field_operands: Vec<Operand> = fields.iter()
                                .map(|field| self.build_operand(field))
                                .collect();
                            
                            let object_type = Type::Object {
                                element_types: field_operands.iter().map(|op| Box::new(op.ty.clone())).collect()
                            };
                            
                            InstructionKind::Object {
                                target: self.get_ref_location_with_type(instruct_idx, object_type),
                                elements: field_operands,
                            }
                        }
                        mir::InstructionKind::Field { object: tuple, field } => {
                            let tuple_operand = self.build_operand(tuple);
                            let field_operand = self.build_operand(field);
                            
                            let result_ty = if let OperandKind::Const(ConstValue::Int32(field_idx)) = &field_operand.kind {
                                match &tuple_operand.ty {
                                    Type::Object { element_types } => {
                                        let idx = *field_idx as usize;
                                        if idx < element_types.len() {
                                            element_types[idx].as_ref().clone()
                                        } else {
                                            // Fallback to instruction type
                                            self.get_current_fx().instructions.get(instruct_idx).ty.clone().into()
                                        }
                                    }
                                    _ => self.get_current_fx().instructions.get(instruct_idx).ty.clone().into()
                                }
                            } else {
                                self.get_current_fx().instructions.get(instruct_idx).ty.clone().into()
                            };
                            
                            InstructionKind::FieldAccess {
                                target: self.get_ref_location_with_type(instruct_idx, result_ty),
                                object: tuple_operand,
                                field: field_operand,
                            }
                        }
                        mir::InstructionKind::ObjectStore { object, field, value } => {
                            let tuple_operand = self.build_operand(object);
                            let field_operand = self.build_operand(field);
                            let value_operand = self.build_operand(value);
                            InstructionKind::ObjectStore {
                                object: tuple_operand,
                                index: field_operand,
                                value: value_operand,
                            }
                        }
                        mir::InstructionKind::Phi(_) => {
                            panic!("Phi instructions should be processed in a separate pass");
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
                        target: *self.mir_to_lir_bb.get(&target.as_index()).expect("Target basic block not found in mapping"),
                    },
                    mir::TerminatorKind::SwitchInt { value, targets, default } => {
                        let value_operand = self.build_operand(value);
                        let switch_targets: Vec<(ConstValue, BasicBlockIdx)> = targets.iter()
                            .map(|(val, bb_idx)| {
                                (ConstValue::Int32(*val), *self.mir_to_lir_bb.get(&bb_idx.as_index()).expect("Target basic block not found in mapping"))
                            })
                            .collect();
                        
                        Terminator::Switch {
                            value: value_operand,
                            targets: switch_targets,
                            default_target: *self.mir_to_lir_bb.get(&default.as_index()).expect("Default basic block not found in mapping"),
                        }
                    }
                    mir::TerminatorKind::Assert { condition, check, message, default } => {
                        let condition_operand = self.build_operand(condition);
                        let check_operand = Operand {
                            ty: Type::Bool,
                            kind: OperandKind::Const(ConstValue::Bool(*check)),
                        };
                        
                        // If condition == check, continue to default block
                        // If condition != check, panic with message
                        
                        let comparison_result_loc = self.create_location(Type::Bool);
                        
                        self.current_basic_block().instructions.push(Instruction {
                            kind: InstructionKind::Eq {
                                target: comparison_result_loc,
                                left: condition_operand,
                                right: check_operand,
                            },
                        });
                        
                        let panic_bb = self.lir.basic_blocks.push(BasicBlock::default());
                        self.panic_blocks.push(panic_bb);
                        
                        self.lir.basic_blocks[panic_bb].terminator = Some(Terminator::Panic {
                            message: message.message(self.get_current_fx(), self.scope),
                        });
                        
                        let default_lir_bb = self.mir_to_lir_bb.get(&default.as_index())
                            .copied()
                            .unwrap_or_else(|| panic!("Default basic block {} not found in mapping. Available mappings: {:?}", default.as_index(), self.mir_to_lir_bb));
                        
                        Terminator::Branch {
                            condition: Operand {
                                ty: Type::Bool,
                                kind: OperandKind::Location(comparison_result_loc),
                            },
                            true_target: default_lir_bb,
                            false_target: panic_bb,
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
            
            let fx = self.lir.functions.get_mut(fx_idx);
            fx.basic_blocks.extend(self.panic_blocks.iter().copied());
            
            // Second pass: Process phi instructions
            for (_bb_idx, instruct_idx, lir_bb_idx) in phi_instructions {
                let mir_instruction = &mir_fx.instructions[instruct_idx];
                if let mir::InstructionKind::Phi(phi_data) = &mir_instruction.kind {
                    let phi_loc = *self.instruction_to_location.get(&instruct_idx)
                        .expect("Phi instruction location should exist");
                    
                    let mut operands = Vec::new();
                    for (pred_bb, pred_inst_idx) in &phi_data.operands {
                        if let Some(pred_loc) = self.instruction_to_location.get(pred_inst_idx) {
                            let operand = Operand {
                                ty: mir_fx.instructions[*pred_inst_idx].ty.clone().into(),
                                kind: OperandKind::Location(*pred_loc),
                            };

                            let lir_pred_bb = *self.mir_to_lir_bb.get(&pred_bb.index).unwrap();
                            operands.push((lir_pred_bb, operand));
                        }
                    }
                    
                    let lir_instruction = Instruction {
                        kind: InstructionKind::Phi {
                            target: phi_loc,
                            operands,
                        },
                    };
                    
                    self.lir.basic_blocks[lir_bb_idx].instructions.insert(0, lir_instruction);
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

    fn current_basic_block(&mut self) -> &mut BasicBlock {
        self.lir.basic_blocks.get_mut(self.current_bb.expect("No current basic block set"))
    }

    fn build_operand(&mut self, value: &Value) -> Operand {
        match value {
            Value::Constant(Constant::Int(value)) => Operand {
                ty: Type::Int32,
                kind: OperandKind::Const(ConstValue::Int32(*value)),
            },
            Value::Constant(Constant::Float(value)) => Operand {
                ty: Type::Float32,
                kind: OperandKind::Const(ConstValue::Float32(*value)),
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
                let location = self.instruction_to_location.get(instr_idx)
                    .copied()
                    .unwrap_or_else(|| self.create_temp_location(*instr_idx));
                
                let instruction = self.get_current_fx().instructions.get(*instr_idx);
                let instr_ty: Type = instruction.ty.clone().into();
                let location_ty = &self.lir.locations[location].ty;
                
                let ty = match (location_ty, &instr_ty) {
                    (Type::Object { element_types: loc_els }, Type::Object { element_types: instr_els }) => {
                        if loc_els.len() >= instr_els.len() {
                            location_ty.clone()
                        } else {
                            instr_ty
                        }
                    }
                    (Type::Object { .. }, _) => location_ty.clone(),
                    _ => instr_ty
                };
                
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
                Some(&location) => {
                    let current_ty = &self.lir.locations[location].ty;
                    let needs_update = matches!(current_ty, Type::Int32 | Type::UInt64) && 
                        matches!(&ty, Type::Object { .. });
                    
                    let needs_nested_update = match (current_ty, &ty) {
                        (Type::Object { element_types: current_els }, Type::Object { element_types: new_els }) => {
                            new_els.len() > current_els.len() || 
                            new_els.iter().zip(current_els.iter()).any(|(new_el, curr_el)| {
                                matches!((curr_el.as_ref(), new_el.as_ref()),
                                    (Type::Object { element_types: curr_nested }, Type::Object { element_types: new_nested })
                                    if new_nested.len() > curr_nested.len())
                            })
                        }
                        _ => false
                    };
                    
                    if needs_update || needs_nested_update {
                        self.lir.locations[location].ty = ty.clone();
                    }
                    location
                }
                None => {
                    let location = self.create_location(ty);
                    self.var_to_location.insert(aliased_var, location);
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

    fn get_ref_location_with_type(&mut self, instruction_idx: InstructionIdx, ty: Type) -> LocationIdx {
        let aliased_var = self.get_current_fx().locals.get(&instruction_idx).copied();

        match aliased_var {
            Some(aliased_var) => match self.var_to_location.get(&aliased_var) {
                Some(&location) => {
                    self.lir.locations[location].ty = ty.clone();
                    location
                }
                None => {
                    let location = self.create_location(ty);
                    self.var_to_location.insert(aliased_var, location);
                    self.instruction_to_location.insert(instruction_idx, location);
                    location
                }
            }
            None => match self.instruction_to_location.get(&instruction_idx) {
                Some(&location) => {
                    self.lir.locations[location].ty = ty.clone();
                    location
                }
                None => {
                    let location = self.create_location(ty);
                    self.instruction_to_location.insert(instruction_idx, location);
                    location
                }
            }
        }
    }

    fn get_ref_location_for_array_init(&mut self, instruction_idx: InstructionIdx, array_size: usize) -> LocationIdx {
        let instruction = self.get_current_fx().instructions.get(instruction_idx);
        let aliased_var = self.get_current_fx().locals.get(&instruction_idx).copied();

        let array_type = match &instruction.ty {
            mir::Type::Array(element_type, _) => Type::Array {
                element_type: Box::new(Type::from((**element_type).clone())),
                size: array_size,
            },
            _ => instruction.ty.clone().into(), // Fallback to normal conversion
        };

        match aliased_var {
            Some(aliased_var) => match self.var_to_location.get(&aliased_var) {
                Some(location) => *location,
                None => {
                    let location = self.create_location(array_type);
                    self.instruction_to_location.insert(instruction_idx, location);
                    location
                }
            }
            None => match self.instruction_to_location.get(&instruction_idx) {
                Some(location) => *location,
                None => {
                    let location = self.create_location(array_type);
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

    fn get_ref_location_for_move(&mut self, instruction_idx: InstructionIdx, source: &Operand) -> LocationIdx {
        let instruction = self.get_current_fx().instructions.get(instruction_idx);
        
        let ty = match &source.kind {
            OperandKind::Location(loc_idx) => {
                let source_location = self.lir.locations.get(*loc_idx);
                match &source_location.ty {
                    Type::Array { element_type, size } => Type::Array { 
                        element_type: element_type.clone(), 
                        size: *size 
                    },
                    _ => instruction.ty.clone().into(),
                }
            },
            _ => instruction.ty.clone().into(),
        };
        
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
}