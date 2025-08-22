use anyhow::Result;
use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicType, BasicTypeEnum},
    values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue},
    IntPredicate, FloatPredicate, AddressSpace,
};
use std::{collections::HashMap, result};

use snowflake_middle::ir::lir::{
    self, LIR, Function, InstructionKind, Operand, OperandKind, ConstValue, 
    Terminator, Type, FunctionIdx, BasicBlockIdx, LocationIdx
};

mod runtime;
use runtime::LLVMRuntime;


pub struct LLVMBackend<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    functions: HashMap<FunctionIdx, FunctionValue<'ctx>>,
    locations: HashMap<LocationIdx, PointerValue<'ctx>>,
    basic_blocks: HashMap<BasicBlockIdx, inkwell::basic_block::BasicBlock<'ctx>>,
}

impl<'ctx> LLVMBackend<'ctx> {
    pub fn new(context: &'ctx Context, module_name: &str) -> Self {
        let module = context.create_module(module_name);
        let builder = context.create_builder();
        
        Self {
            context,
            module,
            builder,
            functions: HashMap::new(),
            locations: HashMap::new(),
            basic_blocks: HashMap::new(),
        }
    }

    pub fn compile_lir(&mut self, lir: &LIR) -> Result<()> {
        // First pass: declare all functions
        for (func_idx, function) in lir.functions.indexed_iter() {
            self.declare_function(func_idx, function, lir)?;
        }

        // Second pass: compile function bodies
        for (func_idx, function) in lir.functions.indexed_iter() {
            self.compile_function(func_idx, function, lir)?;
        }

        Ok(())
    }

    fn declare_function(&mut self, func_idx: FunctionIdx, function: &Function, lir: &LIR) -> Result<()> {
        let return_type = self.lir_type_to_llvm(&function.return_type);
        
        // Convert parameter types
        let mut param_types: Vec<inkwell::types::BasicMetadataTypeEnum> = Vec::new();
        for &param_loc in &function.params {
            let ty = &lir.locations[param_loc].ty;
            if let Some(llvm_type) = self.lir_type_to_llvm(ty) {
                param_types.push(llvm_type.into());
            }
        }
        
        let fn_type = match return_type {
            Some(ret_type) => ret_type.fn_type(&param_types, false),
            None => self.context.void_type().fn_type(&param_types, false),
        };
        
        let fn_value = self.module.add_function(&function.name, fn_type, None);
        self.functions.insert(func_idx, fn_value);
        
        Ok(())
    }

    fn compile_function(&mut self, func_idx: FunctionIdx, function: &Function, lir: &LIR) -> Result<()> {
        let fn_value = self.functions[&func_idx];
        
        for &bb_idx in &function.basic_blocks {
            let bb_name = format!("bb_{}", bb_idx.index);
            let basic_block = self.context.append_basic_block(fn_value, &bb_name);
            self.basic_blocks.insert(bb_idx, basic_block);
        }

        let first_bb = self.basic_blocks[&function.basic_blocks[0]];
        self.builder.position_at_end(first_bb);
        
        for (i, &param_loc) in function.params.iter().enumerate() {
            let param_value = fn_value.get_nth_param(i as u32).unwrap();
            let location = &lir.locations[param_loc];
            let llvm_type = self.lir_type_to_llvm(&location.ty).unwrap();
            
            let alloca = self.builder.build_alloca(llvm_type, &format!("param_{}", i))?;
            self.builder.build_store(alloca, param_value)?;
            self.locations.insert(param_loc, alloca);
        }

        for &bb_idx in &function.basic_blocks {
            let basic_block = self.basic_blocks[&bb_idx];
            self.builder.position_at_end(basic_block);
            
            let bb = &lir.basic_blocks[bb_idx];
            
            for instruction in &bb.instructions {
                self.compile_instruction(instruction, lir)?;
            }
            
            if let Some(ref terminator) = bb.terminator {
                self.compile_terminator(terminator, lir)?;
            }
        }

        Ok(())
    }

    fn compile_instruction(&mut self, instruction: &lir::Instruction, lir: &LIR) -> Result<()> {
        match &instruction.kind {
            InstructionKind::Add { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;
                
                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_add(
                        left_val.into_int_value(), right_val.into_int_value(), "add"
                    )?.into()
                } else {
                    self.builder.build_float_add(
                        left_val.into_float_value(), right_val.into_float_value(), "fadd"
                    )?.into()
                };
                
                self.store_to_location(*target, result, lir)?;
            }
            InstructionKind::Sub { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;
                
                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_sub(
                        left_val.into_int_value(), right_val.into_int_value(), "sub"
                    )?.into()
                } else {
                    self.builder.build_float_sub(
                        left_val.into_float_value(), right_val.into_float_value(), "fsub"
                    )?.into()
                };
                
                self.store_to_location(*target, result, lir)?;
            }
            InstructionKind::Mul { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;
                
                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_mul(
                        left_val.into_int_value(), right_val.into_int_value(), "mul"
                    )?.into()
                } else {
                    self.builder.build_float_mul(
                        left_val.into_float_value(), right_val.into_float_value(), "fmul"
                    )?.into()
                };
                
                self.store_to_location(*target, result, lir)?;
            }
            InstructionKind::Div { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;
                
                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_signed_div(
                        left_val.into_int_value(), right_val.into_int_value(), "div"
                    )?.into()
                } else {
                    self.builder.build_float_div(
                        left_val.into_float_value(), right_val.into_float_value(), "fdiv"
                    )?.into()
                };
                
                self.store_to_location(*target, result, lir)?;
            }
            InstructionKind::Mod { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;
                
                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_signed_rem(
                        left_val.into_int_value(), right_val.into_int_value(), "mod"
                    )?.into()
                } else {
                    self.builder.build_float_rem(
                        left_val.into_float_value(), right_val.into_float_value(), "frem"
                    )?.into()
                };
                
                self.store_to_location(*target, result, lir)?;
            }
            InstructionKind::Eq { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;
                
                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_compare(
                        IntPredicate::EQ, left_val.into_int_value(), right_val.into_int_value(), "eq"
                    )?.into()
                } else {
                    self.builder.build_float_compare(
                        FloatPredicate::OEQ, left_val.into_float_value(), right_val.into_float_value(), "feq"
                    )?.into()
                };

                self.store_to_location(*target, result, lir)?;
            }
            InstructionKind::Ne { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;

                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_compare(
                        IntPredicate::NE, left_val.into_int_value(), right_val.into_int_value(), "ne"
                    )?.into()
                } else {
                    self.builder.build_float_compare(
                        FloatPredicate::ONE, left_val.into_float_value(), right_val.into_float_value(), "fne"
                    )?.into()
                };

                self.store_to_location(*target, result, lir)?;
            }
            InstructionKind::Lt { target, left, right } => {
                // TODO: Think about unsigned comparisons (for all lt/gt/le/ge)
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;

                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    let left_int = left_val.into_int_value();
                    let right_int = right_val.into_int_value();
                    
                    // Ensure both operands have the same type by casting to the larger type
                    let (left_casted, right_casted) = if left_int.get_type().get_bit_width() != right_int.get_type().get_bit_width() {
                        if left_int.get_type().get_bit_width() < right_int.get_type().get_bit_width() {
                            let left_casted = self.builder.build_int_s_extend(left_int, right_int.get_type(), "sext")?;
                            (left_casted, right_int)
                        } else {
                            let right_casted = self.builder.build_int_s_extend(right_int, left_int.get_type(), "sext")?;
                            (left_int, right_casted)
                        }
                    } else {
                        (left_int, right_int)
                    };
                    
                    self.builder.build_int_compare(
                        IntPredicate::SLT, left_casted, right_casted, "lt"
                    )?.into()
                } else {
                    self.builder.build_float_compare(
                        FloatPredicate::OLT, left_val.into_float_value(), right_val.into_float_value(), "flt"
                    )?.into()
                };

                self.store_to_location(*target, result, lir)?;
            }
            InstructionKind::Gt { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;

                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_compare(
                        IntPredicate::SGT, left_val.into_int_value(), right_val.into_int_value(), "gt"
                    )?.into()
                } else {
                    self.builder.build_float_compare(
                        FloatPredicate::OGT, left_val.into_float_value(), right_val.into_float_value(), "fgt"
                    )?.into()
                };

                self.store_to_location(*target, result, lir)?;
            }
            InstructionKind::Le { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;

                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_compare(
                        IntPredicate::SLE, left_val.into_int_value(), right_val.into_int_value(), "le"
                    )?.into()
                } else {
                    self.builder.build_float_compare(
                        FloatPredicate::OLE, left_val.into_float_value(), right_val.into_float_value(), "fle"
                    )?.into()
                };

                self.store_to_location(*target, result, lir)?;
            }
            InstructionKind::Ge { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;

                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_compare(
                        IntPredicate::SGE, left_val.into_int_value(), right_val.into_int_value(), "ge"
                    )?.into()
                } else {
                    self.builder.build_float_compare(
                        FloatPredicate::OGE, left_val.into_float_value(), right_val.into_float_value(), "fge"
                    )?.into()
                };

                self.store_to_location(*target, result, lir)?;
            }
            InstructionKind::Move { target, source } => {
                match &source.ty {
                    Type::Array { .. } => {
                        // Create alias for arrays
                        match &source.kind {
                            OperandKind::Location(src_loc_idx) => {
                                if let Some(src_alloca) = self.locations.get(src_loc_idx) {
                                    self.locations.insert(*target, *src_alloca);
                                } else {
                                    return Err(anyhow::anyhow!("Source array location not found"));
                                }
                            }
                            _ => {
                                let value = self.compile_operand(source, lir)?;
                                self.store_to_location(*target, value, lir)?;
                            }
                        }
                    }
                    _ => {
                        // Default handling
                        let value = self.compile_operand(source, lir)?;
                        self.store_to_location(*target, value, lir)?;
                    }
                }
            }
            InstructionKind::AllocInit { target, value } => {
                let val = self.compile_operand(value, lir)?;
                let location = &lir.locations[*target];
                let llvm_type = self.lir_type_to_llvm(&location.ty).unwrap();
                
                let alloca = self.builder.build_alloca(llvm_type, &format!("loc_{}", target.index))?;
                self.builder.build_store(alloca, val)?;
                self.locations.insert(*target, alloca);
            }
            InstructionKind::Load { target, source } => {
                let source_val = self.compile_operand(source, lir)?;
                if source_val.is_pointer_value() {
                    let ptr = source_val.into_pointer_value();
                    let loaded = self.builder.build_load(self.context.i32_type(), ptr, "load")?;
                    self.store_to_location(*target, loaded, lir)?;
                }
            }
            InstructionKind::Store { target, value } => {
                let val = self.compile_operand(value, lir)?;
                let target_val = self.compile_operand(target, lir)?;
                if target_val.is_pointer_value() {
                    let ptr = target_val.into_pointer_value();
                    self.builder.build_store(ptr, val)?;
                }
            }
            InstructionKind::ArrayAlloc { target, element_type, size } => {
                let arr_size = self.compile_operand(size, lir)?;
                let element_ty = self.lir_type_to_llvm(element_type).unwrap();
                let ptr = self.builder.build_array_alloca(element_ty, arr_size.into_int_value(), "array_alloc")?;
                self.locations.insert(*target, ptr);
            }
            InstructionKind::Call { target, function, args } => {
                let fn_value = self.functions[function];
                let mut arg_values = Vec::new();
                
                for arg in args {
                    let arg_val = self.compile_operand(arg, lir)?;
                    arg_values.push(arg_val.into());
                }
                
                let call_site = self.builder.build_call(fn_value, &arg_values, "call")?;
                
                if let Some(target_loc) = target {
                    if let Some(return_value) = call_site.try_as_basic_value().left() {
                        self.store_to_location(*target_loc, return_value, lir)?;
                    }
                }
            }
            InstructionKind::ArrayIndex { target, array, index } => {
                let index_val = self.compile_operand(index, lir)?;
                let ptr_type = self.lir_type_to_llvm(&array.ty).unwrap();
                let array_ptr = match &array.kind {
                    OperandKind::Location(loc_idx) => {
                        if let Some(alloca) = self.locations.get(loc_idx) {
                            *alloca
                        } else {
                            return Err(anyhow::anyhow!("Array location not found for indexing"));
                        }
                    }
                    _ => {
                        return Err(anyhow::anyhow!("ArrayIndex requires array operand to be a location"));
                    }
                };
                
                // Use two indices: 0 (to get the array pointer) and the actual index
                let zero = self.context.i32_type().const_int(0, false);
                let index_int = index_val.into_int_value();
                let indices = [zero.into(), index_int.into()];
                
                let element_ptr = unsafe {
                    self.builder.build_gep(
                        ptr_type,
                        array_ptr,
                        &indices,
                        "array_gep"
                    )?
                };
                
                // Load the value from the computed address
                let element_type = match &array.ty {
                    Type::Array { element_type, size: _ } => self.lir_type_to_llvm(element_type).unwrap(),
                    _ => self.context.i32_type().into(), // fallback
                };
                
                let loaded_val = self.builder.build_load(
                    element_type,
                    element_ptr,
                    "array_load"
                )?;
                
                self.store_to_location(*target, loaded_val, lir)?;
            }
            InstructionKind::ArrayStore { array, index, value } => {
                let array_ptr = match &array.kind {
                    OperandKind::Location(loc_idx) => {
                        if !self.locations.contains_key(loc_idx) {
                            let location = &lir.locations[*loc_idx];
                            let llvm_type = self.lir_type_to_llvm(&location.ty).unwrap();
                            let alloca = self.builder.build_alloca(llvm_type, &format!("loc_{}", loc_idx.index))?;
                            self.locations.insert(*loc_idx, alloca);
                        }
                        
                        if let Some(alloca) = self.locations.get(loc_idx) {
                            *alloca
                        } else {
                            return Err(anyhow::anyhow!("Array location not found after allocation"));
                        }
                    }
                    _ => {
                        return Err(anyhow::anyhow!("ArrayStore requires array operand to be a location"));
                    }
                };
                
                let index_val = self.compile_operand(index, lir)?;
                let value_val = self.compile_operand(value, lir)?;
                let ptr_type = self.lir_type_to_llvm(&array.ty).unwrap();
                
                // Use two indices: 0 (to get the array pointer) and the actual index
                let zero = self.context.i32_type().const_int(0, false);
                let index_int = index_val.into_int_value();
                let indices = [zero.into(), index_int.into()];
                
                let element_ptr = unsafe {
                    self.builder.build_gep(
                        ptr_type,
                        array_ptr,
                        &indices,
                        "array_store_gep"
                    )?
                };
                
                // Store the value at the computed address
                self.builder.build_store(element_ptr, value_val)?;
            }
            InstructionKind::ArrayLength { target, length } => {
                let length_val = self.compile_operand(length, lir)?;
                self.store_to_location(*target, length_val, lir)?;
            }
            InstructionKind::Phi { target, operands } => {
                // In LLVM, phi nodes must be at the beginning of a basic block
                let target_location = &lir.locations[*target];
                let llvm_type = self.lir_type_to_llvm(&target_location.ty).unwrap();
                
                let phi = self.builder.build_phi(llvm_type, "phi")?;
                
                for (bb_idx, operand) in operands {
                    let value = self.compile_operand(operand, lir)?;
                    let bb = self.basic_blocks[bb_idx];
                    phi.add_incoming(&[(&value, bb)]);
                }
                
                self.store_to_location(*target, phi.as_basic_value(), lir)?;
            }
            InstructionKind::Nop => {
                // No operation - do nothing
            }
            _ => {
                unimplemented!("Instruction {:?} not implemented", instruction.kind);
            }
        }
        
        Ok(())
    }

    fn compile_terminator(&mut self, terminator: &Terminator, lir: &LIR) -> Result<()> {
        match terminator {
            Terminator::Return { value } => {
                match value {
                    Some(operand) => {
                        let val = self.compile_operand(operand, lir)?;
                        self.builder.build_return(Some(&val))?;
                    }
                    None => {
                        self.builder.build_return(None)?;
                    }
                }
            }
            Terminator::Goto { target } => {
                let target_bb = self.basic_blocks[target];
                self.builder.build_unconditional_branch(target_bb)?;
            }
            Terminator::Switch { value, targets, default_target } => {
                let condition_val = self.compile_operand(value, lir)?;
                
                let switch_val = if condition_val.is_int_value() {
                    let int_val = condition_val.into_int_value();
                    if int_val.get_type().get_bit_width() == 1 {
                        self.builder.build_int_z_extend(int_val, self.context.i32_type(), "bool_to_int")?
                    } else {
                        int_val
                    }
                } else {
                    condition_val.into_int_value()
                };
                
                let cases: Vec<(inkwell::values::IntValue, inkwell::basic_block::BasicBlock)> = targets.iter().map(|(case_value, target)| {
                    let case_bb = self.basic_blocks[target];
                    let value = self.compile_const_value(case_value);
                    (value.into_int_value(), case_bb)
                }).collect();

                self.builder.build_switch(switch_val, self.basic_blocks[default_target], &cases)?;
            }
            Terminator::Branch { condition, true_target, false_target } => {
                let condition = self.compile_operand(condition, lir)?;
                let true_bb = self.basic_blocks[true_target];
                let false_bb = self.basic_blocks[false_target];
                self.builder.build_conditional_branch(condition.into_int_value(), true_bb, false_bb)?;
            }
            Terminator::Unreachable { error } => {
                LLVMRuntime::generate_unreachable_error(self.context, &self.module, &self.builder, error)?;
            }
            Terminator::Panic { message } => {
                LLVMRuntime::generate_panic_with_message(self.context, &self.module, &self.builder, message)?;
            }
            _ => unimplemented!("Terminator {:?} not implemented", terminator),
        }
        
        Ok(())
    }

    fn compile_operand(&mut self, operand: &Operand, lir: &LIR) -> Result<BasicValueEnum<'ctx>> {
        match &operand.kind {
            OperandKind::Location(loc_idx) => {
                if let Some(alloca) = self.locations.get(loc_idx) {
                    let location = &lir.locations[*loc_idx];
                    let llvm_type = self.lir_type_to_llvm(&location.ty).unwrap();
                    let loaded = self.builder.build_load(llvm_type, *alloca, "load_loc")?;
                    Ok(loaded)
                } else {
                    // Create a temporary value - this shouldn't happen in well-formed LIR
                    Ok(self.context.i32_type().const_int(0, false).into())
                }
            }
            OperandKind::Const(const_val) => {
                Ok(self.compile_const_value(const_val))
            }
            OperandKind::Deref(loc_idx) => {
                if let Some(alloca) = self.locations.get(loc_idx) {
                    let ptr = self.builder.build_load(self.context.ptr_type(inkwell::AddressSpace::default()), *alloca, "load_ptr")?;
                    if ptr.is_pointer_value() {
                        let ptr_val = ptr.into_pointer_value();
                        // TODO: resolve pointer element type
                        let loaded = self.builder.build_load(self.context.i32_type(), ptr_val, "deref")?;
                        Ok(loaded)
                    } else {
                        Ok(self.context.i32_type().const_int(0, false).into())
                    }
                } else {
                    Ok(self.context.i32_type().const_int(0, false).into())
                }
            }
            _ => {
                unimplemented!("Operand {:?} not implemented", operand.kind);
            }
        }
    }

    fn compile_const_value(&self, const_val: &ConstValue) -> BasicValueEnum<'ctx> {
        match const_val {
            ConstValue::Int8(val) => self.context.i8_type().const_int(*val as u64, true).into(),
            ConstValue::Int16(val) => self.context.i16_type().const_int(*val as u64, true).into(),
            ConstValue::Int32(val) => self.context.i32_type().const_int(*val as u64, true).into(),
            ConstValue::Int64(val) => self.context.i64_type().const_int(*val as u64, true).into(),
            ConstValue::UInt8(val) => self.context.i8_type().const_int(*val as u64, false).into(),
            ConstValue::UInt16(val) => self.context.i16_type().const_int(*val as u64, false).into(),
            ConstValue::UInt32(val) => self.context.i32_type().const_int(*val as u64, false).into(),
            ConstValue::UInt64(val) => self.context.i64_type().const_int(*val, false).into(),
            ConstValue::Float32(val) => self.context.f32_type().const_float(*val as f64).into(),
            ConstValue::Float64(val) => self.context.f64_type().const_float(*val).into(),
            ConstValue::Bool(val) => self.context.bool_type().const_int(if *val { 1 } else { 0 }, false).into(),
            ConstValue::String(_) => {
                // TODO: Implement string constants
                self.context.ptr_type(AddressSpace::default()).const_null().into()
            }
            ConstValue::Null => {
                self.context.ptr_type(AddressSpace::default()).const_null().into()
            }
        }
    }

    fn store_to_location(&mut self, loc_idx: LocationIdx, value: BasicValueEnum<'ctx>, lir: &LIR) -> Result<()> {
        if let Some(alloca) = self.locations.get(&loc_idx) {
            self.builder.build_store(*alloca, value)?;
        } else {
            // Create alloca for this location if it doesn't exist
            let location = &lir.locations[loc_idx];
            let llvm_type = if let Some(ty) = self.lir_type_to_llvm(&location.ty) {
                ty
            } else {
                value.get_type()
            };
            let alloca = self.builder.build_alloca(llvm_type, &format!("loc_{}", loc_idx.index))?;
            self.builder.build_store(alloca, value)?;
            self.locations.insert(loc_idx, alloca);
        }
        Ok(())
    }

    fn lir_type_to_llvm(&self, lir_type: &Type) -> Option<BasicTypeEnum<'ctx>> {
        match lir_type {
            Type::Int8 => Some(self.context.i8_type().into()),
            Type::Int16 => Some(self.context.i16_type().into()),
            Type::Int32 => Some(self.context.i32_type().into()),
            Type::Int64 => Some(self.context.i64_type().into()),
            Type::UInt8 => Some(self.context.i8_type().into()),
            Type::UInt16 => Some(self.context.i16_type().into()),
            Type::UInt32 => Some(self.context.i32_type().into()),
            Type::UInt64 => Some(self.context.i64_type().into()),
            Type::Float32 => Some(self.context.f32_type().into()),
            Type::Float64 => Some(self.context.f64_type().into()),
            Type::Bool => Some(self.context.bool_type().into()),
            Type::String => {
                // String as pointer to i8
                Some(self.context.ptr_type(AddressSpace::default()).into())
            }
            Type::Pointer(element_type) => {
                if let Some(_elem_type) = self.lir_type_to_llvm(element_type) {
                    Some(self.context.ptr_type(AddressSpace::default()).into())
                } else {
                    None
                }
            }
            Type::Array { element_type, size } => {
                if let Some(elem_type) = self.lir_type_to_llvm(element_type) {
                    Some(elem_type.array_type(*size as u32).into())
                } else {
                    None
                }
            }
            Type::Void => None,
        }
    }

    pub fn get_module(&self) -> &Module<'ctx> {
        &self.module
    }

    pub fn print_to_string(&self) -> String {
        self.module.print_to_string().to_string()
    }
}
