use anyhow::Result;
use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    basic_block::BasicBlock,
    types::{BasicType, BasicTypeEnum},
    values::{BasicValueEnum, FunctionValue, PointerValue},
    IntPredicate, FloatPredicate, AddressSpace,
};
use std::collections::{HashMap, HashSet};

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
    basic_blocks: HashMap<BasicBlockIdx, BasicBlock<'ctx>>,
    last_stored_values: HashMap<(BasicBlockIdx, LocationIdx), BasicValueEnum<'ctx>>,
    current_basic_block: Option<BasicBlockIdx>,
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
            last_stored_values: HashMap::new(),
            current_basic_block: None,
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

        // Check if there's a main function, if not create one that calls __global_init
        let has_main = lir.functions.indexed_iter()
            .any(|(_, function)| function.name == "main");
        
        if !has_main {
            self.generate_main_function()?;
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

        // Pre-pass: Create all location allocs
        let mut used_locations = HashSet::new();

        for &bb_idx in &function.basic_blocks {
            let bb = &lir.basic_blocks[bb_idx];
            for instruction in &bb.instructions {
                self.collect_locations_from_instruction(instruction, &mut used_locations);
            }
            if let Some(ref terminator) = bb.terminator {
                self.collect_locations_from_terminator(terminator, &mut used_locations);
            }
        }
        
        for &loc_idx in &used_locations {
            if !self.locations.contains_key(&loc_idx) {
                let location = &lir.locations[loc_idx];
                let llvm_type = self.lir_type_to_llvm(&location.ty).unwrap_or_else(|| self.context.i32_type().into());
                let alloca = self.builder.build_alloca(llvm_type, &format!("loc_{}", loc_idx.index)).unwrap();
                self.locations.insert(loc_idx, alloca);
            }
        }

        // Process all instructions in order
        for &bb_idx in &function.basic_blocks {
            let basic_block = self.basic_blocks[&bb_idx];
            self.builder.position_at_end(basic_block);
            self.current_basic_block = Some(bb_idx);
            
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
                
                // Get the type of the array location
                let array_location = match &array.kind {
                    OperandKind::Location(loc_idx) => &lir.locations[*loc_idx],
                    _ => return Err(anyhow::anyhow!("ArrayIndex requires array operand to be a location")),
                };
                let ptr_type = self.lir_type_to_llvm(&array_location.ty).unwrap();
                
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
            InstructionKind::ArrayLength { target, length } => {
                let length_val = self.compile_operand(length, lir)?;
                self.store_to_location(*target, length_val, lir)?;
            }
            InstructionKind::Object { target, elements } => {
                let location = &lir.locations[*target];
                let object_type = self.lir_type_to_llvm(&location.ty).unwrap();
                let object_alloca = self.builder.build_alloca(object_type, &format!("object_{}", target.index))?;
                
                for (i, element) in elements.iter().enumerate() {
                    let element_value = self.compile_operand(element, lir)?;
                    let zero = self.context.i32_type().const_int(0, false);
                    let index = self.context.i32_type().const_int(i as u64, false);
                    let indices = [zero.into(), index.into()];
                    
                    // Pointer to i-th element in tuple
                    let element_ptr = unsafe {
                        self.builder.build_gep(
                            object_type,
                            object_alloca,
                            &indices,
                            &format!("object_elem_{}", i)
                        )?
                    };
                    
                    self.builder.build_store(element_ptr, element_value)?;
                }
                
                self.locations.insert(*target, object_alloca);
            }
            InstructionKind::FieldAccess { target, object, field } => {
                let object_ptr = match &object.kind {
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
                            return Err(anyhow::anyhow!("Object location not found after allocation"));
                        }
                    }
                    _ => {
                        return Err(anyhow::anyhow!("ObjectIndex requires object operand to be a location"));
                    }
                };
                
                // Get the index (compile-time constant)
                let index_value = match &field.kind {
                    OperandKind::Const(ConstValue::Int32(idx)) => *idx as u32,
                    OperandKind::Const(ConstValue::UInt64(idx)) => *idx as u32,
                    _ => {
                        return Err(anyhow::anyhow!("ObjectIndex requires constant index, got {:?}", field.kind));
                    }
                };

                // Get the object type
                let object_location = match &object.kind {
                    OperandKind::Location(loc_idx) => &lir.locations[*loc_idx],
                    _ => return Err(anyhow::anyhow!("ObjectIndex requires object operand to be a location")),
                };
                let object_type = self.lir_type_to_llvm(&object_location.ty).unwrap();
                
                // Use GEP to point to specific object element
                let zero = self.context.i32_type().const_int(0, false);
                let field_index = self.context.i32_type().const_int(index_value as u64, false);
                let indices = [zero.into(), field_index.into()];
                
                let element_ptr = unsafe {
                    self.builder.build_gep(
                        object_type,
                        object_ptr,
                        &indices,
                        &format!("object_field_{}", index_value)
                    )?
                };
                
                // Get the element type for loading
                let element_type = match &object_location.ty {
                    Type::Object { element_types } => {
                        if index_value < element_types.len() as u32 {
                            self.lir_type_to_llvm(&element_types[index_value as usize]).unwrap()
                        } else {
                            // Should not occur
                            return Err(anyhow::anyhow!("Tuple index {} out of bounds for tuple with {} elements", 
                                index_value, element_types.len()));
                        }
                    }
                    _ => return Err(anyhow::anyhow!("Expected tuple type, got {:?}", object_location.ty)),
                };
                
                // Load the value from the computed address
                let loaded_val = self.builder.build_load(
                    element_type,
                    element_ptr,
                    "tuple_load"
                )?;
                
                self.store_to_location(*target, loaded_val, lir)?;
            }
            InstructionKind::ObjectStore { object, index, value } => {
                let object_ptr = match &object.kind {
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
                            return Err(anyhow::anyhow!("Object location not found after allocation"));
                        }
                    }
                    _ => {
                        return Err(anyhow::anyhow!("ObjectStore requires object operand to be a location"));
                    }
                };
                
                // Get the index (compile-time constant)
                let index_value = match &index.kind {
                    OperandKind::Const(ConstValue::Int32(idx)) => *idx as u32,
                    OperandKind::Const(ConstValue::UInt64(idx)) => *idx as u32,
                    _ => {
                        return Err(anyhow::anyhow!("ObjectStore requires constant index, got {:?}", index.kind));
                    }
                };
                
                let value_val = self.compile_operand(value, lir)?;

                // Get the object type
                let object_location = match &object.kind {
                    OperandKind::Location(loc_idx) => &lir.locations[*loc_idx],
                    _ => return Err(anyhow::anyhow!("ObjectStore requires object operand to be a location")),
                };
                let object_type = self.lir_type_to_llvm(&object_location.ty).unwrap();

                // Use GEP to point to specific object field
                let zero = self.context.i32_type().const_int(0, false);
                let field_index = self.context.i32_type().const_int(index_value as u64, false);
                let indices = [zero.into(), field_index.into()];
                
                let element_ptr = unsafe {
                    self.builder.build_gep(
                        object_type,
                        object_ptr,
                        &indices,
                        &format!("object_store_field_{}", index_value)
                    )?
                };
                
                // Store the value at the computed address
                self.builder.build_store(element_ptr, value_val)?;
            }
            InstructionKind::Phi { target, operands } => {
                // Handle phi nodes by using the first operand (the initial/entry value)
                if let Some((_, first_operand)) = operands.first() {
                    let value = self.compile_operand(first_operand, lir)?;
                    self.store_to_location(*target, value, lir)?;
                } else {
                    let target_location = &lir.locations[*target];
                    let default_value = match target_location.ty {
                        Type::Int32 => self.context.i32_type().const_int(0, false).into(),
                        Type::Bool => self.context.bool_type().const_int(0, false).into(),
                        _ => self.context.i32_type().const_int(0, false).into(),
                    };
                    self.store_to_location(*target, default_value, lir)?;
                }
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
                // For loops
                if let Some(current_bb_idx) = self.current_basic_block {
                    // Check if this is a loop back edge (current block > target block)
                    if current_bb_idx.index > target.index {
                        // This might be a loop back edge - check for phi nodes in the target
                        let target_bb_lir = &lir.basic_blocks[*target];
                        for instruction in &target_bb_lir.instructions {
                            if let InstructionKind::Phi { target: _phi_target, operands } = &instruction.kind {
                                for (pred_bb, operand) in operands {
                                    if pred_bb == &current_bb_idx {
                                        let value = self.compile_operand(operand, lir)?;
                                        
                                        // Copy to the original source location for next iteration
                                        if let Some((_, first_operand)) = operands.first() {
                                            if let OperandKind::Location(orig_loc) = &first_operand.kind {
                                                self.store_to_location(*orig_loc, value, lir)?;
                                            }
                                        }
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }
                
                let target_bb = self.basic_blocks[target];
                self.builder.build_unconditional_branch(target_bb)?;
            }
            Terminator::Switch { value, targets, default_target } => {
                let condition_val = self.compile_operand(value, lir)?;
                
                if let OperandKind::Location(loc_idx) = &value.kind {
                    let location = &lir.locations[*loc_idx];
                    if location.ty == Type::Bool {
                        // Use direct boolean branching instead of switch for bools
                        let bool_val = condition_val.into_int_value();
                        let false_target = targets.iter()
                            .find(|(case_val, _)| matches!(case_val, ConstValue::Int32(0)))
                            .map(|(_, target)| *target)
                            .unwrap_or(*default_target);
                        
                        let true_target = *default_target;
                        
                        let false_bb = self.basic_blocks[&false_target];
                        let true_bb = self.basic_blocks[&true_target];
                        
                        self.builder.build_conditional_branch(bool_val, true_bb, false_bb)?;
                        return Ok(());
                    }
                }
                
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
            ConstValue::String(str) => {
                let string_ptr = runtime::LLVMRuntime::create_string_literal(self.context, &self.module, str).unwrap();
                string_ptr.into()
            }
            ConstValue::Null => {
                self.context.ptr_type(AddressSpace::default()).const_null().into()
            }
        }
    }

    fn store_to_location(&mut self, loc_idx: LocationIdx, value: BasicValueEnum<'ctx>, lir: &LIR) -> Result<()> {
        if let Some(current_bb) = self.current_basic_block {
            self.last_stored_values.insert((current_bb, loc_idx), value);
        }
        
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
            Type::Object { element_types } => {
                let mut llvm_elem_types = Vec::new();
                for elem_type in element_types {
                    if let Some(llvm_type) = self.lir_type_to_llvm(elem_type) {
                        llvm_elem_types.push(llvm_type);
                    } else {
                        return None;
                    }
                }
                Some(self.context.struct_type(&llvm_elem_types, false).into())
            }
            Type::Unit => None,
            Type::Void => None,
        }
    }

    pub fn get_module(&self) -> &Module<'ctx> {
        &self.module
    }

    pub fn print_to_string(&self) -> String {
        self.module.print_to_string().to_string()
    }

    /// Generate a main function that calls `__global_init` and returns 0
    fn generate_main_function(&mut self) -> Result<()> {
        let i32_type = self.context.i32_type();
        let main_type = i32_type.fn_type(&[], false);
        let main_fn = self.module.add_function("main", main_type, None);
        
        let entry_bb = self.context.append_basic_block(main_fn, "entry");
        self.builder.position_at_end(entry_bb);
        
        if let Some(global_init_fn) = self.module.get_function("__global_init") {
            self.builder.build_call(global_init_fn, &[], "call_global_init")?;
        }
        
        let zero = i32_type.const_int(0, false);
        self.builder.build_return(Some(&zero))?;
        
        Ok(())
    }

    /// Collect all locations referenced in an instruction
    fn collect_locations_from_instruction(&self, instruction: &lir::Instruction, locations: &mut HashSet<LocationIdx>) {
        match &instruction.kind {
            InstructionKind::Add { target, left, right } |
            InstructionKind::Sub { target, left, right } |
            InstructionKind::Mul { target, left, right } |
            InstructionKind::Div { target, left, right } |
            InstructionKind::Mod { target, left, right } |
            InstructionKind::Eq { target, left, right } |
            InstructionKind::Ne { target, left, right } |
            InstructionKind::Lt { target, left, right } |
            InstructionKind::Gt { target, left, right } |
            InstructionKind::Le { target, left, right } |
            InstructionKind::Ge { target, left, right } => {
                locations.insert(*target);
                self.collect_locations_from_operand(left, locations);
                self.collect_locations_from_operand(right, locations);
            }
            InstructionKind::Move { target, source } => {
                locations.insert(*target);
                self.collect_locations_from_operand(source, locations);
            }
            InstructionKind::AllocInit { target, value } => {
                locations.insert(*target);
                self.collect_locations_from_operand(value, locations);
            }
            InstructionKind::Load { target, source } => {
                locations.insert(*target);
                self.collect_locations_from_operand(source, locations);
            }
            InstructionKind::Store { target, value } => {
                self.collect_locations_from_operand(target, locations);
                self.collect_locations_from_operand(value, locations);
            }
            InstructionKind::ArrayAlloc { target, size, .. } => {
                locations.insert(*target);
                self.collect_locations_from_operand(size, locations);
            }
            InstructionKind::Call { target, args, .. } => {
                if let Some(target_loc) = target {
                    locations.insert(*target_loc);
                }
                for arg in args {
                    self.collect_locations_from_operand(arg, locations);
                }
            }
            InstructionKind::ArrayIndex { target, array, index } => {
                locations.insert(*target);
                self.collect_locations_from_operand(array, locations);
                self.collect_locations_from_operand(index, locations);
            }
            InstructionKind::ArrayLength { target, length } => {
                locations.insert(*target);
                self.collect_locations_from_operand(length, locations);
            }
            InstructionKind::Object { target, elements } => {
                locations.insert(*target);
                for element in elements {
                    self.collect_locations_from_operand(element, locations);
                }
            }
            InstructionKind::FieldAccess { target, object, field } => {
                locations.insert(*target);
                self.collect_locations_from_operand(object, locations);
                self.collect_locations_from_operand(field, locations);
            }
            InstructionKind::ObjectStore { object, index, value } => {
                self.collect_locations_from_operand(object, locations);
                self.collect_locations_from_operand(index, locations);
                self.collect_locations_from_operand(value, locations);
            }
            InstructionKind::Phi { target, operands } => {
                locations.insert(*target);
                for (_, operand) in operands {
                    self.collect_locations_from_operand(operand, locations);
                }
            }
            InstructionKind::Nop => {}
            _ => {}
        }
    }

    /// Collect all locations referenced in a terminator
    fn collect_locations_from_terminator(&self, terminator: &Terminator, locations: &mut HashSet<LocationIdx>) {
        match terminator {
            Terminator::Return { value } => {
                if let Some(operand) = value {
                    self.collect_locations_from_operand(operand, locations);
                }
            }
            Terminator::Switch { value, .. } => {
                self.collect_locations_from_operand(value, locations);
            }
            Terminator::Branch { condition, .. } => {
                self.collect_locations_from_operand(condition, locations);
            }
            _ => {}
        }
    }

    /// Collect all locations referenced in an operand
    fn collect_locations_from_operand(&self, operand: &Operand, locations: &mut HashSet<LocationIdx>) {
        match &operand.kind {
            OperandKind::Location(loc_idx) => {
                locations.insert(*loc_idx);
            }
            OperandKind::Deref(loc_idx) => {
                locations.insert(*loc_idx);
            }
            _ => {}
        }
    }
}
