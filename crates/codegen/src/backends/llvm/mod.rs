use anyhow::Result;
use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicType, BasicTypeEnum},
    values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue},
    IntPredicate, FloatPredicate, AddressSpace,
};
use std::collections::HashMap;

use snowflake_middle::ir::lir::{
    self, LIR, Function, InstructionKind, Operand, OperandKind, ConstValue, 
    Terminator, Type, FunctionIdx, BasicBlockIdx, LocationIdx
};


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
                    self.builder.build_int_add(left_val.into_int_value(), right_val.into_int_value(), "add")?.into()
                } else {
                    self.builder.build_float_add(left_val.into_float_value(), right_val.into_float_value(), "fadd")?.into()
                };
                
                self.store_to_location(*target, result)?;
            }
            InstructionKind::Sub { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;
                
                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_sub(left_val.into_int_value(), right_val.into_int_value(), "sub")?.into()
                } else {
                    self.builder.build_float_sub(left_val.into_float_value(), right_val.into_float_value(), "fsub")?.into()
                };
                
                self.store_to_location(*target, result)?;
            }
            InstructionKind::Mul { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;
                
                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_mul(left_val.into_int_value(), right_val.into_int_value(), "mul")?.into()
                } else {
                    self.builder.build_float_mul(left_val.into_float_value(), right_val.into_float_value(), "fmul")?.into()
                };
                
                self.store_to_location(*target, result)?;
            }
            InstructionKind::Div { target, left, right } => {
                let left_val = self.compile_operand(left, lir)?;
                let right_val = self.compile_operand(right, lir)?;
                
                let result: BasicValueEnum = if left_val.is_int_value() && right_val.is_int_value() {
                    self.builder.build_int_signed_div(left_val.into_int_value(), right_val.into_int_value(), "div")?.into()
                } else {
                    self.builder.build_float_div(left_val.into_float_value(), right_val.into_float_value(), "fdiv")?.into()
                };
                
                self.store_to_location(*target, result)?;
            }
            InstructionKind::Move { target, source } => {
                let value = self.compile_operand(source, lir)?;
                self.store_to_location(*target, value)?;
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
                    self.store_to_location(*target, loaded)?;
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
            Terminator::Branch { condition, true_target, false_target } => {
                // You'll need to implement condition compilation
                let true_bb = self.basic_blocks[true_target];
                let false_bb = self.basic_blocks[false_target];
                // For now, just branch to true target
                self.builder.build_unconditional_branch(true_bb)?;
            }
            _ => {
                unimplemented!("Terminator {:?} not implemented", terminator);
            }
        }
        
        Ok(())
    }

    fn compile_operand(&mut self, operand: &Operand, lir: &LIR) -> Result<BasicValueEnum<'ctx>> {
        match &operand.kind {
            OperandKind::Location(loc_idx) => {
                if let Some(alloca) = self.locations.get(loc_idx) {
                    let loaded = self.builder.build_load(self.context.i32_type(), *alloca, "load_loc")?;
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
            ConstValue::Int32(val) => self.context.i32_type().const_int(*val as u64, true).into(),
            ConstValue::Int64(val) => self.context.i64_type().const_int(*val as u64, true).into(),
            ConstValue::Float32(val) => self.context.f32_type().const_float(*val as f64).into(),
            ConstValue::Float64(val) => self.context.f64_type().const_float(*val).into(),
            ConstValue::Bool(val) => self.context.bool_type().const_int(if *val { 1 } else { 0 }, false).into(),
            _ => self.context.i32_type().const_int(0, false).into(), // Default fallback
        }
    }

    fn store_to_location(&mut self, loc_idx: LocationIdx, value: BasicValueEnum<'ctx>) -> Result<()> {
        if let Some(alloca) = self.locations.get(&loc_idx) {
            self.builder.build_store(*alloca, value)?;
        } else {
            // Create alloca for this location if it doesn't exist
            let llvm_type = value.get_type();
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
