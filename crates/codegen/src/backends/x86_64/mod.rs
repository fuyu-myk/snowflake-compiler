use std::collections::{HashMap, HashSet};

use anyhow::Result;
use iced_x86::{code_asm::*, Code, Decoder, DecoderOptions, Formatter, Instruction, IntelFormatter, MemoryOperand, NumberBase, Register};
use snowflake_common::{bug_report, IndexVec};

use snowflake_middle::ir::lir::{self, BasicBlockIdx, ConstValue, InstructionKind, LocationIdx, Operand, OperandKind, Terminator, Type};


pub struct CallingConvention<'a> {
    function: &'a lir::Function,
}

impl<'a> CallingConvention<'a> {
    pub fn new(function: &'a lir::Function) -> Self {
        Self { function }
    }

    /// Get register for integer/pointer argument by index (0-5)
    pub fn get_int_arg_register(arg_index: usize) -> Option<Register> {
        match arg_index {
            0 => Some(Register::RDI),
            1 => Some(Register::RSI), 
            2 => Some(Register::RDX),
            3 => Some(Register::RCX),
            4 => Some(Register::R8),
            5 => Some(Register::R9),
            _ => None, // Stack argument
        }
    }

    /// Get register for floating-point argument by index (0-7)
    pub fn get_float_arg_register(arg_index: usize) -> Option<Register> {
        match arg_index {
            0 => Some(Register::XMM0),
            1 => Some(Register::XMM1),
            2 => Some(Register::XMM2),
            3 => Some(Register::XMM3),
            4 => Some(Register::XMM4),
            5 => Some(Register::XMM5),
            6 => Some(Register::XMM6),
            7 => Some(Register::XMM7),
            _ => None, // Stack argument
        }
    }

    /// Get return register for the function's return type
    pub fn get_return_register(&self) -> Register {
        match &self.function.return_type {
            Type::Float32 | Type::Float64 => Register::XMM0,
            _ => Register::RAX,
        }
    }

    /// Get caller-saved registers that need preservation
    pub fn get_caller_saved_registers() -> Vec<Register> {
        vec![
            Register::RAX, Register::RCX, Register::RDX,
            Register::RSI, Register::RDI, Register::R8,
            Register::R9, Register::R10, Register::R11,
            Register::XMM0, Register::XMM1, Register::XMM2,
            Register::XMM3, Register::XMM4, Register::XMM5,
            Register::XMM6, Register::XMM7, Register::XMM8,
            Register::XMM9, Register::XMM10, Register::XMM11,
            Register::XMM12, Register::XMM13, Register::XMM14,
            Register::XMM15,
        ]
    }

    /// Get callee-saved registers
    pub fn get_callee_saved_registers() -> Vec<Register> {
        vec![
            Register::RBX, Register::RBP, Register::R12,
            Register::R13, Register::R14, Register::R15,
        ]
    }

    /// Calculate total stack space needed for arguments
    pub fn calculate_stack_arg_space(args: &[Operand]) -> usize {
        let mut int_reg_count = 0;
        let mut float_reg_count = 0;
        let mut stack_bytes = 0;

        for arg in args {
            match &arg.ty {
                Type::Float32 | Type::Float64 => {
                    if float_reg_count < 8 {
                        float_reg_count += 1;
                    } else {
                        stack_bytes += 8; // All args are 8-byte aligned on stack
                    }
                }
                _ => {
                    if int_reg_count < 6 {
                        int_reg_count += 1;
                    } else {
                        stack_bytes += 8; // All args are 8-byte aligned on stack
                    }
                }
            }
        }

        // Ensure 16-byte stack alignment
        (stack_bytes + 15) & !15
    }
}

pub struct X86_64Codegen {
    asm: CodeAssembler,
    allocator: Allocator,
    labels: HashMap<lir::BasicBlockIdx, CodeLabel>,
    function_labels: HashMap<lir::FunctionIdx, CodeLabel>,
}

impl X86_64Codegen {
    pub fn new() -> Self {
        Self {
            asm: CodeAssembler::new(64).unwrap(),
            allocator: Allocator::default(),
            labels: HashMap::new(),
            function_labels: HashMap::new(),
        }
    }

    pub fn generate(&mut self, lir: &lir::LIR) -> Result<()> {
        // Function label creation
        for (fx_idx, _fx) in lir.functions.indexed_iter() {
            let fx_label = self.asm.create_label();
            self.function_labels.insert(fx_idx, fx_label);
        }

        // Codegen for all functions
        for (fx_idx, fx) in lir.functions.indexed_iter() {
            let mut fx_label = self.function_labels[&fx_idx];
            let mut function_label_set = false;

            self.generate_function_prologue(fx, &lir)?;

            for (bb_index, bb_idx) in fx.basic_blocks.iter().copied().enumerate() {
                let bb_label = self.labels.entry(bb_idx).or_insert_with(|| self.asm.create_label());
                
                // Set function label only for the first basic block to avoid "Only one label per instruction" error
                if bb_index == 0 && !function_label_set {
                    self.asm.set_label(&mut fx_label)?;
                    function_label_set = true;
                }
                
                // Only set basic block label if it's not the first one (since function label is already set)
                if bb_index != 0 || !function_label_set {
                    self.asm.set_label(bb_label)?;
                }
                
                let bb = &lir.basic_blocks[bb_idx];

                for instruction in &bb.instructions {
                    match &instruction.kind {
                        InstructionKind::Add { target, left, right } => {
                            assert_eq!(left.ty.layout(), right.ty.layout());
                            let target_location = self.allocator.get_location_or_alloc(&lir.locations[*target]);

                            match (&left.kind, &right.kind) {
                                (OperandKind::Deref(l_loc), OperandKind::Deref(r_loc)) => {
                                    // Determine destination and source; 3 cases:
                                    if l_loc == target {
                                        // 1. `left` is the `target`, ie a = a + b
                                        //  - use `left` as destination and `right` as source
                                        let dest_location = *self.allocator.get_location_or_panic(l_loc);
                                        let src_location = *self.allocator.get_location_or_panic(r_loc);
                                        self.add(&dest_location, &src_location)?;
                                        self.allocator.locations.insert(*target, dest_location);
                                    } else if r_loc == target {
                                        // 2. `right` is the `target`, ie b = a + b
                                        //  - use `right` as destination and `left` as source
                                        let dest_location = *self.allocator.get_location_or_panic(r_loc);
                                        let src_location = *self.allocator.get_location_or_panic(l_loc);
                                        self.add(&dest_location, &src_location)?;
                                        self.allocator.locations.insert(*target, dest_location);
                                    } else {
                                        // 3. all are distinct, ie a = b + c
                                        //  - move `b` to `a` & add `c` to `a`
                                        let l_location = *self.allocator.get_location_or_panic(l_loc);
                                        self.mov(&target_location, &l_location)?;
                                        let src_location = *self.allocator.get_location_or_panic(r_loc);
                                        self.add(&target_location, &src_location)?;
                                        self.allocator.locations.insert(*target, target_location);
                                    }
                                }
                                (OperandKind::Const(_), OperandKind::Const(_)) => {
                                    bug_report!("Should be resolved during constant propagation");
                                }
                                (OperandKind::Deref(l_loc), OperandKind::Const(r_const)) => {
                                    let dest_loc = *self.allocator.get_location_or_panic(l_loc);
                                    self.add_const_int(&dest_loc, r_const)?;
                                }
                                (OperandKind::Location(l_loc), OperandKind::Location(r_loc)) => {
                                    let dest_location = *self.allocator.get_location_or_panic(&l_loc);
                                    let src_location = *self.allocator.get_location_or_panic(&r_loc);
                                    self.add(&dest_location, &src_location)?;
                                    self.allocator.locations.insert(*target, dest_location);
                                }
                                (OperandKind::Location(l_loc), OperandKind::Const(r_const)) => {
                                    let dest_location = *self.allocator.get_location_or_panic(&l_loc);
                                    self.add_const_int(&dest_location, r_const)?;
                                    self.allocator.locations.insert(*target, dest_location);
                                }
                                _ => unimplemented!("Unsupported operand combination for Add instruction: {:?} and {:?}", left, right),
                            }
                        }
                        InstructionKind::Sub { target, left, right } => {
                            self.generate_binary_op_sub(target, left, right, &lir.locations)?;
                        }
                        InstructionKind::Mul { target, left, right } => {
                            self.generate_binary_op_mul(target, left, right, &lir.locations)?;
                        }
                        InstructionKind::Div { target, left, right } => {
                            self.generate_binary_op_div(target, left, right, &lir.locations)?;
                        }
                        InstructionKind::Mod { target, left, right } => {
                            self.generate_binary_op_mod(target, left, right, &lir.locations)?;
                        }
                        InstructionKind::And { target, left, right } => {
                            self.generate_binary_op_and(target, left, right, &lir.locations)?;
                        }
                        InstructionKind::Or { target, left, right } => {
                            self.generate_binary_op_or(target, left, right, &lir.locations)?;
                        }
                        InstructionKind::Xor { target, left, right } => {
                            self.generate_binary_op_xor(target, left, right, &lir.locations)?;
                        }
                        InstructionKind::Shl { target, left, right } => {
                            self.generate_shift_op(target, left, right, &lir.locations, Code::Shl_rm64_imm8, Code::Shl_rm64_CL)?;
                        }
                        InstructionKind::Shr { target, left, right } => {
                            self.generate_shift_op(target, left, right, &lir.locations, Code::Shr_rm64_imm8, Code::Shr_rm64_CL)?;
                        }
                        InstructionKind::Eq { target, left, right } => {
                            self.generate_comparison_op(target, left, right, &lir.locations, Code::Sete_rm8)?;
                        }
                        InstructionKind::Ne { target, left, right } => {
                            self.generate_comparison_op(target, left, right, &lir.locations, Code::Setne_rm8)?;
                        }
                        InstructionKind::Lt { target, left, right } => {
                            self.generate_comparison_op(target, left, right, &lir.locations, Code::Setl_rm8)?;
                        }
                        InstructionKind::Gt { target, left, right } => {
                            self.generate_comparison_op(target, left, right, &lir.locations, Code::Setg_rm8)?;
                        }
                        InstructionKind::Le { target, left, right } => {
                            self.generate_comparison_op(target, left, right, &lir.locations, Code::Setle_rm8)?;
                        }
                        InstructionKind::Ge { target, left, right } => {
                            self.generate_comparison_op(target, left, right, &lir.locations, Code::Setge_rm8)?;
                        }
                        InstructionKind::Neg { target, operand } => {
                            self.generate_unary_op_neg(target, operand, &lir.locations)?;
                        }
                        InstructionKind::Not { target, operand } => {
                            self.generate_unary_op_not(target, operand, &lir.locations)?;
                        }
                        InstructionKind::Load { target, source } => {
                            self.generate_load(target, source, &lir.locations)?;
                        }
                        InstructionKind::Store { target, value } => {
                            self.generate_store(target, value, &lir.locations)?;
                        }
                        InstructionKind::AllocInit { value, target } => {
                            let target = &lir.locations[*target];
                            let target_loc = self.allocator.allocate_location(target);

                            match &value.kind {
                                OperandKind::Const(const_op) => match const_op {
                                    ConstValue::Int32(value) => {
                                        self.mov_i32(target_loc, *value)?;
                                    }
                                    _ => unimplemented!("Only Int32 constants are supported for comparison"),
                                }
                                OperandKind::Deref(deref_loc) => {
                                    let deref_location = *self.allocator.get_location_or_panic(deref_loc);
                                    self.mov(&target_loc, &deref_location)?;
                                }
                                _ => unimplemented!("Unsupported operand kind for AllocInit: {:?}", value.kind),
                            }
                        }
                        InstructionKind::AddressOf { target, source } => {
                            self.generate_address_of(target, source, &lir.locations)?;
                        }
                        InstructionKind::ArrayAlloc { target, element_type, size } => {
                            self.generate_array_alloc(target, element_type, size, &lir.locations)?;
                        }
                        InstructionKind::ArrayIndex { target, array, index } => {
                            self.generate_array_index(target, array, index, &lir.locations)?;
                        }
                        InstructionKind::ArrayLength { target, length } => {
                            self.generate_array_length(target, length, &lir.locations)?;
                        }
                        InstructionKind::Call { target, function, args } => {
                            self.generate_call(target, function, args, &lir.locations, lir)?;
                        }
                        InstructionKind::Move { target, source } => {
                            self.generate_move(target, source, &lir.locations)?;
                        }
                        InstructionKind::Phi { operands, .. } => {
                            // Phi nodes should be resolved before code generation
                            bug_report!("Phi nodes should be resolved before code generation: {:?}", operands);
                        }
                        InstructionKind::ArrayStore { .. } => {
                            unimplemented!("ArrayStore instruction not yet implemented for x86_64 backend");
                        }
                        InstructionKind::Tuple { .. } => {
                            unimplemented!("Tuple instruction not yet implemented for x86_64 backend");
                        }
                        InstructionKind::TupleField { .. } => {
                            unimplemented!("TupleIndex instruction not yet implemented for x86_64 backend");
                        }
                        InstructionKind::TupleStore { .. } => {
                            unimplemented!("TupleStore instruction not yet implemented for x86_64 backend");
                        }
                        InstructionKind::Nop => {
                            // nothing
                        }
                    }
                }

                match bb.terminator.as_ref() {
                    Some(terminator) => match terminator {
                        Terminator::Return { value } => {
                            if let Some(value) = value {
                                let return_register = match &value.ty {
                                    Type::Float32 | Type::Float64 => Register::XMM0,
                                    _ => Register::RAX,
                                };

                                match &value.kind {
                                    OperandKind::Const(const_op) => match const_op {
                                        ConstValue::Int32(int_value) => {
                                            self.asm.add_instruction(Instruction::with2(
                                                Code::Mov_rm64_imm32,
                                                Register::RAX,
                                                *int_value as i32,
                                            )?)?;
                                        }
                                        ConstValue::Float32(float_value) => {
                                            let bits = float_value.to_bits() as u32;
                                            
                                            self.asm.add_instruction(Instruction::with2(
                                                Code::Mov_rm64_imm32,
                                                Register::RAX,
                                                bits as i32,
                                            )?)?;
                                            
                                            self.asm.add_instruction(Instruction::with2(
                                                Code::Movq_xmm_rm64,
                                                Register::XMM0,
                                                Register::RAX,
                                            )?)?;
                                        }
                                        _ => unimplemented!("Only Int32 and Float32 constants are supported for return"),
                                    }
                                    OperandKind::Deref(loc) => {
                                        let deref_loc = *self.allocator.get_location_or_panic(loc);
                                        match return_register {
                                            Register::XMM0 => {
                                                match &value.ty {
                                                    Type::Float32 => {
                                                        match deref_loc {
                                                            Location::Register(src_reg) => {
                                                                self.asm.add_instruction(Instruction::with2(
                                                                    Code::Movq_xmm_rm64,
                                                                    Register::XMM0,
                                                                    src_reg,
                                                                )?)?;
                                                            }
                                                            Location::Stack(entry_idx) => {
                                                                self.asm.add_instruction(Instruction::with2(
                                                                    Code::Movss_xmm_xmmm32,
                                                                    Register::XMM0,
                                                                    self.memory_op_from_stack_entry(entry_idx),
                                                                )?)?;
                                                            }
                                                        }
                                                    }
                                                    Type::Float64 => {
                                                        match deref_loc {
                                                            Location::Register(src_reg) => {
                                                                self.asm.add_instruction(Instruction::with2(
                                                                    Code::Movq_xmm_rm64,
                                                                    Register::XMM0,
                                                                    src_reg,
                                                                )?)?;
                                                            }
                                                            Location::Stack(entry_idx) => {
                                                                self.asm.add_instruction(Instruction::with2(
                                                                    Code::Movsd_xmm_xmmm64,
                                                                    Register::XMM0,
                                                                    self.memory_op_from_stack_entry(entry_idx),
                                                                )?)?;
                                                            }
                                                        }
                                                    }
                                                    _ => unreachable!("Non-float type with XMM0 return register"),
                                                }
                                            }
                                            Register::RAX => {
                                                self.mov(&Location::Register(Register::RAX), &deref_loc)?;
                                            }
                                            _ => unreachable!("Unexpected return register"),
                                        }
                                    }
                                    OperandKind::Location(loc) => {
                                        let location = *self.allocator.get_location_or_panic(loc);
                                        match return_register {
                                            Register::XMM0 => {
                                                match &value.ty {
                                                    Type::Float32 => {
                                                        match location {
                                                            Location::Register(src_reg) => {
                                                                self.asm.add_instruction(Instruction::with2(
                                                                    Code::Movq_xmm_rm64,
                                                                    Register::XMM0,
                                                                    src_reg,
                                                                )?)?;
                                                            }
                                                            Location::Stack(entry_idx) => {
                                                                self.asm.add_instruction(Instruction::with2(
                                                                    Code::Movss_xmm_xmmm32,
                                                                    Register::XMM0,
                                                                    self.memory_op_from_stack_entry(entry_idx),
                                                                )?)?;
                                                            }
                                                        }
                                                    }
                                                    Type::Float64 => {
                                                        match location {
                                                            Location::Register(src_reg) => {
                                                                self.asm.add_instruction(Instruction::with2(
                                                                    Code::Movq_xmm_rm64,
                                                                    Register::XMM0,
                                                                    src_reg,
                                                                )?)?;
                                                            }
                                                            Location::Stack(entry_idx) => {
                                                                self.asm.add_instruction(Instruction::with2(
                                                                    Code::Movsd_xmm_xmmm64,
                                                                    Register::XMM0,
                                                                    self.memory_op_from_stack_entry(entry_idx),
                                                                )?)?;
                                                            }
                                                        }
                                                    }
                                                    _ => unreachable!("Non-float type with XMM0 return register"),
                                                }
                                            }
                                            Register::RAX => {
                                                self.mov(&Location::Register(Register::RAX), &location)?;
                                            }
                                            _ => unreachable!("Unexpected return register"),
                                        }
                                    }
                                    _ => unimplemented!("Unsupported operand kind for return: {:?}", value.kind),
                                }
                            }

                            self.generate_function_epilogue()?;
                        }
                        Terminator::Goto { target } => {
                            let target_label = self.labels.entry(*target).or_insert_with(|| self.asm.create_label());
                            self.asm.jmp(*target_label)?;
                        }
                        Terminator::Branch { condition, true_target, false_target } => {
                            self.generate_conditional_branch(condition, *true_target, *false_target)?;
                        }
                        Terminator::Switch { value, targets, default_target } => {
                            self.generate_switch(value, targets, *default_target)?;
                        }
                        Terminator::Unreachable { error } => {
                            panic!("Error: {}", error)
                        }
                        Terminator::Panic { .. } => {
                            // TODO: runtime panic here
                            self.asm.ud2()?;
                        }
                    }
                    None => bug_report!("Basic block {:?} has no terminator", bb_idx),
                }
            }
        }

        Ok(())
    }

    fn add_const_int(&mut self, dest_loc: &Location, r_const: &ConstValue) -> Result<()> {
        match r_const {
            ConstValue::Int32(value) => match dest_loc {
                Location::Register(reg) => {
                    self.asm.add_instruction(Instruction::with2(
                        Code::Add_rm64_imm32,
                        *reg,
                        *value as i32,
                    )?)?;
                }
                Location::Stack(entry_idx) => {
                    self.asm.add_instruction(Instruction::with2(
                        Code::Add_rm64_imm32,
                        self.memory_op_from_stack_entry(*entry_idx),
                        *value as i32,
                    )?)?;
                }
            }
            _ => unimplemented!("Only Int32 constants are supported for now"),
        }

        Ok(())
    }

    fn add(&mut self, dest_location: &Location, src_location: &Location) -> Result<()> {
        match (dest_location, src_location) {
            (Location::Register(dest_reg), Location::Register(src_reg)) => {
                // `dest` in reg && `src` in reg: ADD r64, r/m64
                self.asm.add_instruction(Instruction::with2(
                    Code::Add_r64_rm64,
                    *dest_reg,
                    *src_reg,
                )?)?;
            }
            (Location::Stack(dest_entry_idx), Location::Stack(src_entry_idx)) => {
                // `dest` in mem && `src` in mem:
                // Move `dest` to free reg; ADD r64, r/m64
                let (dest_reg, spilled) = self.allocator.move_stack_to_free_reg(*dest_entry_idx);
                if let Some(spilled) = spilled {
                    self.do_spill(spilled)?;
                }

                self.asm.add_instruction(Instruction::with2(
                    Code::Add_r64_rm64,
                    dest_reg,
                    self.memory_op_from_stack_entry(*src_entry_idx),
                )?)?;
            }
            (Location::Register(dest_reg), Location::Stack(src_entry_idx)) => {
                // `dest` in reg && `src` in mem: ADD r64, r/m64
                self.asm.add_instruction(Instruction::with2(
                    Code::Add_r64_rm64,
                    *dest_reg,
                    self.memory_op_from_stack_entry(*src_entry_idx),
                )?)?;
            }
            (Location::Stack(dest_entry_idx), Location::Register(src_reg)) => {
                // `dest` in mem && `src` in reg: ADD r/m64, r64
                self.asm.add_instruction(Instruction::with2(
                    Code::Add_rm64_r64,
                    self.memory_op_from_stack_entry(*dest_entry_idx),
                    *src_reg,
                )?)?;
            }
        }

        Ok(())
    }

    fn mov_i32(&mut self, loc: Location, value: i32) -> Result<()> {
        match loc {
            Location::Register(reg) => {
                self.asm.add_instruction(Instruction::with2(
                    Code::Mov_rm64_imm32,
                    reg,
                    value as i32,
                )?)?;
            }
            Location::Stack(entry_idx) => {
                assert_eq!(entry_idx, self.allocator.frame.entries.len() - 1, "Cannot move to a non-top stack entry");
                self.asm.add_instruction(Instruction::with2(
                    Code::Mov_rm64_imm32,
                    self.memory_op_from_stack_entry(entry_idx),
                    value as i32,
                )?)?;
            }
        };

        Ok(())
    }

    fn mov(&mut self, dest: &Location, src: &Location) -> Result<()> {
        // Eliminate redundant moves (same source and target)
        if std::mem::discriminant(dest) == std::mem::discriminant(src) {
            match (dest, src) {
                (Location::Register(dest_reg), Location::Register(src_reg)) if dest_reg == src_reg => {
                    return Ok(());
                }
                (Location::Stack(dest_entry), Location::Stack(src_entry)) if dest_entry == src_entry => {
                    return Ok(());
                }
                _ => {}
            }
        }
        
        match (dest, src) {
            (Location::Register(dest_reg), Location::Register(src_reg)) => {
                self.asm.add_instruction(Instruction::with2(
                    Code::Mov_r64_rm64,
                    *dest_reg,
                    *src_reg,
                )?)?;
            }
            (Location::Stack(dest_entry_idx), Location::Stack(src_entry_idx)) => {
                let (dest_reg, spilled) = self.allocator.move_stack_to_free_reg(*dest_entry_idx);
                if let Some(spilled) = spilled {
                    self.do_spill(spilled)?;
                }

                self.asm.add_instruction(Instruction::with2(
                    Code::Mov_r64_rm64,
                    dest_reg,
                    self.memory_op_from_stack_entry(*src_entry_idx),
                )?)?;
            }
            (Location::Register(dest_reg), Location::Stack(src_entry_idx)) => {
                self.asm.add_instruction(Instruction::with2(
                    Code::Mov_r64_rm64,
                    *dest_reg,
                    self.memory_op_from_stack_entry(*src_entry_idx),
                )?)?;
            }
            (Location::Stack(dest_entry_idx), Location::Register(src_reg)) => {
                self.asm.add_instruction(Instruction::with2(
                    Code::Mov_rm64_r64,
                    self.memory_op_from_stack_entry(*dest_entry_idx),
                    *src_reg,
                )?)?;
            }
        }

        Ok(())
    }

    fn do_spill(&mut self, (_, reg, stack_idx): Spilled) -> Result<()> {
        self.asm.add_instruction(Instruction::with2(
            Code::Mov_rm64_r64,
            self.memory_op_from_stack_entry(stack_idx),
            reg,
        )?)?;

        Ok(())
    }

    fn memory_op_from_stack_entry(&self, stack_entry_idx: usize) -> MemoryOperand {
        let stack_offset = self.allocator.frame.get_entry(stack_entry_idx).offset;
        MemoryOperand::with_base_displ(Register::RBP, -(stack_offset as i64) - 8)
    }

    pub fn get_asm_output(&mut self) -> Result<String> {
        let data = self.asm.assemble(0)?;
        let mut decoder = Decoder::with_ip(64, &data, 0, DecoderOptions::NONE);
        let mut formatter = IntelFormatter::new();
        formatter.options_mut().set_number_base(NumberBase::Decimal);
        let mut unformatted_output = String::new();
        let mut formatted_output = String::new();
        let mut instruction = Instruction::default();

        while decoder.can_decode() {
            decoder.decode_out(&mut instruction);
            unformatted_output.clear();
            formatter.format(&instruction, &mut unformatted_output);
            formatted_output.push_str(&unformatted_output);
            formatted_output.push('\n');
        }

        Ok(formatted_output)
    }

    // Helper methods for binary operations
    fn generate_binary_op_sub(
        &mut self,
        target: &LocationIdx,
        left: &Operand,
        right: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        match (&left.kind, &right.kind) {
            (OperandKind::Deref(l_loc), OperandKind::Deref(r_loc)) => {
                let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
                
                let (dest, src) = if l_loc == target {
                    (*l_loc, *r_loc)
                } else if r_loc == target {
                    (*r_loc, *l_loc)
                } else {
                    let l_location = *self.allocator.get_location_or_panic(l_loc);
                    self.mov(&target_location, &l_location)?;
                    (*target, *r_loc)
                };

                let dest_location = *self.allocator.get_location_or_panic(&dest);
                let src_location = *self.allocator.get_location_or_panic(&src);

                match (dest_location, src_location) {
                    (Location::Register(dest_reg), Location::Register(src_reg)) => {
                        self.asm.add_instruction(Instruction::with2(Code::Sub_r64_rm64, dest_reg, src_reg)?)?;
                    }
                    (Location::Register(dest_reg), Location::Stack(src_entry)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Sub_r64_rm64,
                            dest_reg,
                            self.memory_op_from_stack_entry(src_entry),
                        )?)?;
                    }
                    (Location::Stack(dest_entry), Location::Register(src_reg)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Sub_rm64_r64,
                            self.memory_op_from_stack_entry(dest_entry),
                            src_reg,
                        )?)?;
                    }
                    (Location::Stack(dest_entry), Location::Stack(src_entry)) => {
                        // Need to load source to register first
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(src_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Sub_rm64_r64,
                            self.memory_op_from_stack_entry(dest_entry),
                            temp_reg,
                        )?)?;
                    }
                }
            }
            (OperandKind::Const(_), OperandKind::Const(_)) => {
                bug_report!("Should be resolved during constant propagation");
            }
            (OperandKind::Deref(_), OperandKind::Const(_)) => {
                unimplemented!("Constant operations not yet implemented for subtraction");
            }
            _ => unimplemented!("Unsupported operand combination"),
        }
        Ok(())
    }

    fn generate_binary_op_mul(
        &mut self,
        target: &LocationIdx,
        left: &Operand,
        right: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        match (&left.kind, &right.kind) {
            (OperandKind::Deref(l_loc), OperandKind::Deref(r_loc)) => {
                let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
                
                let (dest, src) = if l_loc == target {
                    (*l_loc, *r_loc)
                } else if r_loc == target {
                    (*r_loc, *l_loc)
                } else {
                    let l_location = *self.allocator.get_location_or_panic(l_loc);
                    self.mov(&target_location, &l_location)?;
                    (*target, *r_loc)
                };

                let dest_location = *self.allocator.get_location_or_panic(&dest);
                let src_location = *self.allocator.get_location_or_panic(&src);

                match (dest_location, src_location) {
                    (Location::Register(dest_reg), Location::Register(src_reg)) => {
                        self.asm.add_instruction(Instruction::with2(Code::Imul_r64_rm64, dest_reg, src_reg)?)?;
                    }
                    (Location::Register(dest_reg), Location::Stack(src_entry)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Imul_r64_rm64,
                            dest_reg,
                            self.memory_op_from_stack_entry(src_entry),
                        )?)?;
                    }
                    (Location::Stack(dest_entry), Location::Register(src_reg)) => {
                        // Load destination to register, multiply, store back
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(dest_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(Code::Imul_r64_rm64, temp_reg, src_reg)?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(dest_entry),
                            temp_reg,
                        )?)?;
                    }
                    (Location::Stack(dest_entry), Location::Stack(src_entry)) => {
                        // Load both to registers, multiply, store back
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(dest_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Imul_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(src_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(dest_entry),
                            temp_reg,
                        )?)?;
                    }
                }
            }
            (OperandKind::Const(_), OperandKind::Const(_)) => {
                bug_report!("Should be resolved during constant propagation");
            }
            (OperandKind::Deref(_), OperandKind::Const(_)) => {
                unimplemented!("Constant operations not yet implemented for multiplication");
            }
            _ => unimplemented!("Unsupported operand combination"),
        }
        Ok(())
    }

    fn generate_binary_op_div(
        &mut self,
        target: &LocationIdx,
        left: &Operand,
        right: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // Dividend goes in RAX (and RDX for 128-bit)  
        // Divisor is the operand to the DIV instruction
        // Quotient result is in RAX, remainder in RDX
        
        // For signed division, we use IDIV (Integer DIVide)
        // Pattern: mov rax, dividend; cqo; idiv divisor
        // cqo sign-extends RAX into RDX:RAX for 128-bit dividend
        
        match (&left.kind, &right.kind) {
            (OperandKind::Deref(dividend_loc), OperandKind::Deref(divisor_loc)) => {
                // Save current RAX and RDX if they're being used
                // (TODO: handle by register allocation)
                
                // Load dividend into RAX
                let dividend_location = *self.allocator.get_location_or_panic(dividend_loc);
                match dividend_location {
                    Location::Register(reg) if reg != Register::RAX => {
                        self.asm.add_instruction(Instruction::with2(Code::Mov_r64_rm64, Register::RAX, reg)?)?;
                    }
                    Location::Stack(entry) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            Register::RAX,
                            self.memory_op_from_stack_entry(entry),
                        )?)?;
                    }
                    Location::Register(Register::RAX) => {
                        // Already in RAX, no move needed
                    }
                    _ => unreachable!(),
                }

                // Sign extend RAX into RDX:RAX (required for IDIV)
                self.asm.add_instruction(Instruction::with(Code::Cqo))?;

                // Perform division
                let divisor_location = *self.allocator.get_location_or_panic(divisor_loc);
                match divisor_location {
                    Location::Register(reg) => {
                        self.asm.add_instruction(Instruction::with1(Code::Idiv_rm64, reg)?)?;
                    }
                    Location::Stack(entry) => {
                        self.asm.add_instruction(Instruction::with1(
                            Code::Idiv_rm64,
                            self.memory_op_from_stack_entry(entry),
                        )?)?;
                    }
                }

                // Move result from RAX to target location
                let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
                match target_location {
                    Location::Register(Register::RAX) => {
                        // Result already in target, no move needed
                    }
                    Location::Register(reg) => {
                        self.asm.add_instruction(Instruction::with2(Code::Mov_r64_rm64, reg, Register::RAX)?)?;
                    }
                    Location::Stack(entry) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(entry),
                            Register::RAX,
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Only deref operands supported for division"),
        }
        Ok(())
    }

    fn generate_binary_op_mod(
        &mut self,
        target: &LocationIdx,
        left: &Operand,
        right: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // Modulo uses the same IDIV instruction as division
        // The remainder is left in RDX after division
        // Essentially the same as division but we take RDX instead of RAX
        
        match (&left.kind, &right.kind) {
            (OperandKind::Deref(dividend_loc), OperandKind::Deref(divisor_loc)) => {
                // Load dividend into RAX (same as division)
                let dividend_location = *self.allocator.get_location_or_panic(dividend_loc);
                match dividend_location {
                    Location::Register(reg) if reg != Register::RAX => {
                        self.asm.add_instruction(Instruction::with2(Code::Mov_r64_rm64, Register::RAX, reg)?)?;
                    }
                    Location::Stack(entry) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            Register::RAX,
                            self.memory_op_from_stack_entry(entry),
                        )?)?;
                    }
                    Location::Register(Register::RAX) => {
                        // Already in RAX
                    }
                    _ => unreachable!(),
                }

                // Sign extend RAX into RDX:RAX
                self.asm.add_instruction(Instruction::with(Code::Cqo))?;

                // Perform division (remainder goes to RDX)
                let divisor_location = *self.allocator.get_location_or_panic(divisor_loc);
                match divisor_location {
                    Location::Register(reg) => {
                        self.asm.add_instruction(Instruction::with1(Code::Idiv_rm64, reg)?)?;
                    }
                    Location::Stack(entry) => {
                        self.asm.add_instruction(Instruction::with1(
                            Code::Idiv_rm64,
                            self.memory_op_from_stack_entry(entry),
                        )?)?;
                    }
                }

                // Move remainder from RDX to target location
                let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
                match target_location {
                    Location::Register(Register::RDX) => {
                        // Result already in target
                    }
                    Location::Register(reg) => {
                        self.asm.add_instruction(Instruction::with2(Code::Mov_r64_rm64, reg, Register::RDX)?)?;
                    }
                    Location::Stack(entry) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(entry),
                            Register::RDX,
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Only deref operands supported for modulo"),
        }
        Ok(())
    }

    fn generate_binary_op_and(
        &mut self,
        target: &LocationIdx,
        left: &Operand,
        right: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // Bitwise AND operation
        // Assembly: AND dest, src  (dest = dest & src)
        // Similar to ADD/SUB but with AND instruction
        
        match (&left.kind, &right.kind) {
            (OperandKind::Deref(l_loc), OperandKind::Deref(r_loc)) => {
                let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
                
                // Choose which operand to use as destination
                let (dest, src) = if l_loc == target {
                    (*l_loc, *r_loc)
                } else if r_loc == target {
                    (*r_loc, *l_loc)
                } else {
                    // Need to move left operand to target first
                    let l_location = *self.allocator.get_location_or_panic(l_loc);
                    self.mov(&target_location, &l_location)?;
                    (*target, *r_loc)
                };

                let dest_location = *self.allocator.get_location_or_panic(&dest);
                let src_location = *self.allocator.get_location_or_panic(&src);

                match (dest_location, src_location) {
                    (Location::Register(dest_reg), Location::Register(src_reg)) => {
                        self.asm.add_instruction(Instruction::with2(Code::And_r64_rm64, dest_reg, src_reg)?)?;
                    }
                    (Location::Register(dest_reg), Location::Stack(src_entry)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::And_r64_rm64,
                            dest_reg,
                            self.memory_op_from_stack_entry(src_entry),
                        )?)?;
                    }
                    (Location::Stack(dest_entry), Location::Register(src_reg)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::And_rm64_r64,
                            self.memory_op_from_stack_entry(dest_entry),
                            src_reg,
                        )?)?;
                    }
                    (Location::Stack(dest_entry), Location::Stack(src_entry)) => {
                        // Load source to temporary register first
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(src_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::And_rm64_r64,
                            self.memory_op_from_stack_entry(dest_entry),
                            temp_reg,
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Unsupported operand combination for AND"),
        }
        Ok(())
    }

    fn generate_binary_op_or(
        &mut self,
        target: &LocationIdx,
        left: &Operand,
        right: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // Bitwise OR operation  
        // Assembly: OR dest, src  (dest = dest | src)
        // Same pattern as AND but with OR instruction
        
        match (&left.kind, &right.kind) {
            (OperandKind::Deref(l_loc), OperandKind::Deref(r_loc)) => {
                let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
                
                let (dest, src) = if l_loc == target {
                    (*l_loc, *r_loc)
                } else if r_loc == target {
                    (*r_loc, *l_loc)
                } else {
                    let l_location = *self.allocator.get_location_or_panic(l_loc);
                    self.mov(&target_location, &l_location)?;
                    (*target, *r_loc)
                };

                let dest_location = *self.allocator.get_location_or_panic(&dest);
                let src_location = *self.allocator.get_location_or_panic(&src);

                match (dest_location, src_location) {
                    (Location::Register(dest_reg), Location::Register(src_reg)) => {
                        self.asm.add_instruction(Instruction::with2(Code::Or_r64_rm64, dest_reg, src_reg)?)?;
                    }
                    (Location::Register(dest_reg), Location::Stack(src_entry)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Or_r64_rm64,
                            dest_reg,
                            self.memory_op_from_stack_entry(src_entry),
                        )?)?;
                    }
                    (Location::Stack(dest_entry), Location::Register(src_reg)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Or_rm64_r64,
                            self.memory_op_from_stack_entry(dest_entry),
                            src_reg,
                        )?)?;
                    }
                    (Location::Stack(dest_entry), Location::Stack(src_entry)) => {
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(src_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Or_rm64_r64,
                            self.memory_op_from_stack_entry(dest_entry),
                            temp_reg,
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Unsupported operand combination for OR"),
        }
        Ok(())
    }

    fn generate_binary_op_xor(
        &mut self,
        target: &LocationIdx,
        left: &Operand,
        right: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // Bitwise XOR (exclusive OR) operation
        // Assembly: XOR dest, src  (dest = dest ^ src)
        // For future ref: XOR reg, reg is a common idiom to zero a register (faster than MOV reg, 0)
        
        match (&left.kind, &right.kind) {
            (OperandKind::Deref(l_loc), OperandKind::Deref(r_loc)) => {
                let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
                
                let (dest, src) = if l_loc == target {
                    (*l_loc, *r_loc)
                } else if r_loc == target {
                    (*r_loc, *l_loc)
                } else {
                    let l_location = *self.allocator.get_location_or_panic(l_loc);
                    self.mov(&target_location, &l_location)?;
                    (*target, *r_loc)
                };

                let dest_location = *self.allocator.get_location_or_panic(&dest);
                let src_location = *self.allocator.get_location_or_panic(&src);

                match (dest_location, src_location) {
                    (Location::Register(dest_reg), Location::Register(src_reg)) => {
                        self.asm.add_instruction(Instruction::with2(Code::Xor_r64_rm64, dest_reg, src_reg)?)?;
                    }
                    (Location::Register(dest_reg), Location::Stack(src_entry)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Xor_r64_rm64,
                            dest_reg,
                            self.memory_op_from_stack_entry(src_entry),
                        )?)?;
                    }
                    (Location::Stack(dest_entry), Location::Register(src_reg)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Xor_rm64_r64,
                            self.memory_op_from_stack_entry(dest_entry),
                            src_reg,
                        )?)?;
                    }
                    (Location::Stack(dest_entry), Location::Stack(src_entry)) => {
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(src_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Xor_rm64_r64,
                            self.memory_op_from_stack_entry(dest_entry),
                            temp_reg,
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Unsupported operand combination for XOR"),
        }
        Ok(())
    }

    fn generate_shift_op(
        &mut self,
        target: &LocationIdx,
        left: &Operand,
        right: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
        imm_code: Code,
        cl_code: Code,
    ) -> Result<()> {
        // Shift operations in x86-64:
        // - Can shift by immediate value (0-63): SHL/SHR reg, imm8
        // - Can shift by CL register: SHL/SHR reg, cl
        // - The shift amount must be in CL (lowest 8 bits of RCX)
        
        match (&left.kind, &right.kind) {
            (OperandKind::Deref(value_loc), OperandKind::Deref(shift_loc)) => {
                let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
                
                if value_loc != target {
                    let value_location = *self.allocator.get_location_or_panic(value_loc);
                    self.mov(&target_location, &value_location)?;
                }

                // Load shift amount into CL register
                let shift_location = *self.allocator.get_location_or_panic(shift_loc);
                match shift_location {
                    Location::Register(Register::RCX) => {
                        // Already in RCX
                    }
                    Location::Register(reg) => {
                        // Move from other register to RCX
                        self.asm.add_instruction(Instruction::with2(Code::Mov_r64_rm64, Register::RCX, reg)?)?;
                    }
                    Location::Stack(entry) => {
                        // Load from stack to RCX
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            Register::RCX,
                            self.memory_op_from_stack_entry(entry),
                        )?)?;
                    }
                }

                // Perform the shift operation with CL
                match target_location {
                    Location::Register(reg) => {
                        self.asm.add_instruction(Instruction::with1(cl_code, reg)?)?;
                    }
                    Location::Stack(entry) => {
                        self.asm.add_instruction(Instruction::with1(
                            cl_code,
                            self.memory_op_from_stack_entry(entry),
                        )?)?;
                    }
                }
            }
            (OperandKind::Deref(value_loc), OperandKind::Const(ConstValue::Int32(shift_amount))) => {
                // Immediate shift - more efficient than using CL register
                let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
                
                if value_loc != target {
                    let value_location = *self.allocator.get_location_or_panic(value_loc);
                    self.mov(&target_location, &value_location)?;
                }

                // Perform immediate shift (shift amount must be 0-63)
                let shift_imm = *shift_amount as i32;
                match target_location {
                    Location::Register(reg) => {
                        self.asm.add_instruction(Instruction::with2(imm_code, reg, shift_imm)?)?;
                    }
                    Location::Stack(entry) => {
                        self.asm.add_instruction(Instruction::with2(
                            imm_code,
                            self.memory_op_from_stack_entry(entry),
                            shift_imm,
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Unsupported operand combination for shift"),
        }
        Ok(())
    }

    fn generate_comparison_op(
        &mut self,
        target: &LocationIdx,
        left: &Operand,
        right: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
        set_code: Code,
    ) -> Result<()> {
        match (&left.kind, &right.kind) {
            (OperandKind::Deref(l_loc), OperandKind::Deref(r_loc)) => {
                let l_location = self.allocator.get_location_or_alloc(&locations[*l_loc]);
                let r_location = self.allocator.get_location_or_alloc(&locations[*r_loc]);
                match (l_location, r_location) {
                    (Location::Register(l_reg), Location::Register(r_reg)) => {
                        self.asm.add_instruction(Instruction::with2(Code::Cmp_r64_rm64, l_reg, r_reg)?)?;
                    }
                    (Location::Stack(l_entry_idx), Location::Stack(r_entry_idx)) => {
                        let (l_reg, spilled) = self.allocator.move_stack_to_free_reg(l_entry_idx);
                        if let Some(spilled) = spilled {
                            self.do_spill(spilled)?;
                        }
                        self.asm.add_instruction(Instruction::with2(
                            Code::Cmp_r64_rm64,
                            l_reg,
                            self.memory_op_from_stack_entry(r_entry_idx),
                        )?)?;
                    }
                    (Location::Register(l_reg), Location::Stack(r_entry_idx)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Cmp_r64_rm64,
                            l_reg,
                            self.memory_op_from_stack_entry(r_entry_idx),
                        )?)?;
                    }
                    (Location::Stack(l_entry_idx), Location::Register(r_reg)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Cmp_rm64_r64,
                            self.memory_op_from_stack_entry(l_entry_idx),
                            r_reg,
                        )?)?;
                    }
                }
            }
            (OperandKind::Location(l_loc), OperandKind::Location(r_loc)) => {
                let l_location = self.allocator.get_location_or_alloc(&locations[*l_loc]);
                let r_location = self.allocator.get_location_or_alloc(&locations[*r_loc]);
                match (l_location, r_location) {
                    (Location::Register(l_reg), Location::Register(r_reg)) => {
                        self.asm.add_instruction(Instruction::with2(Code::Cmp_r64_rm64, l_reg, r_reg)?)?;
                    }
                    (Location::Stack(l_entry_idx), Location::Stack(r_entry_idx)) => {
                        let (l_reg, spilled) = self.allocator.move_stack_to_free_reg(l_entry_idx);
                        if let Some(spilled) = spilled {
                            self.do_spill(spilled)?;
                        }
                        self.asm.add_instruction(Instruction::with2(
                            Code::Cmp_r64_rm64,
                            l_reg,
                            self.memory_op_from_stack_entry(r_entry_idx),
                        )?)?;
                    }
                    (Location::Register(l_reg), Location::Stack(r_entry_idx)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Cmp_r64_rm64,
                            l_reg,
                            self.memory_op_from_stack_entry(r_entry_idx),
                        )?)?;
                    }
                    (Location::Stack(l_entry_idx), Location::Register(r_reg)) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Cmp_rm64_r64,
                            self.memory_op_from_stack_entry(l_entry_idx),
                            r_reg,
                        )?)?;
                    }
                }
            }
            (OperandKind::Const(_), OperandKind::Const(_)) => {
                bug_report!("Should be resolved during constant propagation");
            }
            (OperandKind::Deref(l_loc), OperandKind::Const(const_op)) |
            (OperandKind::Const(const_op), OperandKind::Deref(l_loc)) => {
                let l_location = self.allocator.get_location_or_alloc(&locations[*l_loc]);
                match l_location {
                    Location::Register(reg) => match *const_op {
                        ConstValue::Int32(value) => {
                            self.asm.add_instruction(Instruction::with2(
                                Code::Cmp_rm64_imm32,
                                reg,
                                value as i32,
                            )?)?;
                        }
                        _ => unimplemented!("Only Int32 constants are supported for comparison"),
                    },
                    Location::Stack(l_entry_idx) => match *const_op {
                        ConstValue::Int32(value) => {
                            self.asm.add_instruction(Instruction::with2(
                                Code::Cmp_rm64_imm32,
                                self.memory_op_from_stack_entry(l_entry_idx),
                                value as i32,
                            )?)?;
                        }
                        _ => unimplemented!("Only Int32 constants are supported for comparison"),
                    }
                }
            }
            (OperandKind::Location(l_loc), OperandKind::Const(const_op)) |
            (OperandKind::Const(const_op), OperandKind::Location(l_loc)) => {
                let l_location = self.allocator.get_location_or_alloc(&locations[*l_loc]);
                match l_location {
                    Location::Register(reg) => match *const_op {
                        ConstValue::Int32(value) => {
                            self.asm.add_instruction(Instruction::with2(
                                Code::Cmp_rm64_imm32,
                                reg,
                                value as i32,
                            )?)?;
                        }
                        _ => unimplemented!("Only Int32 constants are supported for comparison"),
                    },
                    Location::Stack(l_entry_idx) => match *const_op {
                        ConstValue::Int32(value) => {
                            self.asm.add_instruction(Instruction::with2(
                                Code::Cmp_rm64_imm32,
                                self.memory_op_from_stack_entry(l_entry_idx),
                                value as i32,
                            )?)?;
                        }
                        _ => unimplemented!("Only Int32 constants are supported for comparison"),
                    }
                }
            }
            _ => bug_report!("Unsupported operand combination for comparison"),
        }

        let _target_location = self.allocator.get_location_or_alloc(&locations[*target]);

        let (reg, spilled) = self.allocator.get_free_register(Type::Int64);
        if let Some(spilled) = spilled {
            self.do_spill(spilled)?;
        }

        // Convert 64-bit register to 8-bit equivalent for set instruction
        let reg_8bit = match reg {
            Register::RAX => Register::AL,
            Register::RBX => Register::BL,
            Register::RCX => Register::CL,
            Register::RDX => Register::DL,
            Register::RSI => Register::SIL,
            Register::RDI => Register::DIL,
            Register::R8 => Register::R8L,
            Register::R9 => Register::R9L,
            Register::R10 => Register::R10L,
            Register::R11 => Register::R11L,
            Register::R12 => Register::R12L,
            Register::R13 => Register::R13L,
            Register::R14 => Register::R14L,
            Register::R15 => Register::R15L,
            _ => bug_report!("Unsupported register for 8-bit conversion: {:?}", reg),
        };

        self.asm.add_instruction(Instruction::with1(set_code, reg_8bit)?)?;
        self.allocator.free_register(reg);

        let (target_reg, spilled) = self.allocator.ensure_in_reg(*target)?;
        if let Some(spilled) = spilled {
            self.do_spill(spilled)?;
        }

        self.asm.add_instruction(Instruction::with2(Code::Movzx_r64_rm8, target_reg, reg_8bit)?)?;
        
        Ok(())
    }

    // Unary operations
    fn generate_unary_op_neg(
        &mut self,
        target: &LocationIdx,
        operand: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
        
        match &operand.kind {
            OperandKind::Deref(loc) => {
                let src_location = *self.allocator.get_location_or_panic(loc);
                if loc != target {
                    self.mov(&target_location, &src_location)?;
                }
                
                match target_location {
                    Location::Register(reg) => {
                        self.asm.add_instruction(Instruction::with1(Code::Neg_rm64, reg)?)?;
                    }
                    Location::Stack(entry) => {
                        self.asm.add_instruction(Instruction::with1(
                            Code::Neg_rm64,
                            self.memory_op_from_stack_entry(entry),
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Only deref operands supported for negation"),
        }
        
        Ok(())
    }

    fn generate_unary_op_not(
        &mut self,
        target: &LocationIdx,
        operand: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
        
        match &operand.kind {
            OperandKind::Deref(loc) => {
                let src_location = *self.allocator.get_location_or_panic(loc);
                if loc != target {
                    self.mov(&target_location, &src_location)?;
                }
                
                match target_location {
                    Location::Register(reg) => {
                        self.asm.add_instruction(Instruction::with1(Code::Not_rm64, reg)?)?;
                    }
                    Location::Stack(entry) => {
                        self.asm.add_instruction(Instruction::with1(
                            Code::Not_rm64,
                            self.memory_op_from_stack_entry(entry),
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Only deref operands supported for bitwise not"),
        }
        
        Ok(())
    }

    // Memory operations
    fn generate_load(
        &mut self,
        target: &LocationIdx,
        source: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // Load operation: target = *source
        // This dereferences a pointer and loads the value it points to
        // Assembly: MOV target, [source_ptr]
        
        let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
        
        match &source.kind {
            OperandKind::Deref(ptr_loc) => {
                let ptr_location = *self.allocator.get_location_or_panic(ptr_loc);
                
                match (target_location, ptr_location) {
                    (Location::Register(target_reg), Location::Register(ptr_reg)) => {
                        // Load value from memory address in ptr_reg into target_reg
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            target_reg,
                            MemoryOperand::with_base(ptr_reg),
                        )?)?;
                    }
                    (Location::Register(target_reg), Location::Stack(ptr_entry)) => {
                        // Load pointer from stack, then dereference it
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(ptr_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            target_reg,
                            MemoryOperand::with_base(temp_reg),
                        )?)?;
                    }
                    (Location::Stack(target_entry), Location::Register(ptr_reg)) => {
                        // Load from memory into temporary, then store to stack
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            MemoryOperand::with_base(ptr_reg),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(target_entry),
                            temp_reg,
                        )?)?;
                    }
                    (Location::Stack(target_entry), Location::Stack(ptr_entry)) => {
                        // Load pointer from stack, dereference, store result
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(ptr_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            MemoryOperand::with_base(temp_reg),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(target_entry),
                            temp_reg,
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Only deref operands supported for loads"),
        }
        
        Ok(())
    }

    fn generate_store(
        &mut self,
        target: &Operand,
        value: &Operand,
        _locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // Store operation: *target = value
        // This stores a value to the memory location pointed to by target
        // Assembly: MOV [target_ptr], value
        
        match (&target.kind, &value.kind) {
            (OperandKind::Deref(ptr_loc), OperandKind::Deref(value_loc)) => {
                let ptr_location = *self.allocator.get_location_or_panic(ptr_loc);
                let value_location = *self.allocator.get_location_or_panic(value_loc);
                
                match (ptr_location, value_location) {
                    (Location::Register(ptr_reg), Location::Register(value_reg)) => {
                        // Store value_reg to memory location pointed by ptr_reg
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            MemoryOperand::with_base(ptr_reg),
                            value_reg,
                        )?)?;
                    }
                    (Location::Register(ptr_reg), Location::Stack(value_entry)) => {
                        // Load value from stack, then store to memory
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(value_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            MemoryOperand::with_base(ptr_reg),
                            temp_reg,
                        )?)?;
                    }
                    (Location::Stack(ptr_entry), Location::Register(value_reg)) => {
                        // Load pointer from stack, then store value to that address
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(ptr_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            MemoryOperand::with_base(temp_reg),
                            value_reg,
                        )?)?;
                    }
                    (Location::Stack(ptr_entry), Location::Stack(value_entry)) => {
                        // Load both pointer and value, then store
                        let ptr_reg = Register::RAX;
                        let value_reg = Register::RBX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            ptr_reg,
                            self.memory_op_from_stack_entry(ptr_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            value_reg,
                            self.memory_op_from_stack_entry(value_entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            MemoryOperand::with_base(ptr_reg),
                            value_reg,
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Only deref operands supported for stores"),
        }
        
        Ok(())
    }

    fn generate_address_of(
        &mut self,
        _target: &LocationIdx,
        _source: &LocationIdx,
        _locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // AddressOf operation: target = &source
        // This gets the address of a variable (like & in C)
        // Assembly: LEA target, [source_address]
        // LEA (Load Effective Address) calculates address without dereferencing
        unimplemented!("AddressOf operation - would use LEA instruction")
    }

    // Array operations
    fn generate_array_alloc(
        &mut self,
        target: &LocationIdx,
        element_type: &Type,
        size: &Operand,
        _locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // AllocateArray operation: target = new Array[size]
        // This allocates memory for an array on the stack
        
        // Calculate total bytes needed (size * element_size)
        let element_size = match element_type {
            Type::Int8 => 1,
            Type::Int16 => 2,
            Type::Int32 => 4,
            Type::Int64 => 8,
            Type::UInt8 => 1,
            Type::UInt16 => 2,
            Type::UInt32 => 4,
            Type::UInt64 => 8,
            Type::Float32 => 4,
            Type::Float64 => 8,
            Type::Bool => 1,
            _ => 8,  // Default to 8 bytes for pointers etc.
        };
        
        let target_location = *self.allocator.get_location_or_panic(target);
        
        match &size.kind {
            OperandKind::Const(ConstValue::Int32(size_val)) => {
                // Static size known at compile time
                let total_bytes = *size_val * element_size;
                
                // Assembly: Allocate on stack by moving stack pointer
                // SUB RSP, total_bytes  ; Reserve space on stack
                self.asm.add_instruction(Instruction::with2(
                    Code::Sub_rm64_imm32,
                    Register::RSP,
                    total_bytes,
                )?)?;
                
                // MOV target, RSP  ; Store stack pointer as array base
                match target_location {
                    Location::Register(target_reg) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            target_reg,
                            Register::RSP,
                        )?)?;
                    }
                    Location::Stack(target_entry) => {
                        // MOV [RBP + offset], RSP
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(target_entry),
                            Register::RSP,
                        )?)?;
                    }
                }
            }
            OperandKind::Const(ConstValue::Int64(size_val)) => {
                // 64-bit constant size
                let total_bytes = (*size_val as i32) * element_size;
                self.asm.add_instruction(Instruction::with2(
                    Code::Sub_rm64_imm32,
                    Register::RSP,
                    total_bytes,
                )?)?;
                
                match target_location {
                    Location::Register(target_reg) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            target_reg,
                            Register::RSP,
                        )?)?;
                    }
                    Location::Stack(target_entry) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(target_entry),
                            Register::RSP,
                        )?)?;
                    }
                }
            }
            OperandKind::Location(size_loc) => {
                // Dynamic size
                let size_location = *self.allocator.get_location_or_panic(size_loc);
                let temp_reg = Register::RAX;
                
                // Load size into temp register
                match size_location {
                    Location::Register(size_reg) => {
                        if size_reg != temp_reg {
                            self.asm.add_instruction(Instruction::with2(
                                Code::Mov_r64_rm64,
                                temp_reg,
                                size_reg,
                            )?)?;
                        }
                    }
                    Location::Stack(size_entry) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(size_entry),
                        )?)?;
                    }
                }
                
                // Multiply by element size: IMUL RAX, element_size
                if element_size != 1 {
                    self.asm.add_instruction(Instruction::with3(
                        Code::Imul_r64_rm64_imm32,
                        temp_reg,
                        temp_reg,
                        element_size,
                    )?)?;
                }
                
                // Subtract from stack pointer (allocate): SUB RSP, RAX
                self.asm.add_instruction(Instruction::with2(
                    Code::Sub_rm64_r64,
                    Register::RSP,
                    temp_reg,
                )?)?;
                
                // Store result
                match target_location {
                    Location::Register(target_reg) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            target_reg,
                            Register::RSP,
                        )?)?;
                    }
                    Location::Stack(target_entry) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(target_entry),
                            Register::RSP,
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Complex array size operands not supported"),
        }
        
        Ok(())
    }

    fn generate_array_index(
        &mut self,
        target: &LocationIdx,
        array: &Operand,
        index: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // ArrayIndex operation: target = array[index]
        // This loads a value from an array at a specific index
        // Assembly calculation: base_address + (index * element_size)
        
        let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
        
        // Assume 8-byte elements (pointers/int64)
        let element_size = 8;
        
        // Get array base address into a register
        let array_reg = Register::RBX;  // RBX used for array base
        match &array.kind {
            OperandKind::Location(array_loc) => {
                let array_location = self.allocator.get_location_or_alloc(&locations[*array_loc]);
                match array_location {
                    Location::Register(reg) => {
                        if reg != array_reg {
                            // MOV RBX, array_reg  ; Get array base
                            self.asm.add_instruction(Instruction::with2(
                                Code::Mov_r64_rm64,
                                array_reg,
                                reg,
                            )?)?;
                        }
                    }
                    Location::Stack(array_entry) => {
                        // MOV RBX, [RBP + offset]  ; Load array base from stack
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            array_reg,
                            self.memory_op_from_stack_entry(array_entry),
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Only location operands supported for array base"),
        }
        
        // Get index and calculate offset
        match &index.kind {
            OperandKind::Const(ConstValue::Int32(index_val)) => {
                // Static index - calc offset at compile time
                let offset = *index_val * element_size;
                
                // MOV target, [RBX + offset]  ; Load array[constant_index]
                match target_location {
                    Location::Register(target_reg) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            target_reg,
                            MemoryOperand::with_base_displ(array_reg, offset as i64),
                        )?)?;
                    }
                    Location::Stack(target_entry) => {
                        // Use temp register first, then store to stack
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            MemoryOperand::with_base_displ(array_reg, offset as i64),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(target_entry),
                            temp_reg,
                        )?)?;
                    }
                }
            }
            OperandKind::Location(index_loc) => {
                // Dynamic index
                let index_location = self.allocator.get_location_or_alloc(&locations[*index_loc]);
                let index_reg = Register::RCX;  // Use RCX for index
                
                // Load index into RCX
                match index_location {
                    Location::Register(reg) => {
                        if reg != index_reg {
                            self.asm.add_instruction(Instruction::with2(
                                Code::Mov_r64_rm64,
                                index_reg,
                                reg,
                            )?)?;
                        }
                    }
                    Location::Stack(index_entry) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            index_reg,
                            self.memory_op_from_stack_entry(index_entry),
                        )?)?;
                    }
                }
                
                // Scale index by element size: IMUL RCX, element_size
                if element_size != 1 {
                    self.asm.add_instruction(Instruction::with3(
                        Code::Imul_r64_rm64_imm32,
                        index_reg,
                        index_reg,
                        element_size,
                    )?)?;
                }
                
                // MOV target, [RBX + RCX]  ; Load array[dynamic_index]
                match target_location {
                    Location::Register(target_reg) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            target_reg,
                            MemoryOperand::with_base_index(array_reg, index_reg),
                        )?)?;
                    }
                    Location::Stack(target_entry) => {
                        // Use temp register first, then store to stack
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            MemoryOperand::with_base_index(array_reg, index_reg),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(target_entry),
                            temp_reg,
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Complex index operands not supported"),
        }
        
        Ok(())
    }

    fn generate_array_length(
        &mut self,
        target: &LocationIdx,
        length: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // ArrayLength operation: target = array.length
        // Assume arrays store their length at a fixed offset,
        // 8 bytes before the data
        
        let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
        
        // Get array base address
        match &length.kind {
            OperandKind::Location(array_loc) => {
                let array_location = self.allocator.get_location_or_alloc(&locations[*array_loc]);
                let array_reg = Register::RBX;  // Use RBX for array base
                
                // Load array base address
                match array_location {
                    Location::Register(reg) => {
                        if reg != array_reg {
                            self.asm.add_instruction(Instruction::with2(
                                Code::Mov_r64_rm64,
                                array_reg,
                                reg,
                            )?)?;
                        }
                    }
                    Location::Stack(array_entry) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            array_reg,
                            self.memory_op_from_stack_entry(array_entry),
                        )?)?;
                    }
                }
                
                // Load length from [array_base - 8] (assuming length stored before data)
                // MOV target, [RBX - 8]
                match target_location {
                    Location::Register(target_reg) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            target_reg,
                            MemoryOperand::with_base_displ(array_reg, -8),
                        )?)?;
                    }
                    Location::Stack(target_entry) => {
                        // Use temp register first
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            MemoryOperand::with_base_displ(array_reg, -8),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_r64,
                            self.memory_op_from_stack_entry(target_entry),
                            temp_reg,
                        )?)?;
                    }
                }
            }
            OperandKind::Const(length) => {
                let array_length = match length {
                    ConstValue::Int32(len) => *len, // TODO: maybe set all indexes to usize??
                    ConstValue::UInt64(len) => *len as i32,
                    _ => bug_report!("Array length type error")
                };
                
                match target_location {
                    Location::Register(target_reg) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_imm32,
                            target_reg,
                            array_length,
                        )?)?;
                    }
                    Location::Stack(target_entry) => {
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_rm64_imm32,
                            self.memory_op_from_stack_entry(target_entry),
                            array_length,
                        )?)?;
                    }
                }
            }
            _ => unimplemented!("Only location and constant operands supported for arrays"),
        }
        
        Ok(())
    }

    fn generate_call(
        &mut self,
        target: &Option<LocationIdx>,
        function: &lir::FunctionIdx,
        args: &[Operand],
        locations: &IndexVec<LocationIdx, lir::Location>,
        lir: &lir::LIR,
    ) -> Result<()> {
        // Save caller-saved registers that are currently live
        let caller_saved_regs = CallingConvention::get_caller_saved_registers();
        let mut saved_registers = Vec::new();
        
        for reg in &caller_saved_regs {
            if self.allocator.is_register_allocated(*reg) {
                self.asm.add_instruction(iced_x86::Instruction::with1(Code::Push_r64, *reg)?)?;
                saved_registers.push(*reg);
            }
        }

        // Calculate stack space needed for arguments
        let stack_space = CallingConvention::calculate_stack_arg_space(args);
        
        // Align stack to 16-byte boundary before call
        if stack_space > 0 {
            self.asm.add_instruction(iced_x86::Instruction::with2(
                Code::Sub_rm64_imm32, 
                Register::RSP, 
                stack_space as i32
            )?)?;
        }

        // Pass arguments according to calling convention
        let mut int_reg_index = 0;
        let mut float_reg_index = 0;
        let mut stack_offset = 0;

        for arg in args {
            match &arg.ty {
                Type::Float32 | Type::Float64 => {
                    if let Some(reg) = CallingConvention::get_float_arg_register(float_reg_index) {
                        // Pass in floating-point register
                        self.load_operand_to_register(arg, reg, locations)?;
                        float_reg_index += 1;
                    } else {
                        // Pass on stack
                        self.push_operand_to_stack(arg, stack_offset, locations)?;
                        stack_offset += 8;
                    }
                }
                _ => {
                    if let Some(reg) = CallingConvention::get_int_arg_register(int_reg_index) {
                        // Pass in integer register
                        self.load_operand_to_register(arg, reg, locations)?;
                        int_reg_index += 1;
                    } else {
                        // Pass on stack
                        self.push_operand_to_stack(arg, stack_offset, locations)?;
                        stack_offset += 8;
                    }
                }
            }
        }

        // Make the actual function call
        // Look up the target function and generate appropriate call
        let target_function = &lir.functions[*function];
        
        if let Some(function_label) = self.function_labels.get(function) {
            // Direct call to internal function
            self.asm.call(*function_label)?;
        } else {
            // This shouldn't happen by right
            anyhow::bail!("Function label not found for function: {}", target_function.name);
        }

        // Clean up stack arguments
        if stack_space > 0 {
            self.asm.add_instruction(iced_x86::Instruction::with2(
                Code::Add_rm64_imm32, 
                Register::RSP, 
                stack_space as i32
            )?)?;
        }

        // Handle return value if there's a target location
        if let Some(target_loc) = target {
            let target_location = self.allocator.get_location_or_alloc(&locations[*target_loc]);
            let return_ty = &locations[*target_loc].ty;
            
            let return_reg = match return_ty {
                Type::Float32 | Type::Float64 => Register::XMM0,
                _ => Register::RAX,
            };
            
            self.mov(&target_location, &Location::Register(return_reg))?;
        }

        // Restore caller-saved registers in reverse order
        for reg in saved_registers.iter().rev() {
            self.asm.add_instruction(iced_x86::Instruction::with1(Code::Pop_r64, *reg)?)?;
        }

        Ok(())
    }

    /// Load an operand into a specific register
    fn load_operand_to_register(
        &mut self,
        operand: &Operand,
        target_reg: Register,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        match &operand.kind {
            OperandKind::Location(loc_idx) => {
                let source_location = self.allocator.get_location_or_alloc(&locations[*loc_idx]);
                self.mov(&Location::Register(target_reg), &source_location)?;
            }
            OperandKind::Deref(loc_idx) => {
                let source_location = self.allocator.get_location_or_alloc(&locations[*loc_idx]);
                self.mov(&Location::Register(target_reg), &source_location)?;
            }
            OperandKind::Const(const_val) => {
                match const_val {
                    ConstValue::Int32(val) => {
                        self.asm.add_instruction(iced_x86::Instruction::with2(
                            Code::Mov_r64_imm64, 
                            target_reg, 
                            *val as i64
                        )?)?;
                    }
                    ConstValue::Int64(val) => {
                        self.asm.add_instruction(iced_x86::Instruction::with2(
                            Code::Mov_r64_imm64, 
                            target_reg, 
                            *val
                        )?)?;
                    }
                    ConstValue::Bool(val) => {
                        let int_val = if *val { 1 } else { 0 };
                        self.asm.add_instruction(iced_x86::Instruction::with2(
                            Code::Mov_r64_imm64, 
                            target_reg, 
                            int_val as i64
                        )?)?;
                    }
                    _ => unimplemented!("Constant type not yet implemented for function arguments"),
                }
            }
            _ => unimplemented!("Operand kind not yet implemented for function arguments"),
        }
        Ok(())
    }

    /// Push an operand to the stack at a specific offset
    fn push_operand_to_stack(
        &mut self,
        operand: &Operand,
        stack_offset: usize,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        // First load the operand into a temporary register, then move to stack
        let temp_reg = Register::R10; // Use R10 as temporary for stack arguments
        
        self.load_operand_to_register(operand, temp_reg, locations)?;
        
        // Move from temp register to stack position
        let stack_mem = self.memory_op_from_base_offset(Register::RSP, stack_offset as i32);
        self.asm.add_instruction(iced_x86::Instruction::with2(
            Code::Mov_rm64_r64, 
            stack_mem, 
            temp_reg
        )?)?;
        
        Ok(())
    }

    /// Create a memory operand from base + offset
    fn memory_op_from_base_offset(&self, base: Register, offset: i32) -> MemoryOperand {
        MemoryOperand::new(base, Register::None, 1, offset as i64, 8, false, Register::None)
    }

    /// Generate function prologue:
    /// 
    /// Saves frame pointer, sets up stack frame, and handles parameters
    fn generate_function_prologue(&mut self, function: &lir::Function, lir: &lir::LIR) -> Result<()> {
        // Save previous frame pointer
        self.asm.add_instruction(iced_x86::Instruction::with1(Code::Push_r64, Register::RBP)?)?;
        
        // Set up new frame pointer
        self.asm.add_instruction(iced_x86::Instruction::with2(
            Code::Mov_r64_rm64, 
            Register::RBP, 
            Register::RSP
        )?)?;
        
        // Calculate stack space for local variables and parameter spills
        let stack_size = self.calculate_stack_frame_size(function, lir);
        
        if stack_size > 0 {
            self.asm.add_instruction(iced_x86::Instruction::with2(
                Code::Sub_rm64_imm32,
                Register::RSP,
                stack_size as i32
            )?)?;
        }
        
        // Move function parameters from registers to their allocated locations
        self.setup_function_parameters(function, &lir.locations)?;
        
        Ok(())
    }

    /// Setup function parameters by moving them from calling convention registers
    /// to their allocated locations in the function
    fn setup_function_parameters(
        &mut self, 
        function: &lir::Function,
        locations: &IndexVec<LocationIdx, lir::Location>
    ) -> Result<()> {
        let mut int_reg_index = 0;
        let mut float_reg_index = 0;
        
        for param_idx in &function.params {
            let param_type = &locations[*param_idx].ty;
            
            match param_type {
                Type::Float32 | Type::Float64 => {
                    if let Some(src_reg) = CallingConvention::get_float_arg_register(float_reg_index) {
                        // Pre-allocate parameter to its calling convention register
                        self.allocator.locations.insert(*param_idx, Location::Register(src_reg));
                        let param_location = self.allocator.get_location_or_alloc(&locations[*param_idx]);

                        if param_location != Location::Register(src_reg) {
                            self.mov(&param_location, &Location::Register(src_reg))?;
                        }
                        float_reg_index += 1;
                    } else {
                        unimplemented!("Stack parameters not yet implemented");
                    }
                }
                _ => {
                    if let Some(src_reg) = CallingConvention::get_int_arg_register(int_reg_index) {
                        // Pre-allocate parameter to its calling convention register
                        self.allocator.locations.insert(*param_idx, Location::Register(src_reg));
                        let param_location = self.allocator.get_location_or_alloc(&locations[*param_idx]);

                        if param_location != Location::Register(src_reg) {
                            self.mov(&param_location, &Location::Register(src_reg))?;
                        }
                        int_reg_index += 1;
                    } else {
                        unimplemented!("Stack parameters not yet implemented");
                    }
                }
            }
        }
        
        Ok(())
    }
    
    /// Calculate the stack frame size needed for the function
    fn calculate_stack_frame_size(
        &mut self,
        function: &lir::Function,
        lir: &lir::LIR
    ) -> usize {
        let mut total_stack_size = 0;
        
        total_stack_size += self.calculate_stack_parameters_size(function, &lir.locations);
        
        total_stack_size += self.calculate_local_variables_size(function, lir);
        
        // Note: Actual spill slots are allocated dynamically during codegen
        total_stack_size += self.estimate_spill_space();
        
        // Align to 16-byte boundary (required by x86_64 ABI)
        (total_stack_size + 15) & !15
    }
    
    /// Calculate stack space needed for function parameters that are passed on the stack
    fn calculate_stack_parameters_size(
        &self,
        function: &lir::Function,
        locations: &IndexVec<LocationIdx, lir::Location>
    ) -> usize {
        let mut int_reg_count = 0;
        let mut float_reg_count = 0;
        let mut stack_size = 0;
        
        for param_idx in &function.params {
            let param_type = &locations[*param_idx].ty;
            
            match param_type {
                Type::Float32 | Type::Float64 => {
                    if float_reg_count < 8 {
                        float_reg_count += 1; // Param on reg
                    } else {
                        stack_size += 8; // 8-byte alloc for param on stack
                    }
                }
                _ => {
                    if int_reg_count < 6 {
                        int_reg_count += 1;
                    } else {
                        stack_size += 8;
                    }
                }
            }
        }
        
        stack_size
    }
    
    /// Calculate stack space needed for local variables
    fn calculate_local_variables_size(
        &self,
        function: &lir::Function,
        lir: &lir::LIR
    ) -> usize {
        let mut local_vars_size = 0;
        let mut seen_locations = std::collections::HashSet::new();
        
        for bb_idx in &function.basic_blocks {
            let bb = &lir.basic_blocks[*bb_idx];

            for instruction in &bb.instructions {
                if let Some(target) = self.extract_instruction_target(&instruction.kind) {
                    if !function.params.contains(&target) && seen_locations.insert(target) {
                        let var_type = &lir.locations[target].ty;
                        local_vars_size += var_type.layout().size;
                    }
                }
            }
        }
        
        local_vars_size
    }
    
    /// Extract the target LocationIdx from an instruction, if it has one
    fn extract_instruction_target(&self, instruction: &InstructionKind) -> Option<LocationIdx> {
        match instruction {
            InstructionKind::Add { target, .. } |
            InstructionKind::Sub { target, .. } |
            InstructionKind::Mul { target, .. } |
            InstructionKind::Div { target, .. } |
            InstructionKind::Mod { target, .. } |
            InstructionKind::And { target, .. } |
            InstructionKind::Or { target, .. } |
            InstructionKind::Xor { target, .. } |
            InstructionKind::Shl { target, .. } |
            InstructionKind::Shr { target, .. } |
            InstructionKind::Eq { target, .. } |
            InstructionKind::Ne { target, .. } |
            InstructionKind::Lt { target, .. } |
            InstructionKind::Gt { target, .. } |
            InstructionKind::Le { target, .. } |
            InstructionKind::Ge { target, .. } |
            InstructionKind::Neg { target, .. } |
            InstructionKind::Not { target, .. } |
            InstructionKind::Load { target, .. } |
            InstructionKind::AllocInit { target, .. } |
            InstructionKind::AddressOf { target, .. } |
            InstructionKind::ArrayAlloc { target, .. } |
            InstructionKind::ArrayIndex { target, .. } |
            InstructionKind::ArrayLength { target, .. } |
            InstructionKind::Move { target, .. } |
            InstructionKind::Phi { target, .. } => Some(*target),
            InstructionKind::Call { target, .. } => *target,
            InstructionKind::Store { .. } |
            InstructionKind::ArrayStore { .. } |
            InstructionKind::Tuple { .. } |
            InstructionKind::TupleField { .. } |
            InstructionKind::TupleStore { .. } |
            InstructionKind::Nop => None,
        }
    }
    
    /// Conservative estimate of space needed for register spills.
    fn estimate_spill_space(&self) -> usize {
        const ESTIMATED_SPILL_SLOTS: usize = 4;
        ESTIMATED_SPILL_SLOTS * 8
    }

    /// Generate function epilogue.
    /// 
    /// Restores frame pointer and returns.
    fn generate_function_epilogue(&mut self) -> Result<()> {
        // Restore stack pointer from frame pointer
        self.asm.add_instruction(iced_x86::Instruction::with2(
            Code::Mov_r64_rm64,
            Register::RSP,
            Register::RBP
        )?)?;
        
        // Restore previous frame pointer
        self.asm.add_instruction(iced_x86::Instruction::with1(Code::Pop_r64, Register::RBP)?)?;
        
        // Return to caller
        self.asm.ret()?;
        
        Ok(())
    }

    fn generate_move(
        &mut self,
        target: &LocationIdx,
        source: &Operand,
        locations: &IndexVec<LocationIdx, lir::Location>,
    ) -> Result<()> {
        let target_location = self.allocator.get_location_or_alloc(&locations[*target]);
        
        match &source.kind {
            OperandKind::Location(loc) => {
                let src_location = self.allocator.get_location_or_alloc(&locations[*loc]);
                self.mov(&target_location, &src_location)?;
            }
            OperandKind::Deref(loc) => {
                let src_location = self.allocator.get_location_or_alloc(&locations[*loc]);
                self.mov(&target_location, &src_location)?;
            }
            OperandKind::Const(const_val) => {
                match const_val {
                    ConstValue::Int32(value) => {
                        self.mov_i32(target_location, *value)?;
                    }
                    ConstValue::Bool(val) => {
                        let int_val = if *val { 1 } else { 0 };
                        self.mov_i32(target_location, int_val)?;
                    }
                    _ => unimplemented!("Only Int32 and Bool constants supported for moves"),
                }
            }
            _ => unimplemented!("Unsupported source operand for move: {:?}", source.kind),
        }
        
        Ok(())
    }

    fn generate_conditional_branch(
        &mut self,
        condition: &Operand,
        true_target: BasicBlockIdx,
        false_target: BasicBlockIdx,
    ) -> Result<()> {
        // Test the condition
        match &condition.kind {
            OperandKind::Deref(loc) => {
                let condition_location = *self.allocator.get_location_or_panic(loc);
                match condition_location {
                    Location::Register(reg) => {
                        self.asm.add_instruction(Instruction::with2(Code::Test_rm64_r64, reg, reg)?)?;
                    }
                    Location::Stack(entry) => {
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(Code::Test_rm64_r64, temp_reg, temp_reg)?)?;
                    }
                }
            }
            OperandKind::Location(loc) => {
                let condition_location = *self.allocator.get_location_or_panic(loc);
                match condition_location {
                    Location::Register(reg) => {
                        self.asm.add_instruction(Instruction::with2(Code::Test_rm64_r64, reg, reg)?)?;
                    }
                    Location::Stack(entry) => {
                        let temp_reg = Register::RAX;
                        self.asm.add_instruction(Instruction::with2(
                            Code::Mov_r64_rm64,
                            temp_reg,
                            self.memory_op_from_stack_entry(entry),
                        )?)?;
                        self.asm.add_instruction(Instruction::with2(Code::Test_rm64_r64, temp_reg, temp_reg)?)?;
                    }
                }
            }
            _ => unimplemented!("Only deref and location operands supported for branch conditions"),
        }

        // Jump to true target if not zero
        let true_label = self.labels.entry(true_target).or_insert_with(|| self.asm.create_label());
        self.asm.jnz(*true_label)?;

        // Fall through or jump to false target
        let false_label = self.labels.entry(false_target).or_insert_with(|| self.asm.create_label());
        self.asm.jmp(*false_label)?;

        Ok(())
    }

    fn generate_switch(
        &mut self,
        value: &Operand,
        targets: &[(ConstValue, BasicBlockIdx)],
        default_target: BasicBlockIdx,
    ) -> Result<()> {
        match &value.kind {
            OperandKind::Deref(loc) => {
                let value_location = *self.allocator.get_location_or_panic(loc);
                
                for (const_val, target_bb) in targets {
                    match const_val {
                        ConstValue::Int32(val) => {
                            match value_location {
                                Location::Register(reg) => {
                                    self.asm.add_instruction(Instruction::with2(
                                        Code::Cmp_rm64_imm32,
                                        reg,
                                        *val as i32,
                                    )?)?;
                                }
                                Location::Stack(entry) => {
                                    self.asm.add_instruction(Instruction::with2(
                                        Code::Cmp_rm64_imm32,
                                        self.memory_op_from_stack_entry(entry),
                                        *val as i32,
                                    )?)?;
                                }
                            }
                            
                            let target_label = self.labels.entry(*target_bb).or_insert_with(|| self.asm.create_label());
                            self.asm.je(*target_label)?;
                        }
                        ConstValue::Bool(val) => {
                            // Convert boolean to integer for comparison
                            let bool_as_int = if *val { 1i32 } else { 0i32 };
                            match value_location {
                                Location::Register(reg) => {
                                    self.asm.add_instruction(Instruction::with2(
                                        Code::Cmp_rm64_imm32,
                                        reg,
                                        bool_as_int,
                                    )?)?;
                                }
                                Location::Stack(entry) => {
                                    self.asm.add_instruction(Instruction::with2(
                                        Code::Cmp_rm64_imm32,
                                        self.memory_op_from_stack_entry(entry),
                                        bool_as_int,
                                    )?)?;
                                }
                            }
                            
                            let target_label = self.labels.entry(*target_bb).or_insert_with(|| self.asm.create_label());
                            self.asm.je(*target_label)?;
                        }
                        _ => unimplemented!("Only Int32 and Bool constants supported for switch"),
                    }
                }
                
                // Jump to default target if no match
                let default_label = self.labels.entry(default_target).or_insert_with(|| self.asm.create_label());
                self.asm.jmp(*default_label)?;
            }
            OperandKind::Location(loc) => {
                let value_location = *self.allocator.get_location_or_panic(loc);
                
                for (const_val, target_bb) in targets {
                    match const_val {
                        ConstValue::Int32(val) => {
                            match value_location {
                                Location::Register(reg) => {
                                    self.asm.add_instruction(Instruction::with2(
                                        Code::Cmp_rm64_imm32,
                                        reg,
                                        *val as i32,
                                    )?)?;
                                }
                                Location::Stack(entry) => {
                                    self.asm.add_instruction(Instruction::with2(
                                        Code::Cmp_rm64_imm32,
                                        self.memory_op_from_stack_entry(entry),
                                        *val as i32,
                                    )?)?;
                                }
                            }
                            
                            let target_label = self.labels.entry(*target_bb).or_insert_with(|| self.asm.create_label());
                            self.asm.je(*target_label)?;
                        }
                        ConstValue::Bool(val) => {
                            // Convert boolean to integer for comparison
                            let bool_as_int = if *val { 1i32 } else { 0i32 };
                            match value_location {
                                Location::Register(reg) => {
                                    self.asm.add_instruction(Instruction::with2(
                                        Code::Cmp_rm64_imm32,
                                        reg,
                                        bool_as_int,
                                    )?)?;
                                }
                                Location::Stack(entry) => {
                                    self.asm.add_instruction(Instruction::with2(
                                        Code::Cmp_rm64_imm32,
                                        self.memory_op_from_stack_entry(entry),
                                        bool_as_int,
                                    )?)?;
                                }
                            }
                            
                            let target_label = self.labels.entry(*target_bb).or_insert_with(|| self.asm.create_label());
                            self.asm.je(*target_label)?;
                        }
                        _ => unimplemented!("Only Int32 and Bool constants supported for switch"),
                    }
                }
                
                // Jump to default target if no match
                let default_label = self.labels.entry(default_target).or_insert_with(|| self.asm.create_label());
                self.asm.jmp(*default_label)?;
            }
            OperandKind::Const(value) => {
                // If value is constant, we can directly compare it
                match value {
                    ConstValue::Int32(val) => {
                        for (const_val, target_bb) in targets {
                            if let ConstValue::Int32(target_val) = const_val {
                                if target_val == val {
                                    let target_label = self.labels.entry(*target_bb).or_insert_with(|| self.asm.create_label());
                                    self.asm.jmp(*target_label)?;
                                    return Ok(());
                                }
                            }
                        }
                        
                        // Jump to default if no match found
                        let default_label = self.labels.entry(default_target).or_insert_with(|| self.asm.create_label());
                        self.asm.jmp(*default_label)?;
                    }
                    ConstValue::Bool(val) => {
                        // Convert boolean to integer for switch comparison
                        let bool_as_int = if *val { 1i32 } else { 0i32 };
                        
                        for (const_val, target_bb) in targets {
                            if let ConstValue::Int32(target_val) = const_val {
                                if *target_val == bool_as_int {
                                    let target_label = self.labels.entry(*target_bb).or_insert_with(|| self.asm.create_label());
                                    self.asm.jmp(*target_label)?;
                                    return Ok(());
                                }
                            }
                        }

                        // Jump to default if no match found
                        let default_label = self.labels.entry(default_target).or_insert_with(|| self.asm.create_label());
                        self.asm.jmp(*default_label)?;
                    }
                    _ => unimplemented!("Only Int32 constants supported for switch"),
                }
            }
            _ => unimplemented!("Only deref and location operands supported for switch"),
        }
        
        Ok(())
    }
}

#[derive(Debug, Default)]
struct Allocator {
    frame: StackFrame,
    locations: HashMap<LocationIdx, Location>,
    used_registers: HashSet<Register>,
}

type Spilled = (LocationIdx, Register, usize);

impl Allocator {
    pub fn get_location_or_alloc(&mut self, location: &lir::Location) -> Location {
        self.locations.get(&location.idx).cloned().unwrap_or_else(|| self.allocate_location(location))
    }

    pub fn allocate_location(&mut self, location: &lir::Location) -> Location {
        let alloc_location = self.alloc(location.ty.clone());
        self.locations.insert(location.idx, alloc_location.clone());
        alloc_location
    }

    pub fn ensure_in_reg(&mut self, location: LocationIdx) -> Result<(Register, Option<Spilled>)> {
        Ok(match self.get_location(&location).copied() {
            Some(location) => match location {
                Location::Register(reg) => (reg, None),
                Location::Stack(entry_idx) => self.move_stack_to_free_reg(entry_idx),
            },
            None => {
                anyhow::bail!("Location {:?} has not yet been allocated", location);
            },
        })
    }

    pub fn alloc(&mut self, ty: Type) -> Location {
        let register = self.find_register_for_type(&ty);

        match register {
            Some(reg) => {
                self.use_register(reg);
                Location::Register(reg)
            }
            None => {
                let offset = self.alloc_stack(ty);
                Location::Stack(offset)
            }
        }
    }

    fn find_register_for_type(&mut self, _ty: &Type) -> Option<Register> {
        let available_registers = vec![
            Register::RAX, Register::RCX, Register::RDX, Register::RBX,
            Register::RSI, Register::RDI, Register::R8, Register::R9,
            Register::R10, Register::R11, Register::R12, Register::R13,
            Register::R14, Register::R15
        ];

        for reg in available_registers {
            if !self.used_registers.contains(&reg) {
                self.used_registers.insert(reg);
                return Some(reg);
            }
        }

        None
    }

    fn use_register(&mut self, reg: Register) {
        self.used_registers.insert(reg);
    }

    pub fn is_register_allocated(&self, reg: Register) -> bool {
        self.used_registers.contains(&reg)
    }

    fn alloc_stack(&mut self, ty: Type) -> usize {
        self.frame.alloc_stackframe(ty)
    }

    pub fn get_location(&self, place: &LocationIdx) -> Option<&Location> {
        self.locations.get(place)
    }

    pub fn get_location_or_panic(&self, place: &LocationIdx) -> &Location {
        match self.locations.get(place) {
            Some(location) => location,
            None => bug_report!("{:?} has not yet been allocated", place),
        }
    }

    pub fn move_stack_to_free_reg(&mut self, entry_idx: usize) -> (Register, Option<Spilled>) {
        let entry = self.frame.get_entry(entry_idx);
        let entry_type = entry.ty.clone();
        let (reg, spilled) = self.get_free_register(entry_type);

        self.free_stack(entry_idx);
        self.use_register(reg);

        let location = self.locations.iter().find(|(_, loc)| match loc {
            Location::Stack(idx) => *idx == entry_idx,
            Location::Register(_) => false,
        }).map(|(loc_idx, _)| *loc_idx);

        if let Some(location) = location {
            self.locations.insert(location, Location::Register(reg));
        }
        if let Some((spilled_location, _, spilled_stack_idx)) = spilled {
            self.locations.insert(spilled_location, Location::Stack(spilled_stack_idx));
        }

        (reg, spilled)
    }

    fn get_free_register(&mut self, ty: Type) -> (Register, Option<Spilled>) {
        let mut spilled = None;
        let reg = self.find_register_for_type(&ty).unwrap_or_else(
            || {
                let spilled_reg = self.find_register_to_spill(ty);
                spilled = Some(spilled_reg);
                spilled_reg.1
            }
        );

        (reg, spilled)
    }

    fn find_register_to_spill(&mut self, ty: Type) -> Spilled {
        let (reg_to_spill, location_to_spill) = self.locations.iter().find_map(
            |(loc_idx, loc)| match loc {
                Location::Register(reg) => {
                    if reg.size() == ty.layout().size {
                        return Some((*reg, *loc_idx));
                    }

                    None
                }
                Location::Stack(_) => None,
            }
        ).unwrap();
        let stack_idx = self.alloc_stack(ty);

        (location_to_spill, reg_to_spill, stack_idx)
    }

    fn free_stack(&mut self, idx: usize) {
        self.frame.dealloc_stackframe(idx)
    }

    fn free_register(&mut self, reg: Register) {
        self.used_registers.remove(&reg);
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Location {
    Register(Register),
    Stack(usize),
}

#[derive(Debug, Default)]
struct StackFrame {
    entries: Vec<StackFrameEntry>,
    offset: usize,
}

impl StackFrame {
    pub fn alloc_stackframe(&mut self, ty: Type) -> usize {
        let new_idx = self.entries.len();
        let size = ty.layout().size;

        self.entries.push(StackFrameEntry {
            ty,
            offset: self.offset,
            live: true,
        });
        self.offset += size;

        new_idx
    }

    pub fn dealloc_stackframe(&mut self, entry_idx: usize) {
        self.recursive_free(entry_idx)
    }

    fn recursive_free(&mut self, mut idx: usize) {
        while self.free(idx) {
            idx -= 1;
        }
    }

    fn free(&mut self, idx: usize) -> bool {
        if idx != self.entries.len() - 1 {
            return false; // Cannot free non-top entry
        }

        let entry = &mut self.entries[idx];
        if !entry.live {
            return false; // Cannot free dead entry
        }

        entry.live = false;
        self.offset -= entry.ty.layout().size;
        self.entries.pop();
        true
    }

    pub fn get_entry(&self, idx: usize) -> &StackFrameEntry {
        self.entries.get(idx).unwrap()
    }
}

#[derive(Debug)]
struct StackFrameEntry {
    ty: Type,
    offset: usize,
    live: bool,
}