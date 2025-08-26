use std::fmt::Write;

use anyhow::Result;
use snowflake_common::{Idx, IndexVec};

use crate::{
    ir::mir::{basic_block::{BasicBlock, BasicBlockIdx}, Constant, Function, FunctionIdx, Instruction, InstructionIdx, InstructionKind, Terminator, TerminatorKind, Type, Value, MIR}
};


pub struct MIRWriter<W> {
    _phantom: std::marker::PhantomData<W>,
}

impl<W> MIRWriter<W> where W: Write {
    pub fn write_graphviz(writer: &mut W, mir: &MIR) -> Result<()> {
        writeln!(writer, "digraph {{")?;

        for fx in mir.functions.iter() {
            writeln!(writer, "    subgraph cluster_{} {{", fx.name)?;
            writeln!(writer, "        label = \"{}\";", fx.name)?;

            for bb_idx in fx.basic_blocks.iter().copied() {
                let bb = mir.basic_blocks.get_or_panic(bb_idx);
                let mut bb_body = String::new();

                MIRWriter::write_basic_block(&mut bb_body, &mir, fx, bb_idx, &bb)?;
                writeln!(writer, "        {} [label=\"{}\"];", Self::format_bb_idx(bb_idx), bb_body)?;

                match &bb.terminator.as_ref().unwrap().kind {
                    TerminatorKind::Return { .. } => {}
                    TerminatorKind::Goto(target) => {
                        writeln!(writer, "        {} -> {};", Self::format_bb_idx(bb_idx), Self::format_bb_idx(*target))?;
                    }
                    TerminatorKind::SwitchInt { value: _, targets, default } => {
                        writeln!(writer, "        {} -> {};", Self::format_bb_idx(bb_idx), Self::format_bb_idx(*default))?;

                        for (_case_idx, case_target) in targets.iter() {
                            writeln!(writer, "        {} -> {};", Self::format_bb_idx(bb_idx), Self::format_bb_idx(*case_target))?;
                        }
                    }
                    TerminatorKind::Assert { condition: _, check: _, message: _, default } => {
                        writeln!(writer, "        {} -> {};", Self::format_bb_idx(bb_idx), Self::format_bb_idx(*default))?;
                    }
                    TerminatorKind::Unresolved => {}
                }
            }

            writeln!(writer, "    }}")?;
        }

        writeln!(writer, "}}")?;
        Ok(())
    }

    pub fn write_txt(writer: &mut W, mir: &MIR) -> Result<()> {
        for function in mir.functions.iter() {
            writeln!(writer, "fx {}:", function.name)?;

            for bb_idx in function.basic_blocks.iter().copied() {
                let bb = mir.basic_blocks.get_or_panic(bb_idx);
                Self::write_basic_block(writer, &mir, function, bb_idx, &bb)?;
            }
        }
        
        Ok(())
    }

    fn write_basic_block(writer: &mut W, mir: &MIR, fx: &Function, bb_idx: BasicBlockIdx, bb: &&BasicBlock) -> Result<()> {
        let indent = "    ";

        writeln!(writer, "{}:", Self::format_bb_idx(bb_idx))?;
        
        for instruct_idx in &bb.instructions {
            let instruction = fx.instructions.get(*instruct_idx);
            write!(writer, "{}", indent)?;

            if !matches!(instruction.ty, Type::Void) {
                write!(writer, "{} = ", Self::format_instruct_idx(*instruct_idx))?;
            }

            Self::write_instruction(writer, &mir.functions, instruction)?;
            writeln!(writer)?;
        }

        write!(writer, "{}", indent)?;
        Self::write_terminator(writer, &mir.functions, bb.terminator.as_ref().unwrap())?;
        writeln!(writer)?;
        Ok(())
    }

    fn write_terminator(writer: &mut W, _functions: &IndexVec<FunctionIdx, Function>, terminator: &Terminator) -> Result<()> {
        match &terminator.kind {
            TerminatorKind::Return { value } => {
                write!(writer, "return ")?;
                Self::write_value(writer, value)?;
            }
            TerminatorKind::Goto(target) => {
                write!(writer, "goto {}", target)?;
            }
            TerminatorKind::SwitchInt { value, targets, default } => {
                write!(writer, "switchInt (")?;
                Self::write_value(writer, value)?;
                writeln!(writer, ") {{")?;

                for (case_idx, case_target) in targets.iter() {
                    write!(writer, "    case {}: {}", case_idx, case_target)?;
                    writeln!(writer)?;
                }

                write!(writer, "    default: {}", default)?;
                writeln!(writer)?;
                write!(writer, "    }}")?;
            }
            TerminatorKind::Assert { condition, check: _, message, default } => {
                write!(writer, "assert(")?;
                Self::write_value(writer, condition)?;
                write!(writer, ", \"{}\"", message.debug_message())?;
                write!(writer, ") -> [success: {}]", Self::format_bb_idx(*default))?;
            }
            TerminatorKind::Unresolved => { write!(writer, "unresolved")?; }
        }

        Ok(())
    }

    fn write_instruction(writer: &mut W, functions: &IndexVec<FunctionIdx, Function>, instruction: &Instruction) -> Result<()> {
        match &instruction.kind {
            InstructionKind::Value(value) => { Self::write_value(writer, value)?; }
            InstructionKind::Binary { operator, left, right } => {
                write!(writer, "{} ", operator)?;
                Self::write_value(writer, left)?;
                writer.write_str(", ")?;
                Self::write_value(writer, right)?;
            }
            InstructionKind::Unary { operator, operand } => {
                write!(writer, "{} ", operator)?;
                Self::write_value(writer, operand)?;
            }
            InstructionKind::Call { fx_idx, args } => {
                let fx = functions.get(*fx_idx);
                write!(writer, "{}(", fx.name)?;

                for (arg_idx, arg) in args.iter().enumerate() {
                    Self::write_value(writer, arg)?;

                    if arg_idx != args.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }

                write!(writer, ")")?;
            }
            InstructionKind::ArrayAlloc { size, element_type: _ } => {
                write!(writer, "array_alloc(")?;
                Self::write_value(writer, size)?;  
                write!(writer, ")")?;
            }
            InstructionKind::ArrayInit { elements } => {
                write!(writer, "[")?;
                for (i, elem) in elements.iter().enumerate() {
                    Self::write_value(writer, elem)?;
                    if i != elements.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }
                write!(writer, "]")?;
            }
            InstructionKind::IndexVal { array_len } => {
                Self::write_value(writer, array_len)?;
            }
            InstructionKind::ArrayIndex { array, index } => {
                Self::write_value(writer, array)?;
                write!(writer, "[")?;
                Self::write_value(writer, index)?;
                write!(writer, "]")?;
            }
            InstructionKind::ArrayStore { array, index, value } => {
                Self::write_value(writer, array)?;
                write!(writer, "[")?;
                Self::write_value(writer, index)?;
                write!(writer, "] = ")?;
                Self::write_value(writer, value)?;
            }
            InstructionKind::Tuple { elements } => {
                write!(writer, "(")?;
                for (i, elem) in elements.iter().enumerate() {
                    Self::write_value(writer, elem)?;
                    if i == 0 || i != elements.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }
                write!(writer, ")")?;
            }
            InstructionKind::TupleField { tuple, field } => {
                Self::write_value(writer, tuple)?;
                write!(writer, ".")?;
                Self::write_value(writer, field)?;
            }
            InstructionKind::TupleStore { tuple, field, value } => {
                Self::write_value(writer, tuple)?;
                write!(writer, ".")?;
                Self::write_value(writer, field)?;
                write!(writer, " = ")?;
                Self::write_value(writer, value)?;
            }
            InstructionKind::Phi(phi) => {
                write!(writer, "phi {{")?;

                for (idx, (pred, instruct_ref)) in phi.iter().enumerate() {
                    write!(writer, "{} -> {}", pred, Self::format_instruct_idx(*instruct_ref))?;

                    if idx != phi.len() - 1 {
                        write!(writer, ", ")?;
                    }
                }

                write!(writer, "}}")?;
            }
        }

        Ok(())
    }

    fn write_value(writer: &mut W, value: &Value) -> Result<()> {
        match value {
            Value::InstructionRef(instruct_idx) => {
                write!(writer, "{}", Self::format_instruct_idx(*instruct_idx))?;
            }
            Value::ParamRef(param_idx) => {
                write!(writer, "{}", Self::format_param_idx(*param_idx))?;
            }
            Value::Constant(Constant::Int(value)) => {
                write!(writer, "{}", value)?;
            }
            Value::Constant(Constant::Float(value)) => {
                write!(writer, "{}", value)?;
            }
            Value::Constant(Constant::Bool(value)) => {
                write!(writer, "{}", value)?;
            }
            Value::Constant(Constant::String(value)) => {
                write!(writer, "\"{}\"", value)?;
            }
            Value::Constant(Constant::Usize(value)) => {
                write!(writer, "{}", value)?;
            }
            Value::Constant(Constant::Void) => {
                write!(writer, "()")?;
            }
        }

        Ok(())
    }

    /// Formats the index for basic blocks as `bb(index)`
    /// 
    /// Eg: index 0 -> `bb0`
    fn format_bb_idx(bb_idx: BasicBlockIdx) -> String {
        format!("bb{}", bb_idx.as_index())
    }

    /// Formats the index for instructions as `%(index)`
    /// 
    /// Eg: index 0 -> `%0`
    fn format_instruct_idx(idx: InstructionIdx) -> String {
        format!("%{}", idx.as_index())
    }

    /// Formats the index for parameters as `$(index)`
    /// 
    /// Eg: index 0 -> `$0`
    fn format_param_idx(idx: usize) -> String {
        format!("${}", idx)
    }
}