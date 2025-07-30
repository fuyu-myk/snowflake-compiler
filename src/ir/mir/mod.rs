/*
 * This module handles the mid-level intermediate representation (MIR) of the compiler
 */

use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
    ops::{Deref, DerefMut},
};

use snowflake_compiler::{bug_report, idx, IndexVec, Idx};

use crate::{ast, compilation_unit::{self, FunctionIndex, VariableIndex}};

use basic_block::{BasicBlock, BasicBlockIdx};

#[allow(unused)]
pub use builder::MIRBuilder;

#[allow(unused)]
pub use writer::MIRWriter;

mod basic_block;
mod builder;
mod writer;
pub mod optimisations;


pub type Functions = IndexVec<FunctionIndex, Function>;

idx!(InstructionIdx);

pub struct MIR {
    pub functions: Functions,
    pub basic_blocks: BasicBlocks,
}

impl MIR {
    pub fn new() -> Self {
        Self {
            functions: Functions::new(),
            basic_blocks: BasicBlocks::new(),
        }
    }
    
    pub fn new_basic_block(&mut self) -> BasicBlockIdx {
        self.basic_blocks.0.push_with_index(|idx| Some(BasicBlock::new(idx)))
    }
}

#[derive(Debug)]
pub struct BasicBlocks(IndexVec<BasicBlockIdx, Option<BasicBlock>>);

impl BasicBlocks {
    pub fn new() -> Self {
        Self(IndexVec::new())
    }

    pub fn push_basic_block(&mut self) -> BasicBlockIdx {
        self.0.push_with_index(|idx| Some(BasicBlock::new(idx)))
    }
}

impl Deref for BasicBlocks {
    type Target = IndexVec<BasicBlockIdx, Option<BasicBlock>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for BasicBlocks {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Type {
    Int,
    Bool,
    Void,
}

impl From<compilation_unit::Type> for Type {
    fn from(value: crate::typings::Type) -> Self {
        match value {
            compilation_unit::Type::Int => Self::Int,
            compilation_unit::Type::Bool => Self::Bool,
            compilation_unit::Type::Void => Self::Void,
            compilation_unit::Type::Unresolved | compilation_unit::Type::Error => {
                bug_report!("Unresolved type")
            }
        }
    }
}

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub params: Vec<VariableIndex>,
    pub basic_blocks: Vec<BasicBlockIdx>,
    pub instructions: Instructions,
    pub locals: Locals,
    pub return_type: Type,
}

impl Function {
    /// Adds an instruction to the function and returns its index
    pub fn add_instruction(&mut self, instruction: Instruction) -> InstructionIdx {
        self.instructions.push(instruction)
    }

    /// Adds an instruction with automatic trivial phi elimination during construction
    /// Returns either the new instruction index or an existing instruction that should be used instead
    pub fn add_instruction_with_phi_elimination(&mut self, instruction: Instruction) -> InstructionIdx {
        match &instruction.kind {
            InstructionKind::Phi(phi_node) => {
                // Check if this phi node would be trivial
                if let Some(replacement_idx) = PhiNode::check_trivial(&phi_node.operands) {
                    // Don't create the phi node, return the replacement instruction
                    replacement_idx
                } else {
                    // Not trivial, add the phi node normally
                    self.instructions.push(instruction)
                }
            }
            _ => {
                // Not a phi node, add normally
                self.instructions.push(instruction)
            }
        }
    }
}

pub type Instructions = IndexVec<InstructionIdx, Instruction>;
pub type Locals = HashMap<InstructionIdx, VariableIndex>;

#[derive(Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
    pub ty: Type,
}

impl Instruction {
    pub fn new(kind: InstructionKind, ty: Type) -> Self {
        Self { kind, ty }
    }

    pub fn is_pure(&self) -> bool {
        match &self.kind {
            InstructionKind::Value(_) => true,
            InstructionKind::Binary { .. } => true,
            InstructionKind::Unary { .. } => true,
            InstructionKind::Call { .. } => false,
            InstructionKind::Phi(_) => false,
        }
    }
}

#[derive(Debug)]
pub enum InstructionKind {
    Value(Value),
    Binary {
        operator: BinOp,
        left: Value,
        right: Value,
    },
    Unary {
        operator: UnOp,
        operand: Value,
    },
    Call {
        fx_idx: FunctionIndex,
        args: Vec<Value>,
    },
    Phi(PhiNode),
}

impl InstructionKind {
    pub fn as_phi(&self) -> Option<&PhiNode> {
        match self {
            Self::Phi(phi) => Some(phi),
            _ => None,
        }
    }

    pub fn as_phi_mut(&mut self) -> Option<&mut PhiNode> {
        match self {
            Self::Phi(phi) => Some(phi),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Value {
    InstructionRef(InstructionIdx),
    ParamRef(usize),
    ConstantInt(i32),
    Void,
}

impl Value {
    /// Checks if `Value` is a constant.
    pub fn is_const(&self) -> bool {
        matches!(self, Self::ConstantInt(_) | Self::Void)
    }

    /// Returns `InstructionIdx` if `Value` is an instruction reference, `InstructionRef`.
    pub fn as_instruct_ref(&self) -> Option<InstructionIdx> {
        match self {
            Self::InstructionRef(idx) => Some(*idx),
            _ => None,
        }
    }

    /// Returns 'i32' if `Value` is a constant integer, `ConstantInt`.
    /// Returns `None` if it is not a constant integer.
    pub fn as_i32(&self) -> Option<i32> {
        match self {
            Self::ConstantInt(value) => Some(*value),
            _ => None,
        }
    }

    /// Replaces the current value if it is not equal to the new value.
    /// 
    /// Returns `true` if the value was replaced.
    pub fn replace_if_unequal(&mut self, value: Value) -> bool {
        if value != *self {
            *self = value;
            true
        } else {
            false
        }
    }

    /// Used in copy propagation.
    /// 
    /// Replaces irrelevant variable assignments with previously calculated values.
    /// Returns `true` if an instruction is replaced.
    pub fn replace_with_copied_ref(&mut self, copies: &HashMap<InstructionIdx, InstructionIdx>) -> bool {
        match self {
            Self::InstructionRef(idx) => {
                if let Some(new_ref) = copies.get(idx) {
                    *self = Self::InstructionRef(*new_ref);
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    BitShl,
    BitShr,
    Eq,
    Neq,
    Lt,
    Gt,
    Leq,
    Geq,
}

impl From<ast::BinaryOpKind> for BinOp {
    fn from(value: ast::BinaryOpKind) -> Self {
        match value {
            ast::BinaryOpKind::Plus => Self::Add,
            ast::BinaryOpKind::Minus => Self::Sub,
            ast::BinaryOpKind::Multiply => Self::Mul,
            ast::BinaryOpKind::Divide => Self::Div,
            ast::BinaryOpKind::Power => unimplemented!(),
            ast::BinaryOpKind::Modulo => Self::Mod,
            ast::BinaryOpKind::BitwiseAnd => Self::BitAnd,
            ast::BinaryOpKind::BitwiseOr => Self::BitOr,
            ast::BinaryOpKind::BitwiseXor => Self::BitXor,
            ast::BinaryOpKind::ShiftLeft => Self::BitShl,
            ast::BinaryOpKind::ShiftRight => Self::BitShr,
            ast::BinaryOpKind::Equals => Self::Eq,
            ast::BinaryOpKind::NotEquals => Self::Neq,
            ast::BinaryOpKind::LessThan => Self::Lt,
            ast::BinaryOpKind::GreaterThan => Self::Gt,
            ast::BinaryOpKind::LessThanOrEqual => Self::Leq,
            ast::BinaryOpKind::GreaterThanOrEqual => Self::Geq,
        }
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add => write!(f, "add"),
            Self::Sub => write!(f, "sub"),
            Self::Mul => write!(f, "mul"),
            Self::Div => write!(f, "div"),
            Self::Mod => write!(f, "mod"),
            Self::BitAnd => write!(f, "and"),
            Self::BitOr => write!(f, "or"),
            Self::BitXor => write!(f, "xor"),
            Self::BitShl => write!(f, "shl"),
            Self::BitShr => write!(f, "shr"),
            Self::Eq => write!(f, "eq"),
            Self::Neq => write!(f, "neq"),
            Self::Lt => write!(f, "lt"),
            Self::Gt => write!(f, "gt"),
            Self::Leq => write!(f, "leq"),
            Self::Geq => write!(f, "geq"),
        }
    }
}

#[derive(Debug)]
pub enum UnOp {
    Neg,
    Not,
}

impl From<ast::UnaryOpKind> for UnOp {
    fn from(value: ast::UnaryOpKind) -> Self {
        match value {
            ast::UnaryOpKind::Negation => Self::Neg,
            ast::UnaryOpKind::BitwiseNot => Self::Not,
        }
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Neg => write!(f, "neg"),
            Self::Not => write!(f, "not"),
        }
    }
}

type Operands = Vec<(BasicBlockIdx, InstructionIdx)>;

#[derive(Debug, Clone)]
pub struct PhiNode {
    pub operands: Operands,
}

impl PhiNode {
    pub fn operandless() -> Self {
        Self { operands: Operands::new() }
    }

    /// Creates a new phi node with the given operands
    pub fn new(operands: Operands) -> Self {
        Self { operands }
    }

    /// Creates a new phi node with the given operands, automatically eliminating trivial cases
    /// Returns either a new phi node or the instruction index that should be used instead
    pub fn new_with_elimination(operands: Operands) -> Result<Self, InstructionIdx> {
        // Check if the phi node would be trivial
        if let Some(trivial_result) = Self::check_trivial(&operands) {
            // Return the instruction that should be used instead of creating a phi
            Err(trivial_result)
        } else {
            // Not trivial, create the phi node
            Ok(Self { operands })
        }
    }

    /// Adds an operand to the phi node
    pub fn add_operand(&mut self, bb: BasicBlockIdx, inst: InstructionIdx) {
        self.operands.push((bb, inst));
    }

    /// Adds an operand to the phi node and checks if it becomes trivial
    /// Returns Some(instruction_idx) if the phi becomes trivial and should be replaced
    pub fn add_operand_with_elimination(&mut self, bb: BasicBlockIdx, inst: InstructionIdx) -> Option<InstructionIdx> {
        self.operands.push((bb, inst));
        Self::check_trivial(&self.operands)
    }

    /// Checks if the given operands would form a trivial phi node
    fn check_trivial(operands: &Operands) -> Option<InstructionIdx> {
        if operands.is_empty() {
            return None;
        }

        let mut unique_operand: Option<InstructionIdx> = None;

        for &(_, operand_idx) in operands {
            match unique_operand {
                None => unique_operand = Some(operand_idx),
                Some(existing) if existing != operand_idx => return None, // Not trivial
                _ => {} // Same as existing, continue
            }
        }

        unique_operand
    }

    /// Checks if this phi node is trivial (all operands are the same, ignoring self-references)
    pub fn is_trivial(&self, self_idx: InstructionIdx) -> Option<InstructionIdx> {
        if self.operands.is_empty() {
            return None;
        }

        let mut unique_operand: Option<InstructionIdx> = None;

        for &(_, operand_idx) in &self.operands {
            // Skip self-references
            if operand_idx == self_idx {
                continue;
            }

            match unique_operand {
                None => unique_operand = Some(operand_idx),
                Some(existing) if existing != operand_idx => return None,
                _ => {} // Same as existing, continue
            }
        }

        unique_operand
    }

    /// Removes operands coming from a specific basic block
    pub fn remove_operands_from_block(&mut self, bb: BasicBlockIdx) {
        self.operands.retain(|(block, _)| *block != bb);
    }
}

impl Deref for PhiNode {
    type Target = Operands;

    fn deref(&self) -> &Self::Target {
        &self.operands
    }
}

impl DerefMut for PhiNode {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.operands
    }
}

#[derive(Debug, Clone)]
pub struct Terminator {
    pub kind: TerminatorKind,
}

impl Terminator {
    pub fn new(kind: TerminatorKind) -> Self {
        Self { kind }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TerminatorKind {
    Return {
        value: Value,
    },
    /// Execution continues in successor bb
    Goto(BasicBlockIdx),
    /// Switches based on computed Value
    SwitchInt {
        value: Value,
        targets: Vec<(i32, BasicBlockIdx)>,
        default: BasicBlockIdx,
    },
    /// Used for unknown targets
    Unresolved,
}
