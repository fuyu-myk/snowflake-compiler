use snowflake_compiler::{idx, IndexVec};

use crate::ir::mir;

pub(crate) mod builder;


#[derive(Debug)]
pub struct LIR {
    pub functions: IndexVec<FunctionIdx, Function>,
    pub basic_blocks: IndexVec<BasicBlockIdx, BasicBlock>,
    pub locations: Locations,
}

impl LIR {
    pub fn new() -> Self {
        Self {
            functions: IndexVec::new(),
            basic_blocks: IndexVec::new(),
            locations: IndexVec::new(),
        }
    }
}

pub type Locations = IndexVec<LocationIdx, Location>;

idx!(FunctionIdx);
idx!(BasicBlockIdx);
idx!(LocationIdx);

#[derive(Debug)]
pub struct Function {
    pub name: String,
    pub return_type: Type,
    pub params: Vec<LocationIdx>,
    pub basic_blocks: Vec<BasicBlockIdx>,
}

#[derive(Debug, Default)]
pub struct BasicBlock {
    pub instructions: Vec<Instruction>,
    pub terminator: Option<Terminator>,
}

#[derive(Debug)]
pub struct Instruction {
    pub kind: InstructionKind,
}

#[derive(Debug)]
pub enum InstructionKind {
    Add {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Sub {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Gt {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    AllocInit {
        target: LocationIdx,
        value: Operand,
    },
    AddressOf {
        target: LocationIdx,
        source: LocationIdx
    },
}

#[derive(Debug)]
pub enum Terminator {
    Return {
        value: Option<Operand>,
    },
    Goto {
        target: BasicBlockIdx,
    },
}

#[derive(Debug)]
pub struct Operand {
    pub ty: Type,
    pub kind: OperandKind,
}

#[derive(Debug)]
pub enum OperandKind {
    Deref(LocationIdx),
    Const(ConstValue),
}

#[derive(Debug)]
pub enum ConstValue {
    Int8(i8),
    Int32(i32),
    String(String),
}

#[derive(Debug)]
pub struct Location {
    pub idx: LocationIdx,
    pub ty: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Int32,
    Bool,
    String,
    Int8,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Layout {
    pub size: usize,
    pub alignment: usize,
}

impl Type {
    pub fn layout(&self) -> Layout {
        match self {
            Type::Int32 => Layout { size: 4, alignment: 4 },
            Type::String => Layout { size: 8, alignment: 8 },
            Type::Int8 => Layout { size: 1, alignment: 1 },
            Type::Bool => Layout { size: 1, alignment: 1 },
        }
    }
}

impl From<mir::Type> for Type {
    fn from(value: mir::Type) -> Self {
        match value {
            mir::Type::Int => Type::Int32,
            mir::Type::Usize => Type::Int8,
            mir::Type::String => Type::String,
            mir::Type::Bool => Type::Int8,
            mir::Type::Array(_) => todo!(),
            mir::Type::Void => todo!(),
        }
    }
}