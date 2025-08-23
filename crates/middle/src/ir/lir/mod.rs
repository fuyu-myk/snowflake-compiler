use snowflake_common::{idx, IndexVec};

use crate::ir::mir;

pub mod builder;


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
    // Arithmetic operations
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
    Mul {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Div {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Mod {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    
    // Bitwise operations
    And {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Or {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Xor {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Shl {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Shr {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    
    // Comparison operations
    Eq {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Ne {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Lt {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Gt {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Le {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    Ge {
        target: LocationIdx,
        left: Operand,
        right: Operand,
    },
    
    // Unary operations
    Neg {
        target: LocationIdx,
        operand: Operand,
    },
    Not {
        target: LocationIdx,
        operand: Operand,
    },
    
    // Memory operations
    Load {
        target: LocationIdx,
        source: Operand,
    },
    Store {
        target: Operand,
        value: Operand,
    },
    AllocInit {
        target: LocationIdx,
        value: Operand,
    },
    AddressOf {
        target: LocationIdx,
        source: LocationIdx,
    },
    
    // Array operations
    ArrayAlloc {
        target: LocationIdx,
        element_type: Type,
        size: Operand,
    },
    ArrayIndex {
        target: LocationIdx,
        array: Operand,
        index: Operand,
    },
    ArrayLength {
        target: LocationIdx,
        length: Operand,
    },
    ArrayStore {
        array: Operand,
        index: Operand,
        value: Operand,
    },
    Call {
        target: Option<LocationIdx>,
        function: FunctionIdx,
        args: Vec<Operand>,
    },
    Move {
        target: LocationIdx,
        source: Operand,
    },
    
    // Special operations for code generation
    Phi {
        target: LocationIdx,
        operands: Vec<(BasicBlockIdx, Operand)>,
    },
    
    /// No operation
    Nop,
}

#[derive(Debug)]
pub enum Terminator {
    Return {
        value: Option<Operand>,
    },
    Goto {
        target: BasicBlockIdx,
    },
    /// Conditional branch - for Assert
    Branch {
        condition: Operand,
        true_target: BasicBlockIdx,
        false_target: BasicBlockIdx,
    },
    /// Multi-way branch (switch statement)
    Switch {
        value: Operand,
        targets: Vec<(ConstValue, BasicBlockIdx)>,
        default_target: BasicBlockIdx,
    },
    /// Unreachable code
    Unreachable{
        error: String,
    },
    /// Runtime panic with message
    Panic {
        message: String,
    },
}

#[derive(Debug)]
pub struct Operand {
    pub ty: Type,
    pub kind: OperandKind,
}

#[derive(Debug)]
pub enum OperandKind {
    /// Direct reference to a location (register or stack slot)
    Location(LocationIdx),
    /// Dereference a location (memory access)
    Deref(LocationIdx),
    /// Constant value
    Const(ConstValue),
    /// Memory operand with base + offset
    Memory {
        base: LocationIdx,
        offset: i32,
    },
    /// Memory operand with base + index * scale + offset
    IndexedMemory {
        base: Option<LocationIdx>,
        index: Option<LocationIdx>,
        scale: u8, // 1, 2, 4, or 8
        offset: i32,
    },
    /// Function reference for calls
    Function(FunctionIdx),
}

#[derive(Debug)]
pub enum ConstValue {
    Int8(i8),
    Int16(i16),
    Int32(i32),
    Int64(i64),
    UInt8(u8),
    UInt16(u16),
    UInt32(u32),
    UInt64(u64),
    Float32(f32),
    Float64(f64),
    Bool(bool),
    String(String),
    /// Null pointer
    Null,
}

#[derive(Debug, Clone)]
pub struct Location {
    pub idx: LocationIdx,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    // Integer types
    Int8,
    Int16,
    Int32,
    Int64,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    
    // Floating point types
    Float32,
    Float64,
    
    // Other types
    Bool,
    String,
    
    // Pointer types
    Pointer(Box<Type>),
    
    // Array types
    Array {
        element_type: Box<Type>,
        size: usize,
    },
    
    // Void type
    Void,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Layout {
    pub size: usize,
    pub alignment: usize,
}

impl Type {
    /// Returns the layout of this type, in the form of a `Layout` struct
    pub fn layout(&self) -> Layout {
        match self {
            Type::Int8 | Type::UInt8 | Type::Bool => Layout { size: 1, alignment: 1 },
            Type::Int16 | Type::UInt16 => Layout { size: 2, alignment: 2 },
            
            // Use 8-byte allocation for Int32 to match 64-bit operations
            Type::Int32 | Type::UInt32 | Type::Float32 => Layout { size: 8, alignment: 8 },
            Type::Int64 | Type::UInt64 | Type::Float64 => Layout { size: 8, alignment: 8 },
            Type::String | Type::Pointer(_) => Layout { size: 8, alignment: 8 }, // 64-bit pointers
            Type::Array { element_type, size } => {
                let element_layout = element_type.layout();
                Layout {
                    size: element_layout.size * size,
                    alignment: element_layout.alignment,
                }
            }
            Type::Void => Layout { size: 0, alignment: 1 },
        }
    }
    
    /// Returns true if this is an integer type
    pub fn is_integer(&self) -> bool {
        matches!(self, 
            Type::Int8 | Type::Int16 | Type::Int32 | Type::Int64 |
            Type::UInt8 | Type::UInt16 | Type::UInt32 | Type::UInt64
        )
    }
    
    /// Returns true if this is a floating point type
    pub fn is_float(&self) -> bool {
        matches!(self, Type::Float32 | Type::Float64)
    }
    
    /// Returns true if this is a pointer type
    pub fn is_pointer(&self) -> bool {
        matches!(self, Type::Pointer(_) | Type::String)
    }
    
    /// Returns the size of this type in bytes
    pub fn size_bytes(&self) -> usize {
        self.layout().size
    }
    
    /// Returns the alignment of this type in bytes
    pub fn alignment_bytes(&self) -> usize {
        self.layout().alignment
    }
}

impl From<mir::Type> for Type {
    fn from(value: mir::Type) -> Self {
        match value {
            mir::Type::Int => Type::Int32,
            mir::Type::Float => Type::Float32,
            mir::Type::Usize => Type::UInt64, // 64-bit platform
            mir::Type::String => Type::String,
            mir::Type::Bool => Type::Bool,
            mir::Type::Array(element_type, size) => Type::Array {
                element_type: Box::new(Type::from(*element_type)),
                size,
            },
            mir::Type::Void => Type::Void,
        }
    }
}