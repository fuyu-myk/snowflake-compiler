/*
 * This module handles the high-level intermediate representation for the compiler
 */

use std::collections::HashMap;

use crate::{
    ast::{BinaryOpKind, UnaryOpKind},
    compilation_unit::{FunctionIndex, VariableIndex},
    typings::Type
};

mod builder;
mod writer;

#[allow(unused)]
pub use builder::HIRBuilder;

#[allow(unused)]
pub use writer::HIRWriter;


#[derive(Debug)]
pub struct HIR {
    pub functions: HashMap<FunctionIndex, Vec<HIRStatement>>,
}

#[derive(Debug)]
pub struct HIRStatement {
    pub kind: HIRStmtKind,
}

#[derive(Debug)]
pub enum HIRStmtKind {
    Expression { expr: HIRExpression },
    Assignment {
        var_idx: VariableIndex,
        expr: HIRExpression,
    },
    If {
        condition: HIRExpression,
        then_block: Vec<HIRStatement>,
        else_block: Vec<HIRStatement>,
    },
    Declaration {
        var_idx: VariableIndex,
        init: Option<HIRExpression>,
    },
    Block { body: Vec<HIRStatement> },
    Return { expr: HIRExpression },
    Loop { body: Vec<HIRStatement> },
    Break,
}

#[derive(Debug, Clone)]
pub struct HIRExpression {
    pub kind: HIRExprKind,
    pub ty: Type,
}

#[derive(Debug, Clone)]
pub enum HIRExprKind {
    Number(i64),
    Bool(bool),
    Unit,
    Var(VariableIndex),
    Binary {
        operator: BinaryOpKind,
        left: Box<HIRExpression>,
        right: Box<HIRExpression>,
    },
    Unary {
        operator: UnaryOpKind,
        operand: Box<HIRExpression>,
    },
    Call {
        fx_idx: FunctionIndex,
        args: Vec<HIRExpression>,
    },
}