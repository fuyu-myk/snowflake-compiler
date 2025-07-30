use std::fmt::{Display, Formatter};
use anyhow::Result;

use crate::{ast::{BinaryOpKind, BinaryOp, UnaryOpKind, UnaryOp}, typings::Type};


pub struct CAst {
    pub items: Vec<CItem>,
}

impl CAst {
    pub fn new(items: Vec<CItem>) -> Self {
        Self { items }
    }
}

#[derive(Debug, Clone)]
pub enum CType {
    Int,
    Bool,
    Void,
}

impl Display for CType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        return match self {
            CType::Int => write!(f, "int"),
            CType::Bool => write!(f, "bool"),
            CType::Void => write!(f, "void"),
        };
    }
}

impl TryFrom<&Type> for CType {
    type Error = ();

    fn try_from(value: &Type) -> Result<Self, Self::Error> {
        return match value {
            Type::Int => Ok(CType::Int),
            Type::Bool => Ok(CType::Bool),
            Type::Void => Ok(CType::Void),
            Type::Unresolved => Err(()),
            Type::Error => Err(()),
        };
    }
}

pub enum CItem {
    Macro(String, String),
    FxDecl(CFxDecl),
    FxImpl(CFxImpl),
    VarDecl(CVarDecl),
}

pub struct CFxDecl {
    pub identifier: String,
    pub parameters: Vec<CParams>,
    pub return_type: CType,
}

pub struct CFxImpl {
    pub identifier: String,
    pub parameters: Vec<CParams>,
    pub body: Vec<CStatement>,
    pub return_type: CType,
}

pub struct CParams {
    pub name: String,
    pub ty: CType,
}

#[derive(Debug, Clone)]
pub enum CStatement {
    Break,
    VarDecl(CVarDecl),
    Return(CReturn),
    If(CIfStatement),
    While(CWhileStatement),
    Expr(CExpr),
    Block(CBlockStatement),
}

#[derive(Debug, Clone)]
pub struct CVarDecl {
    pub name: String,
    pub ty: CType,
    pub init: Option<CExpr>,
}

#[derive(Debug, Clone)]
pub struct CReturn {
    pub expr: Option<CExpr>,
}

#[derive(Debug, Clone)]
pub struct CIfStatement {
    pub condition: CExpr,
    pub then_block: CBlockStatement,
    pub else_block: Option<CBlockStatement>,
}

#[derive(Debug, Clone)]
pub struct CWhileStatement {
    pub condition: CExpr,
    pub body: CBlockStatement,
}

#[derive(Debug, Clone)]
pub struct CBlockStatement {
    pub statements: Vec<CStatement>
}

#[derive(Debug, Clone)]
pub enum CExpr {
    Number(CNumber),
    Bool(CBool),
    Unary(CUnaryExpr),
    Binary(CBinExpr),
    Parenthesised(Box<CExpr>),
    Assign(CAssignExpr),
    Variable(CVarExpr),
    Call(CCallExpr),
}

#[derive(Debug, Clone)]
pub struct CNumber {
    pub value: i64,
}

#[derive(Debug, Clone)]
pub struct CBool {
    pub value: bool,
}

#[derive(Debug, Clone)]
pub struct CUnaryExpr {
    pub operator: CUnaryOp,
    pub expr: Box<CExpr>,
}

#[derive(Debug, Clone)]
pub enum CUnaryOp {
    Negation,
    BitwiseNot,
}

impl Display for CUnaryOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        return match self {
            CUnaryOp::Negation => write!(f, "-"),
            CUnaryOp::BitwiseNot => write!(f, "~"),
        };
    }
}

impl TryFrom<&UnaryOp> for CUnaryOp {
    type Error = ();

    fn try_from(value: &UnaryOp) -> Result<Self, Self::Error> {
        return match &value.kind {
            UnaryOpKind::Negation => Ok(CUnaryOp::Negation),
            UnaryOpKind::BitwiseNot => Ok(CUnaryOp::BitwiseNot),
        };
    }
}

#[derive(Debug, Clone)]
pub struct CBinExpr {
    pub operator: CBinOp,
    pub left: Box<CExpr>,
    pub right: Box<CExpr>,
}

#[derive(Debug, Clone)]
pub enum CBinOp {
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
    Equals,
    NotEquals,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
    ShiftLeft,
    ShiftRight,
}

impl Display for CBinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        return match self {
            CBinOp::Plus => write!(f, "+"),
            CBinOp::Minus => write!(f, "-"),
            CBinOp::Multiply => write!(f, "*"),
            CBinOp::Divide => write!(f, "/"),
            CBinOp::Modulo => write!(f, "%"),
            CBinOp::BitwiseAnd => write!(f, "&"),
            CBinOp::BitwiseOr => write!(f, "|"),
            CBinOp::BitwiseXor => write!(f, "^"),
            CBinOp::ShiftLeft => write!(f, "<<"),
            CBinOp::ShiftRight => write!(f, ">>"),
            CBinOp::Equals => write!(f, "=="),
            CBinOp::NotEquals => write!(f, "!="),
            CBinOp::LessThan => write!(f, "<"),
            CBinOp::GreaterThan => write!(f, ">"),
            CBinOp::LessThanOrEqual => write!(f, "<="),
            CBinOp::GreaterThanOrEqual => write!(f, ">="),
        };
    }
}

impl TryFrom<&BinaryOp> for CBinOp {
    type Error = ();

    fn try_from(value: &BinaryOp) -> Result<Self, Self::Error> {
        return match &value.kind {
            BinaryOpKind::Plus => Ok(CBinOp::Plus),
            BinaryOpKind::Minus => Ok(CBinOp::Minus),
            BinaryOpKind::Multiply => Ok(CBinOp::Multiply),
            BinaryOpKind::Divide => Ok(CBinOp::Divide),
            BinaryOpKind::Modulo => Ok(CBinOp::Modulo),
            BinaryOpKind::Equals => Ok(CBinOp::Equals),
            BinaryOpKind::NotEquals => Ok(CBinOp::NotEquals),
            BinaryOpKind::BitwiseAnd => Ok(CBinOp::BitwiseAnd),
            BinaryOpKind::BitwiseOr => Ok(CBinOp::BitwiseOr),
            BinaryOpKind::BitwiseXor => Ok(CBinOp::BitwiseXor),
            BinaryOpKind::ShiftLeft => Ok(CBinOp::ShiftLeft),
            BinaryOpKind::ShiftRight => Ok(CBinOp::ShiftRight),
            BinaryOpKind::LessThan => Ok(CBinOp::LessThan),
            BinaryOpKind::GreaterThan => Ok(CBinOp::GreaterThan),
            BinaryOpKind::LessThanOrEqual => Ok(CBinOp::LessThanOrEqual),
            BinaryOpKind::GreaterThanOrEqual => Ok(CBinOp::GreaterThanOrEqual),
            BinaryOpKind::Power => Err(()),
        };
    }
}

#[derive(Debug, Clone)]
pub struct CAssignExpr {
    pub name: String,
    pub expr: Box<CExpr>,
}

#[derive(Debug, Clone)]
pub struct CVarExpr {
    pub name: String,
}

#[derive(Debug, Clone)]
pub struct CCallExpr {
    pub name: String,
    pub args: Vec<CExpr>,
}