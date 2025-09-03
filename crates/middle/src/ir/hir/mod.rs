/*
 * This module handles the high-level intermediate representation for the compiler
 */

use std::{collections::HashMap, hash::Hash};

use snowflake_front::{
    ast::{BinaryOpKind, ItemIndex, UnaryOpKind}, compilation_unit::VariableIndex
};
use snowflake_common::{text::span::TextSpan, token::Token, typings::Type};

mod builder;
mod writer;

#[allow(unused)]
pub use builder::HIRBuilder;

#[allow(unused)]
pub use writer::HIRWriter;


#[derive(Debug)]
pub struct HIR {
    pub functions: HashMap<ItemIndex, Vec<HIRStatement>>,
    pub top_statements: HashMap<ItemIndex, Vec<HIRStatement>>,
    pub source_map: HashMap<HIRNodeId, TextSpan>,  // Source location mapping
}

#[derive(Debug)]
pub struct ScopeInfo {
    pub parent: Option<ScopeId>,
    pub variables: Vec<VariableIndex>,
    pub is_loop_scope: bool,
}

#[derive(Debug)]
pub struct HIRContext {
    pub scopes: HashMap<ScopeId, ScopeInfo>,
    pub current_scope: ScopeId,
    pub next_scope_id: usize,
    pub next_node_id: usize,
}

impl HIRContext {
    pub fn new() -> Self {
        Self {
            scopes: HashMap::new(),
            current_scope: ScopeId(0),
            next_scope_id: 1,
            next_node_id: 0,
        }
    }

    pub fn next_node_id(&mut self) -> HIRNodeId {
        let id = HIRNodeId(self.next_node_id);
        self.next_node_id += 1;
        id
    }

    pub fn enter_scope(&mut self, is_loop_scope: bool) -> ScopeId {
        let scope_id = ScopeId(self.next_scope_id);
        self.next_scope_id += 1;

        self.scopes.insert(scope_id, ScopeInfo {
            parent: Some(self.current_scope),
            variables: Vec::new(),
            is_loop_scope,
        });

        self.current_scope = scope_id;
        scope_id
    }

    pub fn exit_scope(&mut self) {
        if let Some(scope) = self.scopes.get(&self.current_scope) {
            if let Some(parent) = scope.parent {
                self.current_scope = parent;
            } else {
                // If no parent, reset to root scope
                self.current_scope = ScopeId(0);
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HIRNodeId(usize);

#[derive(Debug, Clone)]
pub struct HIRStatement {
    pub kind: HIRStmtKind,
    pub id: HIRNodeId,
    pub span: TextSpan,
}

#[derive(Debug, Clone)]
pub enum HIRStmtKind {
    Expression { expr: HIRExpression },
    Assignment {
        target: HIRExpression,  // Can be variable, index, etc.
        value: HIRExpression,
    },
    Declaration {
        var_idx: VariableIndex,
        init_expr: Option<HIRExpression>,
        is_mutable: bool,
    },
    Const {
        var_idx: VariableIndex,
        init_expr: Option<HIRExpression>,
    },
    Return { expr: HIRExpression },
    Loop { body: Vec<HIRStatement> },
    Item { item_id: HIRItemId },
}

#[derive(Debug, Clone)]
pub struct HIRItemId {
    pub from: ItemIndex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ScopeId(usize);

#[derive(Debug, Clone)]
pub struct HIRExpression {
    pub kind: HIRExprKind,
    pub ty: Type,
    pub id: HIRNodeId,
    pub span: TextSpan,
}

#[derive(Debug, Clone)]
pub enum HIRExprKind {
    Number(i64),
    Float(f64),
    Usize(usize),
    String(String),
    Bool(bool),
    Unit,
    Var { var_idx: VariableIndex },
    Array {
        elements: Vec<HIRExpression>,
        element_type: Type,
        alloc_type: AllocType,
    },
    Index {
        object: Box<HIRExpression>,
        index: Box<HIRExpression>,
        bounds_check: bool,
        length: Box<HIRExpression>,
    },
    Tuple {
        elements: Vec<HIRExpression>,
        element_types: Vec<Box<Type>>,
    },
    Field {
        object: Box<HIRExpression>,
        field: Box<HIRExpression>,
    },
    Struct {
        fields: Vec<HIRExprField>,
        tail_expr: HIRStructTailExpr,
    },
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
        fx_idx: ItemIndex,
        args: Vec<HIRExpression>,
    },
    If {
        condition: Box<HIRExpression>,
        then_block: Box<HIRExpression>,
        else_block: Option<Box<HIRExpression>>,
    },
    Block {
        body: Box<Block>,
        scope_id: ScopeId,
    },
    Break,
    Continue,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub statements: Vec<Box<HIRStatement>>,
    pub span: TextSpan,
}

#[derive(Debug, Clone)]
pub struct HIRExprField {
    pub identifier: Token,
    pub expr: HIRExpression,
    pub is_shorthand: bool,
}

#[derive(Debug, Clone)]
pub enum HIRStructTailExpr {
    None,
    Default(TextSpan),
}

#[derive(Debug, Clone, Copy)]
pub enum AllocType {
    Stack, // [T; N] - static array
    Heap, // Vec<T> - dynamic array
}