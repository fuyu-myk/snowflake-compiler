/*
 * This program handles the logic for basic blocks in the MIR
 * 
 * A basic block is a node in the MIR that contains a sequence of statements executed sequentially.
 * There are no branches one
 * This allows for easier data flow analyses and optimisations
 */

use std::fmt::{Display, Formatter};

use snowflake_compiler::{idx, Idx};

use crate::ir::mir::{InstructionIdx, Terminator, TerminatorKind};


#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub instructions: Vec<InstructionIdx>,
    pub terminator: Option<Terminator>,
    pub idx: BasicBlockIdx,
}

impl BasicBlock {
    pub fn new(idx: BasicBlockIdx) -> Self {
        Self {
            instructions: vec![],
            terminator: None,
            idx: idx,
        }
    }

    #[inline]
    pub fn is_terminated(&self) -> bool {
        self.terminator.is_some()
    }

    #[inline]
    pub fn set_terminator(&mut self, kind: TerminatorKind) {
        tracing::debug!("Setting terminator of {:?} to {:?}", self.idx, kind);
        self.terminator = Some(Terminator::new(kind));
    }

    pub fn maybe_set_terminator(&mut self, kind: TerminatorKind) {
        if !self.is_terminated() {
            self.set_terminator(kind);
        }
    }
}

idx!(BasicBlockIdx);

impl Display for BasicBlockIdx {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "bb{}", self.as_index())
    }
}