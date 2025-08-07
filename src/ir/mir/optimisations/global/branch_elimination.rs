use std::collections::{HashMap, HashSet};
use crate::ir::mir::{basic_block::BasicBlockIdx, builder::Dominators, optimisations::MIRPass, BasicBlocks, Constant, Function, TerminatorKind, Value, MIR};


/// Branch Elimination is a global optimization pass that removes unnecessary branches.
///
/// This pass analyzes the control flow of the program and eliminates branches that do not affect the final outcome.
/// Such an optimization happens in the following scenarios:
/// - If a branch always leads to the same block, it can be removed.
/// - If a branch condition is always true or false, the branch can be simplified.
/// - If all paths from a conditional branch lead to the same destination (through dominance analysis).
pub struct BranchElimination;

impl BranchElimination {
    /// Computes dominators using a simple iterative algorithm
    fn compute_dominators(&self, function: &Function, basic_blocks: &BasicBlocks) -> Dominators {
        let mut dominators = Dominators::new();
        let predecessors = function.predecessors(basic_blocks);
        
        if function.basic_blocks.is_empty() {
            return dominators;
        }
        
        let entry_bb = function.basic_blocks[0]; // First block is entry
        let mut changed = true;
        
        // Initialize: entry block dominates itself, all others start with universal set
        let mut dom_sets: HashMap<BasicBlockIdx, HashSet<BasicBlockIdx>> = HashMap::new();

        // Entry block only dominates itself initially
        let mut entry_set = HashSet::new();
        entry_set.insert(entry_bb);
        dom_sets.insert(entry_bb, entry_set);
        
        // All other blocks start dominated by all blocks (will be refined)
        for &bb_idx in function.basic_blocks.iter().skip(1) {
            let all_blocks: HashSet<_> = function.basic_blocks.iter().copied().collect();
            dom_sets.insert(bb_idx, all_blocks);
        }
        
        // Iterative refinement
        while changed {
            changed = false;
            
            for &bb_idx in function.basic_blocks.iter().skip(1) { // Skip entry block
                let mut new_dom_set = HashSet::new();
                new_dom_set.insert(bb_idx); // Block always dominates itself
                
                if let Some(pred_list) = predecessors.get(bb_idx) {
                    if !pred_list.is_empty() {
                        // Start with dominators of first predecessor
                        let mut intersection = dom_sets[&pred_list[0]].clone();
                        
                        // Intersect with dominators of all predecessors
                        for &pred in pred_list.iter().skip(1) {
                            intersection = intersection.intersection(&dom_sets[&pred]).copied().collect();
                        }
                        
                        new_dom_set.extend(intersection);
                    }
                }
                
                if dom_sets[&bb_idx] != new_dom_set {
                    dom_sets.insert(bb_idx, new_dom_set);
                    changed = true;
                }
            }
        }
        
        // Convert to immediate dominators
        for &bb_idx in function.basic_blocks.iter().skip(1) {
            let dom_set = &dom_sets[&bb_idx];
            
            // Find immediate dominator (closest dominator that isn't self)
            let mut candidates: Vec<_> = dom_set.iter().filter(|&&d| d != bb_idx).copied().collect();
            candidates.sort_by_key(|_| dom_set.len()); // Heuristic: prefer blocks with fewer dominators
            
            for &candidate in &candidates {
                let candidate_doms = &dom_sets[&candidate];
                // Check if this candidate is not dominated by any other candidate
                let is_immediate = candidates.iter().all(|&other| {
                    other == candidate || !candidate_doms.contains(&other)
                });
                
                if is_immediate {
                    dominators.set_idom(bb_idx, candidate);
                    break;
                }
            }
        }
        
        dominators
    }
    
    /// Checks if a conditional branch always leads to the same block through dominance
    fn can_eliminate_conditional(&self, _switch_bb: BasicBlockIdx, default_target: BasicBlockIdx, 
                                 case_targets: &[(i32, BasicBlockIdx)], dominators: &Dominators) -> Option<BasicBlockIdx> {
        let mut all_targets = vec![default_target];
        all_targets.extend(case_targets.iter().map(|(_, target)| *target));
        
        // If all targets are the same, we can eliminate the branch
        if all_targets.iter().all(|&target| target == default_target) {
            return Some(default_target);
        }
        
        // Check if one target dominates all others (advanced case)
        for &potential_dominator in &all_targets {
            if all_targets.iter().all(|&target| {
                target == potential_dominator || dominators.dominates(target, potential_dominator)
            }) {
                return Some(potential_dominator);
            }
        }
        
        None
    }
}

impl MIRPass for BranchElimination {
    fn run(&mut self, mir: &mut MIR) -> u32 {
        let mut changes = 0;

        // Iterate over all functions in the MIR
        for function in mir.functions.iter_mut() {
            // Compute dominator information for this function
            let dominators = self.compute_dominators(function, &mir.basic_blocks);
            
            // Iterate over all basic blocks in the function
            for bb_idx in function.basic_blocks.iter().copied() {
                let bb = mir.basic_blocks.get_mut(bb_idx).as_mut();
                match bb {
                    None => continue,
                    Some(bb) => {
                        // Check if the terminator is a branch that can be eliminated
                        if let Some(terminator) = bb.terminator.as_mut() {
                            match &terminator.kind {
                                TerminatorKind::Return { .. } | TerminatorKind::Unresolved | TerminatorKind::Assert { .. } => {}
                                TerminatorKind::Goto(target) => {
                                    // Remove self-loops (infinite loops should be handled differently)
                                    if *target == bb_idx {
                                        terminator.kind = TerminatorKind::Unresolved;
                                        changes += 1;
                                    }
                                }
                                TerminatorKind::SwitchInt { value, targets, default } => {
                                    // Check for constant condition
                                    if let Value::Constant(Constant::Int(const_val)) = value {
                                        // Find the target for this constant value
                                        let actual_target = targets.iter()
                                            .find(|(case_val, _)| *case_val == *const_val)
                                            .map(|(_, target)| *target)
                                            .unwrap_or(*default);
                                        
                                        terminator.kind = TerminatorKind::Goto(actual_target);
                                        changes += 1;
                                    }
                                    // Check if all branches lead to the same block
                                    else if let Some(unified_target) = self.can_eliminate_conditional(
                                        bb_idx, *default, targets, &dominators
                                    ) {
                                        terminator.kind = TerminatorKind::Goto(unified_target);
                                        changes += 1;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        
        changes
    }
}