use std::collections::{HashMap, HashSet};

use snowflake_common::{bug_report, Idx, IndexVec};
use snowflake_front::{
    ast::ItemIndex, compilation_unit::{GlobalScope, VariableIndex}
};
use snowflake_common::{
    diagnostics::DiagnosticsReportCell,
    text::span::TextSpan
};

use crate::ir::{
    hir::{HIRExprKind, HIRExpression, HIRStatement, HIRStmtKind, QualifiedPath, HIR}, 
    mir::{basic_block::{BasicBlock, BasicBlockIdx}, AssertMessage, BasicBlocks, BinOp, Constant, Function, FunctionIdx, Global, GlobalIdx, Instruction, InstructionIdx, InstructionKind, ObjectKind, PhiNode, TerminatorKind, Type, Value, MIR}
};


pub struct MIRBuilder {
    mir: MIR,
    diagnostics: DiagnosticsReportCell,
}

impl MIRBuilder {
    pub fn new(diagnostics: DiagnosticsReportCell) -> Self {
        Self { mir: MIR::new(), diagnostics }
    }

    /// Evaluate a constant expression at compile time
    fn evaluate_const_expr(&self, expr: &HIRExpression, _global_scope: &GlobalScope) -> Value {
        match &expr.kind {
            HIRExprKind::Number(value) => Value::Constant(Constant::Int(*value as i32)),
            HIRExprKind::Float(value) => Value::Constant(Constant::Float(*value as f32)),
            HIRExprKind::Bool(value) => Value::Constant(Constant::Bool(*value)),
            _ => {
                // TODO: const expressions for non-literals
                Value::Constant(Constant::Void)
            }
        }
    }

    /// Builds the MIR.
    /// 
    /// All functions are built first, then all calls are resolved as instructions.
    pub fn build(mut self, hir: &HIR, global_scope: &GlobalScope) -> MIR {
        let mut fx_map: HashMap<ItemIndex, FunctionIdx> = HashMap::new();
        let mut calls_to_resolve = Vec::new();

        for (_, statements) in hir.top_statements.iter() {
            for statement in statements {
                if let HIRStmtKind::Const { var_idx, init_expr } = &statement.kind {
                    let variable = &global_scope.variables[*var_idx];
                    let initializer = init_expr.as_ref().map(|expr| {
                        self.evaluate_const_expr(expr, global_scope)
                    });
                    
                    let global = Global {
                        name: variable.name.tokens.last().unwrap().span.literal.clone(),
                        ty: variable.ty.clone().into(),
                        initializer,
                        is_constant: true,
                        variable_index: *var_idx,
                    };
                    
                    self.mir.globals.push(global);
                }
            }
        }

        // Building every function
        for (fx_idx, fx_body) in hir.functions.iter() {
            // Check if this function exists in global scope (skip synthetic functions)
            let fx_opt = global_scope.functions.indexed_iter()
                .find(|(idx, _)| *idx == *fx_idx)
                .map(|(_, fx)| fx);
            
            let function_builder = if let Some(fx) = fx_opt {
                // Regular function with declaration
                FunctionBuilder::new(Function {
                    name: fx.name.clone(),
                    params: fx.parameters.clone(),
                    basic_blocks: Vec::new(),
                    instructions: IndexVec::new(),
                    locals: HashMap::new(),
                    return_type: fx.return_type.clone().into()
                }, &self.mir.globals)
            } else {
                // Synthetic function (e.g., global init), create a default one
                FunctionBuilder::new(Function {
                    name: "__global_init".to_string(),
                    params: Vec::new(),
                    basic_blocks: Vec::new(),
                    instructions: IndexVec::new(),
                    locals: HashMap::new(),
                    return_type: crate::ir::mir::Type::Void
                }, &self.mir.globals)
            };

            let (fx, to_be_resolved) = function_builder.build(&mut self.mir.basic_blocks, global_scope, fx_body);
            let mir_fx_idx = self.mir.functions.push(fx);

            calls_to_resolve.extend(to_be_resolved.into_iter().map(
                |(instruct_idx, fx_idx)| (instruct_idx, fx_idx, mir_fx_idx),
            ));

            fx_map.insert(*fx_idx, mir_fx_idx);
        }

        // Resolving every call
        for (instruct_idx, fx_idx, fx_called) in calls_to_resolve {
            let mir_fx_idx = fx_map.get(&fx_idx).copied()
                .unwrap_or_else(|| {
                    let fx_name = &global_scope.functions.get(fx_idx).name;
                    bug_report!("Function '{}' (idx {:?}) not found in fx_map. Available functions: {:?}", 
                        fx_name, fx_idx, fx_map.keys().collect::<Vec<_>>())
                });
            
            let callee_fn = &self.mir.functions[mir_fx_idx];
            let actual_return_type = callee_fn.basic_blocks.iter()
                .filter_map(|bb_idx| {
                    let bb = self.mir.basic_blocks.get_or_panic(*bb_idx);
                    match &bb.terminator().kind {
                        TerminatorKind::Return { value } => {
                            match value {
                                Value::InstructionRef(instr_idx) => {
                                    Some(callee_fn.instructions.get(*instr_idx).ty.clone())
                                }
                                _ => Some(callee_fn.return_type.clone())
                            }
                        }
                        _ => None
                    }
                })
                .next()
                .unwrap_or_else(|| callee_fn.return_type.clone());
            
            let instruction = self.mir.functions[fx_called].instructions.get_mut(instruct_idx);

            match &mut instruction.kind {
                InstructionKind::Call { fx_idx: call_fx_idx, .. } => {
                    *call_fx_idx = mir_fx_idx;
                    
                    instruction.ty = actual_return_type;
                }
                _ => bug_report!("Expected call instruction, found {:?}", instruction.kind),
            }
        }

        self.mir
    }
}

type LocalDefinitions = HashMap<VariableIndex, HashMap<BasicBlockIdx, InstructionIdx>>;

struct LoopInfo {
    entry_bb: BasicBlockIdx,
    break_blocks: Vec<BasicBlockIdx>,
}

struct FunctionBuilder {
    temp_var_counter: usize,
    function: Function,
    loops: Vec<LoopInfo>,
    definitions: LocalDefinitions,
    incomplete_phis: HashMap<BasicBlockIdx, Vec<(InstructionIdx, VariableIndex)>>,
    sealed_blocks: HashSet<BasicBlockIdx>,
    calls_to_resolve: Vec<(InstructionIdx, ItemIndex)>,
    globals: IndexVec<crate::ir::mir::GlobalIdx, Global>,
}

impl FunctionBuilder {
    pub fn new(function: Function, globals: &IndexVec<GlobalIdx, Global>) -> Self {
        Self {
            temp_var_counter: 0,
            function,
            loops: vec![],
            definitions: HashMap::new(),
            incomplete_phis: HashMap::new(),
            sealed_blocks: HashSet::new(),
            calls_to_resolve: Vec::new(),
            globals: globals.clone(),
        }
    }

    pub fn build(mut self, basic_blocks: &mut BasicBlocks, global_scope: &GlobalScope, body: &[HIRStatement]) -> (
        Function,
        Vec<(InstructionIdx, ItemIndex)>,
    ) {
        // Basic block building logic
        let mut bb_builder = BasicBlockBuilder::new(basic_blocks, &mut self.function);
        for (idx, var_idx) in self.function.params.clone().into_iter().enumerate() {
            let param_ty = global_scope.variables.get(var_idx).ty.clone().into();
            let instruct_idx = bb_builder.add_instruction(
                basic_blocks,
                &mut self.function,
                Instruction::new(
                    InstructionKind::Value(Value::ParamRef(idx)),
                    param_ty,
                    TextSpan::default(), // TODO: Track parameter spans from function declaration
                ),
            );
            self.write_variable(var_idx, bb_builder.current, instruct_idx);
        }

        // Statement building logic
        let mut tail_expression: Option<(&HIRExpression, TextSpan)> = None;
        for statement in body.iter() {
            match &statement.kind {
                HIRStmtKind::TailExpression { expr } => {
                    tail_expression = Some((expr, statement.span.clone()));
                    let value = self.build_expr(basic_blocks, &mut bb_builder, global_scope, expr);
                    let ty: Type = match &value {
                        Value::InstructionRef(instr_ref) => {
                            self.function.instructions[*instr_ref].ty.clone()
                        }
                        _ => expr.ty.clone().into(),
                    };

                    if !basic_blocks.get_or_panic(bb_builder.current).is_terminated() {
                        let instruct_idx = bb_builder.add_instruction(
                            basic_blocks,
                            &mut self.function,
                            Instruction::new(InstructionKind::Value(value), ty, statement.span.clone())
                        );

                        bb_builder.terminate(basic_blocks, TerminatorKind::Return {
                            value: Value::InstructionRef(instruct_idx)
                        });
                    }
                }
                _ => self.build_statement(basic_blocks, &mut bb_builder, global_scope, statement)
            }
        }

        // Add implicit return if the current basic block isn't terminated
        if !basic_blocks.get_or_panic(bb_builder.current).is_terminated() {
            // Only add implicit return for void functions
            // Non-void functions without explicit returns should get a default value return
            let return_value = if tail_expression.is_some() {
                // Should already have been handled above
                unreachable!("Should have been terminated by a tail expression")
            } else {
                match self.function.return_type {
                    Type::Void => Value::Constant(Constant::Void),
                    Type::Int => {
                        tracing::warn!("Function '{}' with return type {:?} lacks explicit return statement, adding default return 0", 
                                    self.function.name, self.function.return_type);
                        Value::Constant(Constant::Int(0))
                    }
                    Type::Float => {
                        tracing::warn!("Function '{}' with return type {:?} lacks explicit return statement, adding default return 0.0", 
                                    self.function.name, self.function.return_type);
                        Value::Constant(Constant::Float(0.0))
                    }
                    Type::String => {
                        tracing::warn!("Function '{}' with return type {:?} lacks explicit return statement, adding default empty string return", 
                                    self.function.name, self.function.return_type);
                        Value::Constant(Constant::String(String::new()))
                    }
                    Type::Bool => {
                        tracing::warn!("Function '{}' with return type {:?} lacks explicit return statement, adding default return false", 
                                    self.function.name, self.function.return_type);
                        Value::Constant(Constant::Int(0))
                    }
                    Type::Usize => {
                        tracing::warn!("Function '{}' with return type {:?} lacks explicit return statement, adding default return 0", 
                                    self.function.name, self.function.return_type);
                        Value::Constant(Constant::Usize(0))
                    }
                    Type::Array(_, _) => {
                        tracing::warn!("Function '{}' with return type {:?} lacks explicit return statement, adding default empty array return", 
                                    self.function.name, self.function.return_type);
                        Value::InstructionRef(bb_builder.add_instruction(
                            basic_blocks,
                            &mut self.function,
                            Instruction::new(
                                InstructionKind::ArrayInit { elements: Vec::new() },
                                Type::Array(Box::new(Type::Void), 0),
                                TextSpan::default(),
                            ),
                        ))
                    }
                    Type::Object(_) => {
                        tracing::warn!("Function '{}' with return type {:?} lacks explicit return statement, adding default empty tuple return", 
                                    self.function.name, self.function.return_type);
                        Value::InstructionRef(bb_builder.add_instruction(
                            basic_blocks,
                            &mut self.function,
                            Instruction::new(
                                InstructionKind::Object {
                                    kind: ObjectKind::Unresolved,
                                    fields: Vec::new()
                                },
                                Type::Object(vec![Type::Void.into()]),
                                TextSpan::default(),
                            ),
                        ))
                    }
                    Type::Unit => {
                        // TODO: check if this is appropriate
                        Value::Constant(Constant::Void)
                    }
                    Type::Enum { .. } => {
                        tracing::warn!("Function '{}' with enum return type lacks explicit return statement, adding default void return", 
                                    self.function.name);
                        Value::Constant(Constant::Void)
                    }
                }
            };

            bb_builder.terminate(basic_blocks, TerminatorKind::Return { value: return_value });
        }

        // Ensuring no incomplete phis
        let predecessors = self.function.predecessors(basic_blocks);
        for basic_block in self.function.basic_blocks.clone().into_iter() {
            if !self.is_sealed(basic_block) {
                self.seal_block(basic_blocks, basic_block, global_scope);
            }

            let immediate_predecessors = predecessors.get(basic_block);
            for instruct_idx in basic_blocks.get_or_panic(basic_block).instructions.iter().copied() {
                let instruction = &self.function.instructions[instruct_idx];
                if let InstructionKind::Phi(phi) = &instruction.kind {
                    let predecessors_len = immediate_predecessors.map(|ip| ip.len()).unwrap_or_default();

                    assert_eq!(
                        phi.operands.len(),
                        predecessors_len,
                        "Phi node in {} has {} operand(s), but {} predecessor(s). Operands: {:?}, Predecessors: {:?}",
                        basic_block,
                        phi.operands.len(),
                        predecessors_len,
                        phi.operands,
                        immediate_predecessors
                    );

                    for (predecessor, _) in phi.operands.iter() {
                        if let Some(immediate_predecessors) = immediate_predecessors {
                            assert!(
                                immediate_predecessors.contains(predecessor),
                                "Phi node {:?} has operand for predecessor {:?}, but is not an immediate predecessor of {:?}",
                                phi,
                                predecessor,
                                basic_block,
                            );
                        }
                    }
                }
            }
        }

        assert!(self.incomplete_phis.is_empty());
        assert!(self.loops.is_empty());

        // Update function return type if it's an Enum with empty variants
        //   - Happens when a function declares it returns an enum type,
        //     but the actual return value is a specific variant (Object type)
        if let Type::Enum { variants, .. } = &self.function.return_type {
            if variants.is_empty() {
                // Find the actual return type from return statements
                for bb_idx in &self.function.basic_blocks {
                    let bb = basic_blocks.get_or_panic(*bb_idx);
                    if let TerminatorKind::Return { value } = &bb.terminator().kind {
                        if let Value::InstructionRef(instr_idx) = value {
                            let actual_type = self.function.instructions[*instr_idx].ty.clone();
                            self.function.return_type = actual_type;
                            break;
                        }
                    }
                }
            }
        }

        (self.function, self.calls_to_resolve)
    }

    #[inline]
    /// Creates a variable definition in `FunctionBuilder`, as well as a local definition in `Function`
    pub fn write_variable(&mut self, var_idx: VariableIndex, bb_idx: BasicBlockIdx, instruct_idx: InstructionIdx) {
        tracing::debug!("Writing variable {:?} in {} as {:?}", var_idx, bb_idx, instruct_idx);

        self.definitions.entry(var_idx).or_default().insert(bb_idx, instruct_idx);
        self.function.locals.insert(instruct_idx, var_idx);
    }

    #[inline]
    pub fn push_loop(&mut self, entry_bb: BasicBlockIdx) {
        tracing::debug!("Entering loop at bb{}", entry_bb);
        self.loops.push(LoopInfo {
            entry_bb,
            break_blocks: Vec::new(),
        });
    }

    #[inline]
    pub fn pop_loop(&mut self) -> Vec<BasicBlockIdx> {
        self.loops.pop().unwrap().break_blocks
    }

    pub fn build_statement(&mut self, basic_blocks: &mut BasicBlocks, bb_builder: &mut BasicBlockBuilder, global_scope: &GlobalScope, statement: &HIRStatement) {
        match &statement.kind {
            HIRStmtKind::Expression { expr } => {
                // Transforms expression into a value and assigns it to a new instruction
                // Eg: `1 + 2` becomes `%0 = 1 + 2`
                let value = self.build_expr(basic_blocks, bb_builder, global_scope, expr);
                let ty = expr.ty.clone().into();

                // Only add instruction if the current basic block is not already terminated
                // (this is such that break/continue expressions can terminate the block)
                if !basic_blocks.get_or_panic(bb_builder.current).is_terminated() {
                    bb_builder.add_instruction(
                        basic_blocks,
                        &mut self.function,
                        Instruction::new(InstructionKind::Value(value), ty, statement.span.clone())
                    );
                }
            }
            HIRStmtKind::TailExpression { expr } => {
                let val = self.build_expr(basic_blocks, bb_builder, global_scope, expr);
                let ty = match &val {
                    Value::InstructionRef(instr_ref) => {
                        self.function.instructions[*instr_ref].ty.clone()
                    }
                    _ => expr.ty.clone().into(),
                };
                
                if !basic_blocks.get_or_panic(bb_builder.current).is_terminated() {
                    bb_builder.add_instruction(
                        basic_blocks,
                        &mut self.function,
                        Instruction::new(InstructionKind::Value(val), ty, statement.span.clone())
                    );
                }
            }
            HIRStmtKind::Assignment { target, value } => {
                match &target.kind {
                    HIRExprKind::Var { var_idx } => {
                        // Handle simple variable assignment: var = value
                        let val = self.build_expr(basic_blocks, bb_builder, global_scope, value);
                        
                        if !basic_blocks.get_or_panic(bb_builder.current).is_terminated() {
                            let instruct_idx = bb_builder.add_instruction(
                                basic_blocks,
                                &mut self.function,
                                Instruction::new(InstructionKind::Value(val), value.ty.clone().into(), statement.span.clone())
                            );

                            self.write_variable(*var_idx, bb_builder.current, instruct_idx);
                        }
                    }
                    HIRExprKind::Index { object, index, bounds_check, length } => {
                        // Handle indexed assignment: array[index] = value
                        let array_val = self.build_expr(basic_blocks, bb_builder, global_scope, object);
                        let index_val = self.build_expr(basic_blocks, bb_builder, global_scope, index);
                        let value_val = self.build_expr(basic_blocks, bb_builder, global_scope, value);
                        let length_val = self.build_expr(basic_blocks, bb_builder, global_scope, length);

                        if *bounds_check {
                            self.arr_index_bounds_check(
                                basic_blocks,
                                bb_builder,
                                global_scope,
                                object,
                                index,
                                &index_val,
                                length_val,
                            );
                        }
                        
                        if !basic_blocks.get_or_panic(bb_builder.current).is_terminated() {
                            bb_builder.add_instruction(
                                basic_blocks,
                                &mut self.function,
                                Instruction::new(
                                    InstructionKind::ArrayStore { 
                                        array: array_val, 
                                        index: index_val, 
                                        value: value_val 
                                    }, 
                                    Type::Void, // Store operations don't return a value
                                    statement.span.clone()
                                )
                            );
                        }
                    }
                    HIRExprKind::Field { object: tuple, field: index } => {
                        let tuple_val = self.build_expr(basic_blocks, bb_builder, global_scope, tuple);
                        let index_val = self.build_expr(basic_blocks, bb_builder, global_scope, index);
                        let value_val = self.build_expr(basic_blocks, bb_builder, global_scope, value);

                        if !basic_blocks.get_or_panic(bb_builder.current).is_terminated() {
                            bb_builder.add_instruction(
                                basic_blocks,
                                &mut self.function,
                                Instruction::new(
                                    InstructionKind::ObjectStore { 
                                        object: tuple_val, 
                                        field: index_val, 
                                        value: value_val 
                                    }, 
                                    Type::Void, // Store operations don't return a value
                                    statement.span.clone()
                                )
                            );
                        }
                    }
                    _ => {
                        self.build_expr(basic_blocks, bb_builder, global_scope, target);
                        self.build_expr(basic_blocks, bb_builder, global_scope, value);
                    }
                }
            }
            HIRStmtKind::Declaration { var_idx, init_expr, is_mutable: _ } => {
                // Transforms initialiser into a value and assigns it to a new instruction,
                // where the instruction represents the variable
                // Eg: `let a = 1 + 2` becomes `%0 = 1 + 2`
                // `%0` is now used in place of var `a`
                let value = init_expr.as_ref().map(|init| {
                    self.build_expr(basic_blocks, bb_builder, global_scope, init)
                });
                
                let ty = if let Some(value_ref) = &value {
                    match value_ref {
                        Value::InstructionRef(instr_ref) => {
                            let instr = &self.function.instructions[*instr_ref];
                            instr.ty.clone()
                        }
                        _ => {
                            Type::from(global_scope.variables.get(*var_idx).ty.clone())
                        }
                    }
                } else {
                    Type::from(global_scope.variables.get(*var_idx).ty.clone())
                };
                
                let instruct_idx = bb_builder.add_instruction(
                    basic_blocks,
                    &mut self.function,
                    Instruction::new(InstructionKind::Value(value.unwrap_or(Value::Constant(Constant::Void))), ty, statement.span.clone()),
                );

                self.write_variable(*var_idx, bb_builder.current, instruct_idx);
            }
            HIRStmtKind::Const { var_idx, init_expr } => {
                // Similar to `HIRStmtKind::Declaration`
                let value = init_expr.as_ref().map(|init| {
                    self.build_expr(basic_blocks, bb_builder, global_scope, init)
                });
                
                let ty = if let Some(value_ref) = &value {
                    match value_ref {
                        Value::InstructionRef(instr_ref) => {
                            let instr = &self.function.instructions[*instr_ref];
                            instr.ty.clone()
                        }
                        _ => {
                            Type::from(global_scope.variables.get(*var_idx).ty.clone())
                        }
                    }
                } else {
                    Type::from(global_scope.variables.get(*var_idx).ty.clone())
                };
                
                let instruct_idx = bb_builder.add_instruction(
                    basic_blocks,
                    &mut self.function,
                    Instruction::new(InstructionKind::Value(value.unwrap_or(Value::Constant(Constant::Void))), ty, statement.span.clone()),
                );

                self.write_variable(*var_idx, bb_builder.current, instruct_idx);
            }
            HIRStmtKind::Item { item_id: _ } => {
                // In the future, this could handle local function definitions, etc.
            }
        }
    }

    pub fn build_expr(&mut self, basic_blocks: &mut BasicBlocks, bb_builder: &mut BasicBlockBuilder, global_scope: &GlobalScope, expr: &HIRExpression) -> Value {
        match &expr.kind {
            HIRExprKind::Number(value) => Value::Constant(Constant::Int(*value as i32)),
            HIRExprKind::Float(value) => Value::Constant(Constant::Float(*value as f32)),
            HIRExprKind::Usize(value) => Value::Constant(Constant::Usize(*value)),
            HIRExprKind::String(value) => Value::Constant(Constant::String(value.clone())),
            HIRExprKind::Bool(value) => Value::Constant(Constant::Bool(*value)),
            HIRExprKind::Unit => Value::Constant(Constant::Void),
            HIRExprKind::Var { var_idx } => {
                if let Some(global) = self.globals.iter().find(|g| g.variable_index == *var_idx && g.is_constant) {
                    global.initializer.clone().unwrap_or(Value::Constant(Constant::Void))
                } else if let Some(param_idx) = self.function.params.iter().position(|p| *p == *var_idx) {
                    Value::ParamRef(param_idx)
                } else {
                    let var_name = &global_scope.variables.get(*var_idx).name;
                    let instruct_ref = self.latest_variable_def(basic_blocks, *var_idx, bb_builder.current, global_scope)
                        .unwrap_or_else(|| bug_report!("Variable '{}' (idx {:?}) has no definition in current scope (function: {})", var_name, var_idx, self.function.name));
                    Value::InstructionRef(instruct_ref)
                }
            }
            HIRExprKind::Array { elements, element_type, alloc_type } => {
                // Different instructions for static and dynamic arrays
                match alloc_type {
                    crate::ir::hir::AllocType::Stack => {
                        // Static array - array initialization instruction
                        let element_values: Vec<Value> = elements.iter()
                            .map(|elem| self.build_expr(basic_blocks, bb_builder, global_scope, elem))
                            .collect();

                        let element_span_refs: Vec<&TextSpan> = elements.iter()
                            .map(|elem| &elem.span)
                            .collect();

                        let instruct_ref = bb_builder.add_instruction(
                            basic_blocks,
                            &mut self.function,
                            Instruction::new(
                                InstructionKind::ArrayInit { elements: element_values.clone() },
                                Type::Array(Box::new(element_type.clone().into()), elements.len()),
                                TextSpan::combine_refs(&element_span_refs),
                            ),
                        );

                        Value::InstructionRef(instruct_ref)
                    }
                    crate::ir::hir::AllocType::Heap => {
                        // Dynamic array - allocate then initialize
                        let size = Value::Constant(Constant::Usize(elements.len()));
                        
                        let alloc_ref = bb_builder.add_instruction(
                            basic_blocks,
                            &mut self.function,
                            Instruction::new(
                                InstructionKind::ArrayAlloc { 
                                    element_type: element_type.clone().into(), 
                                    size,
                                },
                                Type::Array(Box::new(element_type.clone().into()), elements.len()),
                                TextSpan::default(),
                            ),
                        );

                        if !elements.is_empty() {
                            let element_values: Vec<Value> = elements.iter()
                                .map(|elem| self.build_expr(basic_blocks, bb_builder, global_scope, elem))
                                .collect();

                            let element_span_refs: Vec<&TextSpan> = elements.iter()
                                .map(|elem| &elem.span)
                                .collect();

                            let init_ref = bb_builder.add_instruction(
                                basic_blocks,
                                &mut self.function,
                                Instruction::new(
                                    InstructionKind::ArrayInit { elements: element_values },
                                    Type::Array(Box::new(element_type.clone().into()), elements.len()),
                                    TextSpan::combine_refs(&element_span_refs),
                                ),
                            );

                            Value::InstructionRef(init_ref)
                        } else {
                            Value::InstructionRef(alloc_ref)
                        }
                    }
                }
            }
            HIRExprKind::Index { object, index, bounds_check, length } => {
                let object_val = self.build_expr(basic_blocks, bb_builder, global_scope, &object);
                let index_val = self.build_expr(basic_blocks, bb_builder, global_scope, &index);
                let length_val = self.build_expr(basic_blocks, bb_builder, global_scope, &length);

                if *bounds_check {
                    self.arr_index_bounds_check(
                        basic_blocks,
                        bb_builder,
                        global_scope,
                        &object,
                        &index,
                        &index_val,
                        length_val,
                    );
                }

                let instruct_ref = bb_builder.add_instruction(
                    basic_blocks,
                    &mut self.function,
                    Instruction::new(
                        InstructionKind::ArrayIndex { 
                            array: object_val, 
                            index: index_val 
                        }, 
                        Type::from(expr.ty.clone()),
                        TextSpan::combine_two(&object.span, &index.span),
                    ),
                );

                Value::InstructionRef(instruct_ref)
            }
            HIRExprKind::Tuple { elements, .. } => {
                let element_values: Vec<Value> = elements.iter()
                    .map(|elem| self.build_expr(basic_blocks, bb_builder, global_scope, elem))
                    .collect();

                let element_span_refs: Vec<&TextSpan> = elements.iter()
                    .map(|elem| &elem.span)
                    .collect();

                let element_types: Vec<Box<Type>> = element_values.iter().zip(elements.iter())
                    .map(|(value, hir_elem)| {
                        match value {
                            Value::InstructionRef(instr_ref) => {
                                let instr = &self.function.instructions[*instr_ref];
                                Box::new(instr.ty.clone())
                            }
                            _ => {
                                Box::new(hir_elem.ty.clone().into())
                            }
                        }
                    })
                    .collect();

                let instruct_ref = bb_builder.add_instruction(
                    basic_blocks,
                    &mut self.function,
                    Instruction::new(
                        InstructionKind::Object {
                            kind: ObjectKind::Tuple,
                            fields: element_values.clone()
                        },
                        Type::Object(element_types),
                        TextSpan::combine_refs(&element_span_refs),
                    ),
                );

                Value::InstructionRef(instruct_ref)
            }
            HIRExprKind::Field { object, field } => {
                let object_val = self.build_expr(basic_blocks, bb_builder, global_scope, &object);
                let field_val = self.build_expr(basic_blocks, bb_builder, global_scope, &field);
                
                // Determine the result type
                let result_ty = match (Type::from(expr.ty.clone()), &object_val, &field_val) {
                    (Type::Enum { .. }, Value::InstructionRef(instr_ref), Value::Constant(Constant::Int(idx))) => {
                        let object_instr = &self.function.instructions[*instr_ref];
                        if let Type::Object(ref element_types) = object_instr.ty {
                            // Extract the field type at the given index
                            if let Some(field_type) = element_types.get(*idx as usize) {
                                field_type.as_ref().clone()
                            } else {
                                Type::from(expr.ty.clone())
                            }
                        } else {
                            Type::from(expr.ty.clone())
                        }
                    }
                    _ => Type::from(expr.ty.clone()),
                };
                
                let instruct_ref = bb_builder.add_instruction(
                    basic_blocks,
                    &mut self.function,
                    Instruction::new(
                        InstructionKind::Field { object: object_val, field: field_val },
                        result_ty,
                        expr.span.clone(),
                    ),
                );
                Value::InstructionRef(instruct_ref)
            }
            HIRExprKind::Struct { fields, path, .. } => {
                let mut field_values = Vec::new();
                
                // Prepend the discriminant as the first field for enums
                let is_enum_variant = if let QualifiedPath::ResolvedEnumVariant(_enum_idx, discriminant) = path {
                    let discriminant_value = Value::Constant(Constant::Usize(*discriminant));
                    field_values.push(discriminant_value);
                    true
                } else {
                    false
                };
                
                for field in fields {
                    let field_value = self.build_expr(basic_blocks, bb_builder, global_scope, &field.expr);
                    field_values.push(field_value);
                }

                // Building an Object type with discriminant + variant fields
                let ty = if is_enum_variant {
                    // Get the field types from the original expression
                    let mut field_types = vec![Box::new(Type::Usize)]; // discriminant
                    for field in fields {
                        field_types.push(Box::new(Type::from(field.expr.ty.clone())));
                    }
                    Type::Object(field_types)
                } else {
                    Type::from(expr.ty.clone())
                };

                let instruct_ref = bb_builder.add_instruction(
                    basic_blocks,
                    &mut self.function,
                    Instruction::new(
                        InstructionKind::Object {
                            kind: ObjectKind::Struct,
                            fields: field_values
                        },
                        ty,
                        expr.span.clone(),
                    ),
                );

                Value::InstructionRef(instruct_ref)
            }
            HIRExprKind::Binary { operator, left, right } => {
                let left_value = self.build_expr(basic_blocks, bb_builder, global_scope, &left);
                let right_value = self.build_expr(basic_blocks, bb_builder, global_scope, &right);
                let ty = expr.ty.clone().into();
                let instruct_ref = bb_builder.add_instruction(
                    basic_blocks,
                    &mut self.function,
                    Instruction::new(
                        InstructionKind::Binary { operator: (*operator).into(), left: left_value, right: right_value },
                        ty,
                        TextSpan::combine_two(&left.span, &right.span),
                    ),
                );

                Value::InstructionRef(instruct_ref)
            },
            HIRExprKind::Unary { operator, operand } => {
                let operand_value = self.build_expr(basic_blocks, bb_builder, global_scope, &operand);
                let ty = expr.ty.clone().into();
                let instruct_ref = bb_builder.add_instruction(
                    basic_blocks,
                    &mut self.function,
                    Instruction::new(
                        InstructionKind::Unary { operator: (*operator).into(), operand: operand_value },
                        ty,
                        operand.span.clone(),
                    )
                );

                Value::InstructionRef(instruct_ref)
            },
            HIRExprKind::If { condition, then_block, else_block } => {
                // A condition bb is constructed first, with a `SwitchInt` terminator that jumps to the
                // then bb if the condition holds true, or the else bb if it is false
                //
                // Finally, a bb, `if_end_bb`, is created to terminate the if statement
                tracing::debug!("Building if expression");

                // building condition
                tracing::debug!("Building condition");
                let condition = self.build_expr(basic_blocks, bb_builder, global_scope, &condition);
                let predecessor = bb_builder.current;
                let then_start_bb = bb_builder.new_bb(basic_blocks, &mut self.function);
                let else_start_bb = bb_builder.new_bb(basic_blocks, &mut self.function);
                let if_end_bb = bb_builder.new_bb(basic_blocks, &mut self.function);

                bb_builder.set_bb(predecessor);
                bb_builder.terminate(
                    basic_blocks,
                    TerminatorKind::SwitchInt {
                        value: condition,
                        targets: vec![(0, else_start_bb)],
                        default: then_start_bb
                    },
                );
                tracing::debug!("Condition built");

                self.seal_block(basic_blocks, then_start_bb, global_scope);
                self.seal_block(basic_blocks, else_start_bb, global_scope);

                // building then block
                tracing::debug!("Building then block");
                bb_builder.set_bb(then_start_bb);
                let then_value = self.build_expr(basic_blocks, bb_builder, global_scope, &then_block);
                let then_exit_bb = bb_builder.current;
                basic_blocks.get_mut_or_panic(then_exit_bb).maybe_set_terminator(TerminatorKind::Goto(if_end_bb));
                tracing::debug!("Then block built");

                // building else block
                tracing::debug!("Building else block");
                bb_builder.set_bb(else_start_bb);
                let else_value = if let Some(else_block) = else_block {
                    self.build_expr(basic_blocks, bb_builder, global_scope, &else_block)
                } else {
                    Value::Constant(Constant::Void)
                };
                let else_exit_bb = bb_builder.current;
                basic_blocks.get_mut_or_panic(else_exit_bb).maybe_set_terminator(TerminatorKind::Goto(if_end_bb));
                tracing::debug!("Else block built");

                // Create merge block and phi node for the result
                bb_builder.set_bb(if_end_bb);
                let ty: Type = expr.ty.clone().into();
                let mut operands = Vec::new();

                let then_block = basic_blocks.get_or_panic(then_exit_bb);
                let then_reaches_merge = if let Some(terminator) = &then_block.terminator {
                    matches!(terminator.kind, TerminatorKind::Goto(_) | TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. })
                } else {
                    false
                };
                
                if then_reaches_merge {
                    match then_value {
                        Value::InstructionRef(then_instr) => operands.push((then_exit_bb, then_instr)),
                        _ => {
                            let then_instr = bb_builder.add_instruction(
                                basic_blocks,
                                &mut self.function,
                                Instruction::new(
                                    InstructionKind::Value(then_value),
                                    ty.clone(),
                                    expr.span.clone(),
                                ),
                            );
                            operands.push((then_exit_bb, then_instr));
                        }
                    }
                }
                
                let else_block = basic_blocks.get_or_panic(else_exit_bb);
                let else_reaches_merge = if let Some(terminator) = &else_block.terminator {
                    matches!(terminator.kind, TerminatorKind::Goto(_) | TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. })
                } else {
                    false
                };
                
                if else_reaches_merge {
                    match else_value {
                        Value::InstructionRef(else_instr) => operands.push((else_exit_bb, else_instr)),
                        _ => {
                            let else_instr = bb_builder.add_instruction(
                                basic_blocks,
                                &mut self.function,
                                Instruction::new(
                                    InstructionKind::Value(else_value),
                                    ty.clone(),
                                    expr.span.clone(),
                                ),
                            );
                            operands.push((else_exit_bb, else_instr));
                        }
                    }
                }

                // Only create a phi node if we have operands from multiple predecessors
                let phi_ref = if operands.len() > 1 {
                    bb_builder.add_instruction(
                        basic_blocks,
                        &mut self.function,
                        Instruction::new(
                            InstructionKind::Phi(PhiNode {
                                operands,
                            }),
                            ty,
                            expr.span.clone(),
                        ),
                    )
                } else if operands.len() == 1 {
                    // Use the value directly
                    operands[0].1
                } else {
                    // Create a void value
                    bb_builder.add_instruction(
                        basic_blocks,
                        &mut self.function,
                        Instruction::new(
                            InstructionKind::Value(Value::Constant(Constant::Void)),
                            ty,
                            expr.span.clone(),
                        ),
                    )
                };

                self.seal_block(basic_blocks, if_end_bb, global_scope);
                tracing::debug!("If expression built");
                Value::InstructionRef(phi_ref)
            }
            HIRExprKind::Block { body, scope_id: _ } => {
                let mut last_value = Value::Constant(Constant::Void);
                
                for statement in body.statements.iter() {
                    match &statement.kind {
                        HIRStmtKind::Expression { expr } => {
                            let _value = self.build_expr(basic_blocks, bb_builder, global_scope, expr);
                            let ty = expr.ty.clone().into();
                            
                            if !basic_blocks.get_or_panic(bb_builder.current).is_terminated() {
                                bb_builder.add_instruction(
                                    basic_blocks,
                                    &mut self.function,
                                    Instruction::new(InstructionKind::Value(_value), ty, statement.span.clone())
                                );
                            }
                            last_value = Value::Constant(Constant::Void);
                        }
                        HIRStmtKind::TailExpression { expr } => {
                            last_value = self.build_expr(basic_blocks, bb_builder, global_scope, expr);
                            
                            let ty = match &last_value {
                                Value::InstructionRef(instr_ref) => {
                                    self.function.instructions[*instr_ref].ty.clone()
                                }
                                _ => {
                                    expr.ty.clone().into()
                                }
                            };
                            
                            if !basic_blocks.get_or_panic(bb_builder.current).is_terminated() {
                                let instruct_idx = bb_builder.add_instruction(
                                    basic_blocks,
                                    &mut self.function,
                                    Instruction::new(InstructionKind::Value(last_value.clone()), ty, statement.span.clone())
                                );
                                last_value = Value::InstructionRef(instruct_idx);
                            }
                        }
                        _ => {
                            self.build_statement(basic_blocks, bb_builder, global_scope, statement);
                            last_value = Value::Constant(Constant::Void);
                        }
                    }
                }
                
                last_value
            }
            HIRExprKind::Call { fx_idx, args } => {
                let args_values = args.iter()
                    .map(|arg| self.build_expr(basic_blocks, bb_builder, global_scope, arg))
                    .collect();
                let args_span_refs: Vec<&TextSpan> = args.iter()
                    .map(|arg| &arg.span).collect();
                let ty = expr.ty.clone().into();
                let instruct_idx = bb_builder.add_instruction(
                    basic_blocks,
                    &mut self.function,
                    Instruction::new(
                        InstructionKind::Call { fx_idx: FunctionIdx::first(), args: args_values },
                        ty,
                        TextSpan::combine_refs(&args_span_refs),
                    )
                );

                self.calls_to_resolve.push((instruct_idx, *fx_idx));
                Value::InstructionRef(instruct_idx)
            }
            HIRExprKind::Return { expr } => {
                // Transforms the return expression to a value
                // If current bb is terminated, create a new bb
                // Terminate the bb with a `Return` terminator
                let value = self.build_expr(basic_blocks, bb_builder, global_scope, expr);
                if basic_blocks.get_or_panic(bb_builder.current).is_terminated() {
                    bb_builder.new_bb(basic_blocks, &mut self.function);
                }

                let _bb = bb_builder.terminate(basic_blocks, TerminatorKind::Return { value: value.clone() });
                value
            }
            HIRExprKind::Loop { body } => {
                // Each loop will undergo the following steps:
                // 1. An entry block will be created
                // 2. The loop body will be constructed; consists of more than one bb
                // 3. Terminate the last block of the body by jumping (Goto) to the entry block
                //     - Only done if last block isn't already terminated
                //     - This is done to prevent the overide of `break` or `return` statements
                // 4. An exit block will be created
                // 5. Update all blocks that should know the exit block of the loop
                let _predecessor = bb_builder.terminate_and(basic_blocks, &mut self.function, TerminatorKind::Goto);
                let loop_entry_bb = bb_builder.current;
                self.push_loop(loop_entry_bb);

                for statement in body.iter() {
                    self.build_statement(basic_blocks, bb_builder, global_scope, statement);
                }

                if !basic_blocks.get_or_panic(bb_builder.current).is_terminated() {
                    bb_builder.terminate(basic_blocks, TerminatorKind::Goto(loop_entry_bb));

                    if !self.is_sealed(bb_builder.current) {
                        self.seal_block(basic_blocks, bb_builder.current, global_scope);
                    }
                }

                // Seal the loop entry block after the loop body is built
                self.seal_block(basic_blocks, loop_entry_bb, global_scope);

                let exit_block = bb_builder.new_bb(basic_blocks, &mut self.function);
                self.pop_loop_and_update(basic_blocks, exit_block);
                self.seal_block(basic_blocks, exit_block, global_scope);

                Value::Constant(Constant::Void)
            }
            HIRExprKind::Break => {
                // Current block terminated with an unresolved terminator (for breaks in loops)
                // maybe problematic?
                let break_block = bb_builder.terminate(basic_blocks, TerminatorKind::Unresolved);
                self.push_depending_block(break_block);
                Value::Constant(Constant::Void)
            }
            HIRExprKind::Continue => {
                // For continue, jump directly to the loop entry block
                if let Some(current_loop) = self.loops.last() {
                    let loop_entry = current_loop.entry_bb;
                    bb_builder.terminate(basic_blocks, TerminatorKind::Goto(loop_entry));
                    Value::Constant(Constant::Void)
                } else {
                    // Continue outside of loop - this should be caught before this point
                    panic!("Continue statement outside of loop");
                }
            }
            HIRExprKind::Path(_) => todo!(),
        }
    }

    fn arr_index_bounds_check(&mut self, basic_blocks: &mut BasicBlocks, bb_builder: &mut BasicBlockBuilder, global_scope: &GlobalScope, object: &Box<HIRExpression>, index: &Box<HIRExpression>, index_val: &Value, length_val: Value) {
        let combined_span = TextSpan::combine_refs(&[&object.span, &index.span]);
    
        let bounds_check_ref = bb_builder.add_instruction(
            basic_blocks,
            &mut self.function,
            Instruction::new(
                InstructionKind::Binary { 
                    operator: BinOp::Lt,
                    left: index_val.clone(),
                    right: length_val.clone(),
                },
                Type::Bool,
                combined_span,
            ),
        );
    
        // Create the basic block for successful array access
        let predecessor = bb_builder.current;
        let array_access_bb = bb_builder.new_bb(basic_blocks, &mut self.function);
    
        bb_builder.set_bb(predecessor);
        bb_builder.terminate(
            basic_blocks,
            TerminatorKind::Assert {
                condition: Value::InstructionRef(bounds_check_ref),
                check: true,
                message: Box::new(AssertMessage::ArrayIndexOutOfBounds { len: length_val, index: index_val.clone() }),
                default: array_access_bb,
            }
        );
    
        bb_builder.set_bb(array_access_bb);
        self.seal_block(basic_blocks, array_access_bb, global_scope);
    }

    pub fn seal_block(&mut self, basic_blocks: &mut BasicBlocks, bb_idx: BasicBlockIdx, global_scope: &GlobalScope) {
        if self.is_sealed(bb_idx) {
            bug_report!("Tried to seal block {} after it was already sealed", bb_idx);
        }

        tracing::debug!("Sealing {:?}", bb_idx);
        if let Some(incomplete_phis) = self.incomplete_phis.get(&bb_idx).cloned() { // use w/out clone??
            tracing::debug!("{:?} has incomplete phis {:?}", bb_idx, incomplete_phis);
            let predecessors = self.function.predecessors(basic_blocks);

            for (incomplete_phi, var_idx) in incomplete_phis.iter().copied() {
                if let Some(replacement_idx) = self.add_phi_operands(
                    basic_blocks,
                    incomplete_phi,
                    var_idx,
                    predecessors.get(bb_idx).unwrap(),
                    global_scope,
                ) {
                    // The phi became trivial, update the variable mapping
                    tracing::debug!("Replacing trivial phi {:?} with {:?} for variable {:?}", 
                                  incomplete_phi, replacement_idx, var_idx);
                    self.write_variable(var_idx, bb_idx, replacement_idx);
                    
                    self.function.instructions[incomplete_phi].kind = InstructionKind::Value(Value::InstructionRef(replacement_idx));
                }
            }
        }

        self.incomplete_phis.remove(&bb_idx);
        self.sealed_blocks.insert(bb_idx);
    }

    pub fn is_sealed(&self, bb_idx: BasicBlockIdx) -> bool {
        self.sealed_blocks.contains(&bb_idx)
    }

    pub fn add_phi_operands(
        &mut self,
        basic_blocks: &mut BasicBlocks,
        phi: InstructionIdx,
        var_idx: VariableIndex,
        preds: &Vec<BasicBlockIdx>,
        global_scope: &GlobalScope,
    ) -> Option<InstructionIdx> {
        tracing::debug!("Adding phi operands for {:?} with predecessors {:?}", phi, preds);

        let mut operands_added = false;
        for pred in preds.iter().copied() {
            let already_exists = {
                let phi_node = self.function.instructions[phi].kind.as_phi_mut().unwrap();
                phi_node.operands.iter().any(|(existing_pred, _)| *existing_pred == pred)
            };

            if already_exists {
                continue;
            }

            let var_ref = self.latest_variable_def(basic_blocks, var_idx, pred, global_scope)
                .unwrap_or_else(|| bug_report!("No definition for variable {:?} in block {:?}", var_idx, pred));
            
            let phi_node = self.function.instructions[phi].kind.as_phi_mut().unwrap();
            phi_node.operands.push((pred, var_ref));
            operands_added = true;
        }

        // Check for triviality only at the end
        if operands_added {
            let phi_node = &self.function.instructions[phi].kind.as_phi().unwrap();
            phi_node.is_trivial(phi)
        } else {
            let phi_node = &self.function.instructions[phi].kind.as_phi().unwrap();
            phi_node.is_trivial(phi)
        }
    }

    /// Returns latest definition of a variable in the current bb and above.
    ///     Runs a local definition check before checking above bbs.
    /// 
    /// Returns None when there is no definition found.
    pub fn latest_variable_def(
        &mut self, basic_blocks: &mut BasicBlocks, var_idx: VariableIndex, bb_idx: BasicBlockIdx, global_scope: &GlobalScope,
    ) -> Option<InstructionIdx> {
        let definitions = self.definitions.get(&var_idx)?;
        match definitions.get(&bb_idx) {
            Some(instruction) => Some(*instruction),
            None => self.latest_variable_def_rec(basic_blocks, var_idx, bb_idx, global_scope),
        }
    }

    pub fn latest_variable_def_rec(
        &mut self, basic_blocks: &mut BasicBlocks, var_idx: VariableIndex, bb_idx: BasicBlockIdx, global_scope: &GlobalScope
    ) -> Option<InstructionIdx> {
        let predecessors = self.function.predecessors(basic_blocks);
        let preceding_bbs = predecessors.get(bb_idx)?;
        let instruct_ref = if !self.is_sealed(bb_idx) {
            tracing::debug!(
                "Found unsealed block {:?} for variable {:?}. Inserting operandless phi",
                bb_idx,
                var_idx,
            );

            let instruct_ref = self.add_operandless_phi(basic_blocks, var_idx, bb_idx, global_scope);
            self.incomplete_phis.entry(bb_idx).or_default().push((instruct_ref, var_idx));
            instruct_ref
        } else if preceding_bbs.len() == 1 {
            self.latest_variable_def(basic_blocks, var_idx, preceding_bbs[0], global_scope)?
        } else {
            tracing::debug!(
                "Inserting operandless phi for variable {:?} in block {:?}",
                var_idx,
                bb_idx,
            );

            let instruct_ref = self.add_operandless_phi(basic_blocks, var_idx, bb_idx, global_scope);
            self.write_variable(var_idx, bb_idx, instruct_ref);
            tracing::debug!(
                "Adding phi operands for {:?} in block {:?}",
                var_idx,
                bb_idx,
            );

            if let Some(replacement_idx) = self.add_phi_operands(basic_blocks, instruct_ref, var_idx, preceding_bbs, global_scope) {
                tracing::debug!("Phi {:?} became trivial, replacing with {:?} for variable {:?}", 
                              instruct_ref, replacement_idx, var_idx);
                self.write_variable(var_idx, bb_idx, replacement_idx);
                
                self.function.instructions[instruct_ref].kind = InstructionKind::Value(Value::InstructionRef(replacement_idx));
                replacement_idx
            } else {
                instruct_ref
            }
        };

        self.write_variable(var_idx, bb_idx, instruct_ref);
        Some(instruct_ref)
    }

    pub fn add_operandless_phi(
        &mut self, basic_blocks: &mut BasicBlocks, var_idx: VariableIndex, bb: BasicBlockIdx, global_scope: &GlobalScope
    ) -> InstructionIdx {
        let instruct_ref = self.function.instructions.push(Instruction::new(
            InstructionKind::Phi(PhiNode::operandless()), global_scope.variables[var_idx].ty.clone().into(), TextSpan::default()
        ));
        let instructions = basic_blocks.get_or_panic(bb).instructions.clone();
        let mut new_instructions = vec![instruct_ref];

        new_instructions.extend(instructions);
        basic_blocks.get_mut_or_panic(bb).instructions = new_instructions;
        instruct_ref
    }

    pub fn pop_loop_and_update(&mut self, basic_blocks: &mut BasicBlocks, exit_block: BasicBlockIdx) {
        tracing::debug!("Exiting loop at bb{}", exit_block);
        let bb_to_update = self.pop_loop();

        for bb in bb_to_update.iter() {
            let bb = basic_blocks.get_mut_or_panic(*bb);
            assert_eq!(
                bb.terminator.as_ref().map(|terminator| &terminator.kind),
                Some(&TerminatorKind::Unresolved),
                "Basic blocks that depend on the start/exit of a loop must have an unresolved terminator"
            );
            bb.set_terminator(TerminatorKind::Goto(exit_block));
        }
    }

    pub fn push_depending_block(&mut self, bb: BasicBlockIdx) {
        self.loops.last_mut().unwrap().break_blocks.push(bb);
    }
}

struct BasicBlockBuilder {
    current: BasicBlockIdx,
}

impl BasicBlockBuilder {
    pub fn new(basic_blocks: &mut BasicBlocks, fx: &mut Function) -> Self {
        let mut builder = Self {
            current: BasicBlockIdx::first(),
        };

        let new_bb = builder.new_bb(basic_blocks, fx);
        builder.set_bb(new_bb);
        builder
    }

    pub fn new_bb(&mut self, basic_blocks: &mut BasicBlocks, fx: &mut Function) -> BasicBlockIdx {
        let new_bb = basic_blocks.push_basic_block();
        fx.basic_blocks.push(new_bb);
        tracing::debug!("Starting new basic block {:?}", new_bb);

        self.current = new_bb;
        new_bb
    }

    pub fn set_bb(&mut self, bb: BasicBlockIdx) {
        tracing::debug!("Setting current basic block to {:?}", bb);
        self.current = bb;
    }

    pub fn add_instruction(&mut self, basic_blocks: &mut BasicBlocks, fx: &mut Function, instruction: Instruction) -> InstructionIdx {
        let current_bb = self.get_current_bb_mut(basic_blocks);
        if let Some(terminator) = current_bb.terminator.as_ref() {
            bug_report!("{} already has a terminator: {:?}", self.current, terminator)
        }

        let instruct_idx = fx.instructions.push(instruction);
        current_bb.instructions.push(instruct_idx);
        instruct_idx
    }

    pub fn terminate(&mut self, basic_blocks: &mut BasicBlocks, terminator: TerminatorKind) -> BasicBlockIdx {
        let bb = self.get_current_bb_mut(basic_blocks);
        if let Some(terminator) = bb.terminator.as_ref() {
            bug_report!("{:?} already has a terminator: {:?}", self.current, terminator)
        }

        match &terminator {
            TerminatorKind::Goto(to) => {
                assert_ne!(*to, self.current, "Unable to jump to same basic block currently");
            }
            TerminatorKind::SwitchInt { targets, default, .. } => {
                assert_ne!(*default, self.current, "Unable to jump to same basic block currently");

                for (_, target) in targets {
                    assert_ne!(*target, self.current, "Unable to jump to same basic block currently");
                }
            }
            TerminatorKind::Assert { default, .. } => {
                assert_ne!(*default, self.current, "Unable to jump to same basic block currently");
            }
            TerminatorKind::Return { .. } | TerminatorKind::Unresolved => {}
        };
        
        bb.set_terminator(terminator);
        self.current
    }

    /// Terminates current bb with `terminator_builder` and creates a new one.
    /// 
    /// `terminator_builder` is called with the index of the new bb.
    /// 
    /// The index of the previous bb is returned.
    pub fn terminate_and(
        &mut self, basic_blocks: &mut BasicBlocks, fx: &mut Function, terminator_builder: impl FnOnce(BasicBlockIdx) -> TerminatorKind,
    ) -> BasicBlockIdx {
        let old_bb = self.current;
        let new_bb = self.new_bb(basic_blocks, fx);

        self.set_bb(old_bb);
        self.terminate(basic_blocks, terminator_builder(new_bb));
        self.set_bb(new_bb);
        old_bb
    }

    pub fn get_current_bb_mut<'ctx>(&mut self, basic_blocks: &'ctx mut BasicBlocks) -> &'ctx mut BasicBlock {
        basic_blocks.get_mut_or_panic(self.current)
    }
}

impl Function {
    pub fn predecessors(&self, basic_blocks: &BasicBlocks) -> Predecessors {
        let mut predecessors = Predecessors::new();
        for (idx, bb) in basic_blocks.indexed_iter_as_option().flatten() {
            if let Some(terminator) = bb.terminator.as_ref() {
                match &terminator.kind {
                    TerminatorKind::Goto(target) => {
                        predecessors.insert(*target, idx);
                    }
                    TerminatorKind::SwitchInt { targets, default, .. } => {
                        predecessors.insert(*default, idx);

                        for (_, target) in targets {
                            predecessors.insert(*target, idx);
                        }
                    }
                    TerminatorKind::Assert { default, .. } => {
                        predecessors.insert(*default, idx);
                    }
                    TerminatorKind::Return { .. } | TerminatorKind::Unresolved => {}
                }
            }
        }

        predecessors
    }

    pub fn successors(&self, basic_blocks: &BasicBlocks) -> Successors {
        let mut successors = Successors::new();
        for (idx, bb) in basic_blocks.indexed_iter_as_option().flatten() {
            if let Some(terminator) = bb.terminator.as_ref() {
                match &terminator.kind {
                    TerminatorKind::Goto(target) => {
                        successors.insert(idx, *target);
                    }
                    TerminatorKind::SwitchInt { targets, default, .. } => {
                        successors.insert(idx, *default);

                        for (_, target) in targets {
                            successors.insert(idx, *target);
                        }
                    }
                    TerminatorKind::Assert { default, .. } => {
                        successors.insert(idx, *default);
                    }
                    TerminatorKind::Return { .. } | TerminatorKind::Unresolved => {}
                }
            }
        }

        successors
    }
}

pub struct Predecessors(HashMap<BasicBlockIdx, Vec<BasicBlockIdx>>);

impl Predecessors {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn get(&self, bb: BasicBlockIdx) -> Option<&Vec<BasicBlockIdx>> {
        self.0.get(&bb)
    }

    pub fn insert(&mut self, bb: BasicBlockIdx, successor: BasicBlockIdx) {
        self.0.entry(bb).or_insert_with(|| Vec::with_capacity(1)).push(successor);
    }

    pub fn get_all(&self, bb: BasicBlockIdx) -> Vec<BasicBlockIdx> {
        let mut visited = HashSet::new();
        let mut queue = vec![bb];

        while let Some(bb) = queue.pop() {
            if visited.contains(&bb) {
                continue;
            }

            visited.insert(bb);
            if let Some(predecessors) = self.0.get(&bb) {
                queue.extend(predecessors.iter().copied());
            }
        }

        visited.remove(&bb);
        visited.into_iter().collect()
    }
}

pub struct Successors(HashMap<BasicBlockIdx, HashSet<BasicBlockIdx>>);

impl Successors {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn get(&self, bb: BasicBlockIdx) -> Option<&HashSet<BasicBlockIdx>> {
        self.0.get(&bb)
    }

    pub fn insert(&mut self, bb: BasicBlockIdx, sucessor: BasicBlockIdx) {
        self.0.entry(bb).or_insert_with(|| HashSet::with_capacity(1)).insert(sucessor);
    }

    pub fn get_all(&self, bb: BasicBlockIdx) -> HashSet<BasicBlockIdx> {
        let mut visited = HashSet::new();
        let mut queue = vec![bb];

        while let Some(bb) = queue.pop() {
            if visited.contains(&bb) {
                continue;
            }

            visited.insert(bb);
            if let Some(sucessors) = self.0.get(&bb) {
                queue.extend(sucessors.iter().copied());
            }
        }

        visited.remove(&bb);
        visited
    }
}

#[derive(Debug, Clone)]
pub struct Dominators(HashMap<BasicBlockIdx, BasicBlockIdx>);

impl Dominators {
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    #[inline]
    /// Returns all blocks dominated by the given basic block.
    pub fn get_dominated_bbs(&self, bb_idx: BasicBlockIdx) -> HashSet<BasicBlockIdx> {
        let mut unvisited_bbs = vec![bb_idx];
        let mut visited = HashSet::new();

        while let Some(bb_idx) = unvisited_bbs.pop() {
            if visited.contains(&bb_idx) {
                continue;
            }

            visited.insert(bb_idx);

            for (bb, idom) in self.0.iter() {
                if *idom == bb_idx {
                    unvisited_bbs.push(*bb);
                }
            }
        }

        visited
    }

    /// Returns `true` if `a` is dominated by `b`.
    pub fn dominates(&self, a: BasicBlockIdx, b: BasicBlockIdx) -> bool {
        self.get_dominated_bbs(b).contains(&a)
    }

    /// Similar to the method `dominates`, but with the additional restriction that `a != b`.
    pub fn strictly_dominates(&self, a: BasicBlockIdx, b: BasicBlockIdx) -> bool {
        a != b && self.dominates(a, b)
    }

    /// Fetches the immediate dominator for the queried basic block.
    pub fn get_idom(&self, bb: BasicBlockIdx) -> Option<BasicBlockIdx> {
        self.0.get(&bb).copied()
    }

    /// Returns all immediate dominators.
    /// 
    /// The entry block does not possess an immediate dominator.
    pub fn get_all_idoms(&self) -> &HashMap<BasicBlockIdx, BasicBlockIdx> {
        &self.0
    }

    /// Sets `idom` as the immediate dominator for basic block `bb`.
    pub fn set_idom(&mut self, bb: BasicBlockIdx, idom: BasicBlockIdx) {
        self.0.insert(bb, idom);
    }
}