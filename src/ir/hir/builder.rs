use std::{cell::Cell, collections::HashMap};

use snowflake_compiler::{bug_report, Idx};

use crate::{ast::{Ast, ExpressionId, ExpressionKind, ItemKind, StatementId, StatementKind}, compilation_unit::{FunctionIndex, GlobalScope, VariableIndex}, ir::hir::{AllocType, HIRContext, HIRExprKind, HIRExpression, HIRNodeId, HIRStatement, HIRStmtKind, ScopeId, HIR}, text::span::TextSpan, typings::Type};


struct Ctx {
    statements: Vec<HIRStatement>,
}

impl Ctx {
    fn new() -> Self {
        Self { statements: vec![] }
    }

    fn with_capacity(capacity: usize) -> Self {
        Self { statements: Vec::with_capacity(capacity) }
    }
}

pub struct HIRBuilder {
    hir: HIR,
    temp_var_count: Cell<usize>,
    context: HIRContext,
}

impl HIRBuilder {
    pub fn new() -> Self {
        Self {
            hir: HIR { 
                functions: HashMap::new(),
                source_map: HashMap::new(),
            },
            temp_var_count: Cell::new(0),
            context: HIRContext::new(),
        }
    }

    /// Method to get a new node ID
    fn next_node_id(&mut self) -> HIRNodeId {
        self.context.next_node_id()
    }

    /// Method to get a default span (you should replace this with actual span tracking)
    fn default_span(&self) -> TextSpan {
        TextSpan::new(0, 0, String::new())
    }

    /// Method to get a current or default scope
    fn current_scope_id(&self) -> ScopeId {
        self.context.current_scope
    }

    /// Method to create a HIRStatement with proper ID and span
    fn create_statement(&mut self, kind: HIRStmtKind) -> HIRStatement {
        let id = self.next_node_id();
        let span = self.default_span();
        HIRStatement { kind, id, span }
    }

    /// Method to create a HIRExpression with proper ID and span
    fn create_expression(&mut self, kind: HIRExprKind, ty: Type) -> HIRExpression {
        let id = self.next_node_id();
        let span = self.default_span();
        HIRExpression { kind, ty, id, span }
    }

    pub fn build(mut self, ast: &Ast, global_scope: &mut GlobalScope) -> HIR {
        for item in ast.items.iter() {
            match &item.kind {
                ItemKind::Statement(stmt_id) => {
                    // Handle top-level statements
                    // These could be global initializations, module-level expressions, etc.
                    let global_init_idx = FunctionIndex::new(0); // Use a reserved index for global init
                    
                    let mut temp_ctx = Ctx::new();
                    self.build_statement(*stmt_id, ast, global_scope, &mut temp_ctx, false);
                    
                    let ctx = self.hir.functions.entry(global_init_idx)
                        .or_insert_with(Vec::new);
                    ctx.extend(temp_ctx.statements);
                },
                ItemKind::Function(fx_decl) => {
                    let mut ctx = Ctx::new();
                    for stmt_id in fx_decl.body.iter() {
                        self.build_statement(*stmt_id, ast, global_scope, &mut ctx, false);
                    }
                    self.hir.functions.insert(fx_decl.index, ctx.statements);
                }
            }
        }

        self.hir
    }

    fn build_statement(&mut self, stmt_id: StatementId, ast: &Ast, global_scope: &mut GlobalScope, ctx: &mut Ctx, _temp_needed: bool) {
        let statement = ast.query_statement(stmt_id);
        let kind = match &statement.kind {
            StatementKind::Expression(expr) => {
                let expr = self.build_expression(*expr, ast, global_scope, ctx, false);
                HIRStmtKind::Expression { expr }
            }
            StatementKind::Let(let_statement) => {
                let expr = self.build_expression(let_statement.initialiser, ast, global_scope, ctx, true);
                HIRStmtKind::Declaration { var_idx: let_statement.variable_index, init: Some(expr) }
            }
            StatementKind::While(while_statement) => {
                let condition = self.build_expression(while_statement.condition, ast, global_scope, ctx, false);
                let mut body_ctx = Ctx::with_capacity(while_statement.body.len());

                for stmt_id in while_statement.body.iter() {
                    self.build_statement(*stmt_id, ast, global_scope, &mut body_ctx, false);
                }

                let break_expr = self.create_expression(HIRExprKind::Break, Type::Void);
                let break_stmt = self.create_statement(HIRStmtKind::Expression { expr: break_expr });
                let if_stmt = self.create_statement(HIRStmtKind::If {
                    condition,
                    then_block: body_ctx.statements,
                    else_block: vec![break_stmt],
                });

                HIRStmtKind::Loop { body: vec![if_stmt] }
            }
            StatementKind::Return(return_statement) => {
                let expr = return_statement.return_value.as_ref().copied()
                    .map(|expr_id| self.build_expression(expr_id, ast, global_scope, ctx, true))
                    .unwrap_or_else(|| self.create_expression(HIRExprKind::Unit, Type::Void));
                
                HIRStmtKind::Return { expr }
            }
        };

        ctx.statements.push(self.create_statement(kind));
    }

    fn build_expression(&mut self, expr_id: ExpressionId, ast: &Ast, global_scope: &mut GlobalScope, ctx: &mut Ctx, temp_needed: bool) -> HIRExpression {
        let expr = ast.query_expression(expr_id);
        let kind = match &expr.kind {
            ExpressionKind::Number(number_expr) => HIRExprKind::Number(number_expr.number),
            ExpressionKind::Usize(usize_expr) => HIRExprKind::Usize(usize_expr.number),
            ExpressionKind::String(string_expr) => HIRExprKind::String(string_expr.string.clone()),
            ExpressionKind::Boolean(bool_expr) => HIRExprKind::Bool(bool_expr.value),
            ExpressionKind::Binary(bin_expr) => {
                let left = self.build_expression(bin_expr.left, ast, global_scope, ctx, true);
                let right = self.build_expression(bin_expr.right, ast, global_scope, ctx, true);

                HIRExprKind::Binary {
                    operator: bin_expr.operator.kind.clone(),
                    left: Box::new(left),
                    right: Box::new(right)
                }
            },
            ExpressionKind::CompoundBinary(_) => bug_report!("CompoundBinary expressions should be desugared before HIR conversion"),
            ExpressionKind::Unary(un_expr) => {
                let operand = self.build_expression(un_expr.operand, ast, global_scope, ctx, true);

                HIRExprKind::Unary {
                    operator: un_expr.operator.kind.clone(),
                    operand: Box::new(operand)
                }
            },
            ExpressionKind::Parenthesised(paren_expr) => {
                self.build_expression(paren_expr.expression, ast, global_scope, ctx, temp_needed).kind
            },
            ExpressionKind::Variable(var_expr) => HIRExprKind::Var(var_expr.variable_index),
            ExpressionKind::Assignment(assign_expr) => {
                let expr = self.build_expression(assign_expr.expression, ast, global_scope, ctx, true);
                let statement = self.create_statement(HIRStmtKind::Assignment {
                    var_idx: assign_expr.variable_index,
                    expr,
                });

                ctx.statements.push(statement);

                if temp_needed {
                    HIRExprKind::Var(assign_expr.variable_index)
                } else {
                    HIRExprKind::Unit
                }
            },
            ExpressionKind::If(if_expr) => {
                let condition = self.build_expression(if_expr.condition, ast, global_scope, ctx, false);
                let mut then_ctx = Ctx::new();

                for stmt_id in &if_expr.then_branch.statements {
                    self.build_statement(*stmt_id, ast, global_scope, &mut then_ctx, false);
                }

                let mut else_ctx = Ctx::new();
                if let Some(else_branch) = &if_expr.else_branch {
                    for stmt_id in else_branch.body.iter() {
                        self.build_statement(*stmt_id, ast, global_scope, &mut else_ctx, false);
                    }
                }

                let expr_kind = if matches!(expr.ty, Type::Void) || !temp_needed {
                    HIRExprKind::Unit
                } else {
                    let then_expr = match then_ctx.statements.last_mut().unwrap().kind {
                        HIRStmtKind::Expression { ref mut expr } => expr.clone(),
                        _ => bug_report!("Last statement in then branch of if expression is not an expression"),
                    };

                    let else_expr = match else_ctx.statements.last_mut().unwrap().kind {
                        HIRStmtKind::Expression { ref mut expr } => expr.clone(),
                        _ => bug_report!("Last statement in else branch of if expression is not an expression"),
                    };

                    let temp_var_idx = self.declare_next_temp_var(global_scope, expr.ty.clone());
                    ctx.statements.push(self.create_statement(HIRStmtKind::Declaration { 
                        var_idx: temp_var_idx, 
                        init: None 
                    }));
                    
                    *then_ctx.statements.last_mut().unwrap() = self.create_statement(HIRStmtKind::Assignment { 
                        var_idx: temp_var_idx, 
                        expr: then_expr 
                    });
                    *else_ctx.statements.last_mut().unwrap() = self.create_statement(HIRStmtKind::Assignment { 
                        var_idx: temp_var_idx, 
                        expr: else_expr 
                    });

                    HIRExprKind::Var(temp_var_idx)
                };

                ctx.statements.push(self.create_statement(HIRStmtKind::If {
                    condition,
                    then_block: then_ctx.statements,
                    else_block: else_ctx.statements
                }));

                expr_kind
            },
            ExpressionKind::Block(block_expr) => {
                let mut block_ctx = Ctx::new();

                for stmt_id in block_expr.statements.iter() {
                    self.build_statement(*stmt_id, ast, global_scope, &mut block_ctx, false);
                }

                let expr_kind = if matches!(expr.ty, Type::Void) || !temp_needed {
                    HIRExprKind::Unit
                } else {
                    let last_stmt = block_ctx.statements.last_mut().unwrap();
                    let _expr = match &last_stmt.kind {
                        HIRStmtKind::Expression { expr } => expr.clone(),
                        _ => bug_report!("Last statement in block expression is not an expression")
                    };

                    if let HIRStmtKind::Expression { expr } = &last_stmt.kind {
                        let temp_var_idx = self.declare_next_temp_var(global_scope, expr.ty.clone());
                        ctx.statements.push(self.create_statement(HIRStmtKind::Declaration { 
                            var_idx: temp_var_idx, 
                            init: None 
                        }));

                        *last_stmt = self.create_statement(HIRStmtKind::Assignment { 
                            var_idx: temp_var_idx, 
                            expr: expr.clone() 
                        });

                        HIRExprKind::Var(temp_var_idx)
                    } else {
                        HIRExprKind::Unit
                    }
                };

                // For now, use a default scope_id - this should be properly managed
                let scope_id = self.current_scope_id();
                ctx.statements.push(self.create_statement(HIRStmtKind::Block { 
                    body: block_ctx.statements,
                    scope_id,
                }));

                expr_kind
            },
            ExpressionKind::Call(call_expr) => {
                let args = call_expr.arguments.iter()
                    .map(|expr_id| self.build_expression(*expr_id, ast, global_scope, ctx, true))
                    .collect();


                HIRExprKind::Call { fx_idx: call_expr.fx_idx, args: args }
            },
            ExpressionKind::Break(_) => HIRExprKind::Break,
            ExpressionKind::Continue(_) => HIRExprKind::Continue,
            ExpressionKind::Array(array_expr) => {
                let elements = array_expr.elements.iter()
                    .map(|elem_id| self.build_expression(*elem_id, ast, global_scope, ctx, true))
                    .collect::<Vec<_>>();

                // Get element type from the first element or default to Void for empty arrays
                let element_type = if let Some(first_elem) = elements.first() {
                    first_elem.ty.clone()
                } else {
                    let ty = Type::from_str(&array_expr.type_decl.span.literal);
                    match ty {
                        None => bug_report!("Array type declaration is missing or invalid"),
                        Some(ty) => ty
                    }
                };

                HIRExprKind::Array {
                    elements,
                    element_type,
                    alloc_type: AllocType::Stack, // Stack alloc for static arrays
                }
            },
            ExpressionKind::IndexExpression(index_expr) => {
                let object = self.build_expression(index_expr.object, ast, global_scope, ctx, true);
                let index = self.build_expression(index_expr.index, ast, global_scope, ctx, true);

                HIRExprKind::Index {
                    object: Box::new(object),
                    index: Box::new(index),
                    bounds_check: true, // Done as a default
                }
            },
            ExpressionKind::Error(_) => bug_report!("Error expression in HIR builder"),
        };

        self.create_expression(kind, expr.ty.clone())
    }

    fn declare_next_temp_var(&self, global_scope: &mut GlobalScope, ty: Type) -> VariableIndex {
        global_scope.declare_variable(&self.next_temp_var(), ty, false, false)
    }

    fn next_temp_var(&self) -> String {
        let temp_var_idx = self.temp_var_count.get();
        self.temp_var_count.set(temp_var_idx + 1);

        format!("%{}", temp_var_idx)
    }
}