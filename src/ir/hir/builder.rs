use std::{cell::Cell, collections::HashMap};

use snowflake_compiler::{bug_report, Idx};

use crate::{ast::{Ast, ExpressionId, ExpressionKind, ItemKind, StatementId, StatementKind}, compilation_unit::{FunctionIndex, GlobalScope, VariableIndex}, ir::hir::{HIRExprKind, HIRExpression, HIRStatement, HIRStmtKind, HIR}, typings::Type};


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
}

impl HIRBuilder {
    pub fn new() -> Self {
        Self {
            hir: HIR { functions: HashMap::new() },
            temp_var_count: Cell::new(0)
        }
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

    fn build_statement(&self, stmt_id: StatementId, ast: &Ast, global_scope: &mut GlobalScope, ctx: &mut Ctx, _temp_needed: bool) {
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

                let body = vec![
                    HIRStatement {
                        kind: HIRStmtKind::If {
                            condition,
                            then_block: body_ctx.statements,
                            else_block: vec![HIRStatement {
                                kind: HIRStmtKind::Expression {
                                    expr: HIRExpression {
                                        kind: HIRExprKind::Break,
                                        ty: Type::Void
                                    }
                                }
                            }],
                        }
                    }
                ];

                HIRStmtKind::Loop { body }
            }
            StatementKind::Return(return_statement) => {
                let expr = return_statement.return_value.as_ref().copied()
                    .map(|expr_id| self.build_expression(expr_id, ast, global_scope, ctx, true))
                    .unwrap_or(HIRExpression {
                        kind: HIRExprKind::Unit,
                        ty: Type::Void,
                    });
                
                HIRStmtKind::Return { expr }
            }
        };

        ctx.statements.push(HIRStatement { kind });
    }

    fn build_expression(&self, expr_id: ExpressionId, ast: &Ast, global_scope: &mut GlobalScope, ctx: &mut Ctx, temp_needed: bool) -> HIRExpression {
        let expr = ast.query_expression(expr_id);
        let kind = match &expr.kind {
            ExpressionKind::Number(number_expr) => HIRExprKind::Number(number_expr.number),
            ExpressionKind::String(string_expr) => HIRExprKind::String(string_expr.value.clone()),
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
                let statement = HIRStatement {
                    kind: HIRStmtKind::Assignment {
                        var_idx: assign_expr.variable_index,
                        expr: self.build_expression(assign_expr.expression, ast, global_scope, ctx, true),
                    }
                };

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
                    ctx.statements.push(HIRStatement {
                        kind: HIRStmtKind::Declaration { var_idx: temp_var_idx, init: None }
                    });
                    
                    *then_ctx.statements.last_mut().unwrap() = HIRStatement {
                        kind: HIRStmtKind::Assignment { var_idx: temp_var_idx, expr: then_expr }
                    };
                    *else_ctx.statements.last_mut().unwrap() = HIRStatement {
                        kind: HIRStmtKind::Assignment { var_idx: temp_var_idx, expr: else_expr }
                    };

                    HIRExprKind::Var(temp_var_idx)
                };

                ctx.statements.push(HIRStatement {
                    kind: HIRStmtKind::If {
                        condition,
                        then_block: then_ctx.statements,
                        else_block: else_ctx.statements
                    }
                });

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
                        ctx.statements.push(HIRStatement {
                            kind: HIRStmtKind::Declaration { var_idx: temp_var_idx, init: None },
                        });

                        *last_stmt = HIRStatement {
                            kind: HIRStmtKind::Assignment { var_idx: temp_var_idx, expr: expr.clone() },
                        };

                        HIRExprKind::Var(temp_var_idx)
                    } else {
                        HIRExprKind::Unit
                    }
                };

                ctx.statements.push(HIRStatement {
                    kind: HIRStmtKind::Block { body: block_ctx.statements }
                });

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
            ExpressionKind::Error(_) => bug_report!("Error expression in HIR builder"),
        };

        HIRExpression { kind: kind, ty: expr.ty.clone() }
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