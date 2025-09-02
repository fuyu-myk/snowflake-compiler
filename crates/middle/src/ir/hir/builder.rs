use std::{cell::Cell, collections::HashMap};

use snowflake_common::{bug_report, diagnostics::DiagnosticsReportCell, typings::ObjectKind, Idx};
use snowflake_front::{
    ast::{Ast, ExprIndex, ExpressionKind, ItemIndex, ItemKind, StatementKind, StmtIndex, StructRest},
    compilation_unit::{GlobalScope, VariableIndex}
};
use snowflake_common::{text::span::TextSpan, typings::Type};

use crate::ir::hir::{AllocType, HIRContext, HIRExprField, HIRExprKind, HIRExpression, HIRItemId, HIRNodeId, HIRStatement, HIRStmtKind, HIRStructTailExpr, ScopeId, HIR};


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
    diagnostics: DiagnosticsReportCell,
}

impl HIRBuilder {
    pub fn new(diagnostics: DiagnosticsReportCell) -> Self {
        Self {
            hir: HIR { 
                functions: HashMap::new(),
                top_statements: HashMap::new(),
                source_map: HashMap::new(),
            },
            temp_var_count: Cell::new(0),
            context: HIRContext::new(),
            diagnostics,
        }
    }

    /// Method to get a new node ID
    fn next_node_id(&mut self) -> HIRNodeId {
        self.context.next_node_id()
    }

    /// Method to get a current or default scope
    fn current_scope_id(&self) -> ScopeId {
        self.context.current_scope
    }

    /// Method to create a HIRStatement with proper ID and span
    fn create_statement(&mut self, kind: HIRStmtKind, span: TextSpan) -> HIRStatement {
        let id = self.next_node_id();
        self.hir.source_map.insert(id, span.clone());
        HIRStatement { kind, id, span }
    }

    /// Method to create a HIRExpression with proper ID and span
    fn create_expression(&mut self, kind: HIRExprKind, ty: Type, span: TextSpan) -> HIRExpression {
        let id = self.next_node_id();
        self.hir.source_map.insert(id, span.clone());
        HIRExpression { kind, ty, id, span }
    }

    pub fn build(mut self, ast: &Ast, global_scope: &mut GlobalScope) -> HIR {
        for item in ast.items.iter() {
            if item.is_local {
                continue;
            }
            
            match &item.kind {
                ItemKind::Function(fx_decl) => {
                    let mut ctx = Ctx::new();
                    for stmt_id in fx_decl.body.iter() {
                        self.build_statement(*stmt_id, ast, global_scope, &mut ctx, false);
                    }
                    self.hir.functions.insert(fx_decl.index, ctx.statements);
                }
                ItemKind::Const(const_decl) => {
                    let global_init_idx = ItemIndex::new(0);

                    let mut temp_ctx = Ctx::new();
                    let init_expr = if let Some(ref expr) = const_decl.expr {
                        Some(self.build_expression(**expr, ast, global_scope, &mut temp_ctx, true))
                    } else {
                        None
                    };

                    let const_name = &const_decl.identifier.span.literal;
                    let var_idx = global_scope.lookup_global_variable_by_name(const_name)
                        .expect("Const variable should be declared during resolution phase");

                    let const_stmt = HIRStatement {
                        kind: HIRStmtKind::Const {
                            var_idx,
                            init_expr,
                        },
                        id: self.next_node_id(),
                        span: const_decl.identifier.span.clone(),
                    };

                    let ctx = self.hir.top_statements.entry(global_init_idx)
                        .or_insert_with(Vec::new);
                    ctx.extend(temp_ctx.statements);
                    ctx.push(const_stmt);
                }
                ItemKind::Struct(name, generics, _) => {
                    let struct_name = &name.span.literal;
                    let struct_idx = global_scope.lookup_struct(struct_name)
                        .expect("Struct should be declared during resolution phase");
                    let span = TextSpan::combine_two(&name.span, &generics.span);

                    let struct_stmt = HIRStatement {
                        kind: HIRStmtKind::Item { item_id: HIRItemId { from: struct_idx } },
                        id: self.next_node_id(),
                        span,
                    };

                    self.hir.top_statements.insert(struct_idx, vec![struct_stmt]);
                }
            }
        }

        self.hir
    }

    fn build_statement(&mut self, stmt_id: StmtIndex, ast: &Ast, global_scope: &mut GlobalScope, ctx: &mut Ctx, _temp_needed: bool) {
        let statement = ast.query_statement(stmt_id);
        let span = statement.span.clone();
        let kind = match &statement.kind {
            StatementKind::Expression(expr) => {
                let expr = self.build_expression(*expr, ast, global_scope, ctx, false);
                HIRStmtKind::Expression { expr }
            }
            StatementKind::Let(let_statement) => {
                let expr = self.build_expression(let_statement.initialiser, ast, global_scope, ctx, true);
                
                // Extract mutability from the pattern
                let is_mutable = match &let_statement.pattern.kind {
                    snowflake_front::ast::PatternKind::Identifier(binding_mode, _) => {
                        matches!(binding_mode.0, snowflake_front::ast::Mutability::Mutable)
                    }
                    _ => false // Other patterns default to immutable for now
                };
                
                HIRStmtKind::Declaration { 
                    var_idx: let_statement.variable_index, 
                    init_expr: Some(expr),
                    is_mutable 
                }
            }
            StatementKind::While(while_statement) => {
                let condition = self.build_expression(while_statement.condition, ast, global_scope, ctx, false);
                let mut body_ctx = Ctx::with_capacity(while_statement.body.len());

                for stmt_id in while_statement.body.iter() {
                    self.build_statement(*stmt_id, ast, global_scope, &mut body_ctx, false);
                }

                let while_span = TextSpan::combine_refs(&[&while_statement.while_keyword.span, &condition.span]);
                let break_expr = self.create_expression(HIRExprKind::Break, Type::Void, while_span.clone());
                let break_stmt = self.create_statement(HIRStmtKind::Expression { expr: break_expr }, while_span.clone());
                let if_stmt = self.create_statement(HIRStmtKind::If {
                    condition,
                    then_block: body_ctx.statements,
                    else_block: vec![break_stmt],
                }, while_span);

                HIRStmtKind::Loop { body: vec![if_stmt] }
            }
            StatementKind::Const(const_statement) => {
                let expr = self.build_expression(const_statement.expr, ast, global_scope, ctx, true);
                
                HIRStmtKind::Const { 
                    var_idx: const_statement.variable_index, 
                    init_expr: Some(expr),
                }
            }
            StatementKind::Return(return_statement) => {
                let expr = return_statement.return_value.as_ref().copied()
                    .map(|expr_id| self.build_expression(expr_id, ast, global_scope, ctx, true))
                    .unwrap_or_else(|| {
                        match return_statement.return_value {
                            Some(value) => self.create_expression(HIRExprKind::Unit, Type::Void, ast.query_expression(value).span.clone()),
                            None => self.create_expression(HIRExprKind::Unit, Type::Void, return_statement.return_keyword.span.clone()),
                        }
                    });

                HIRStmtKind::Return { expr }
            }
            StatementKind::Item(item_id) => {
                let ast_item = ast.query_item(*item_id);

                match &ast_item.kind {
                    ItemKind::Struct(_, _, _) => {
                        HIRStmtKind::Item { item_id: HIRItemId { from: *item_id } }
                    }
                    ItemKind::Function(_) => {
                        // Placeholder
                        HIRStmtKind::Expression { 
                            expr: self.create_expression(HIRExprKind::Unit, Type::Void, ast_item.span.clone()) 
                        }
                    }
                    ItemKind::Const(_) => {
                        HIRStmtKind::Item { item_id: HIRItemId { from: *item_id } }
                    }
                }
            }
        };

        ctx.statements.push(self.create_statement(kind, span));
    }

    fn build_expression(&mut self, expr_id: ExprIndex, ast: &Ast, global_scope: &mut GlobalScope, ctx: &mut Ctx, temp_needed: bool) -> HIRExpression {
        let expr = ast.query_expression(expr_id);
        let kind = match &expr.kind {
            ExpressionKind::Number(number_expr) => HIRExprKind::Number(number_expr.number),
            ExpressionKind::Float(float_expr) => HIRExprKind::Float(float_expr.number),
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
            ExpressionKind::Variable(var_expr) => HIRExprKind::Var { var_idx: var_expr.variable_index },
            ExpressionKind::Assignment(assign_expr) => {
                let value_expr = self.build_expression(assign_expr.expression, ast, global_scope, ctx, true);
                let target_expr = self.build_expression(assign_expr.lhs, ast, global_scope, ctx, true);
                
                let span = value_expr.span.clone();
                let value_kind = value_expr.kind.clone();
                let statement = self.create_statement(HIRStmtKind::Assignment {
                    target: target_expr,
                    value: value_expr,
                }, span);

                ctx.statements.push(statement);

                if temp_needed {
                    value_kind
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
                    let temp_span = expr.span.clone();
                    
                    let temp_target_then = self.create_expression(
                        HIRExprKind::Var { var_idx: temp_var_idx },
                        then_expr.ty.clone(),
                        temp_span.clone()
                    );
                    let temp_target_else = self.create_expression(
                        HIRExprKind::Var { var_idx: temp_var_idx },
                        else_expr.ty.clone(),
                        temp_span.clone()
                    );
                    
                    *then_ctx.statements.last_mut().unwrap() = self.create_statement(HIRStmtKind::Assignment { 
                        target: temp_target_then, 
                        value: then_expr
                    }, temp_span.clone());
                    *else_ctx.statements.last_mut().unwrap() = self.create_statement(HIRStmtKind::Assignment { 
                        target: temp_target_else, 
                        value: else_expr 
                    }, temp_span);

                    HIRExprKind::Var { var_idx: temp_var_idx }
                };

                ctx.statements.push(self.create_statement(HIRStmtKind::If {
                    condition,
                    then_block: then_ctx.statements,
                    else_block: else_ctx.statements,
                }, expr.span.clone()));

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
                        let temp_span = expr.span.clone();
                        ctx.statements.push(self.create_statement(HIRStmtKind::Declaration { 
                            var_idx: temp_var_idx, 
                            init_expr: None,
                            is_mutable: false
                        }, temp_span.clone()));

                        let temp_target = self.create_expression(
                            HIRExprKind::Var { var_idx: temp_var_idx },
                            expr.ty.clone(),
                            temp_span.clone()
                        );

                        *last_stmt = self.create_statement(HIRStmtKind::Assignment { 
                            target: temp_target, 
                            value: expr.clone() 
                        }, temp_span);

                        HIRExprKind::Var { var_idx: temp_var_idx }
                    } else {
                        HIRExprKind::Unit
                    }
                };

                // For now, use a default scope_id
                let scope_id = self.current_scope_id();
                ctx.statements.push(self.create_statement(HIRStmtKind::Block { 
                    body: block_ctx.statements,
                    scope_id,
                }, expr.span.clone()));

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

                let element_type = if let Some(first_elem) = elements.first() {
                    first_elem.ty.clone()
                } else {
                    Type::from_token(&array_expr.type_decl)
                };

                HIRExprKind::Array {
                    elements,
                    element_type,
                    alloc_type: AllocType::Stack, // Stack alloc for static arrays
                }
            },
            ExpressionKind::IndexExpression(index_expr) => {
                let mut object = self.build_expression(index_expr.object, ast, global_scope, ctx, true);
                
                let index = self.build_expression(index_expr.index.idx_no, ast, global_scope, ctx, true);
                
                // Get the length from the current object type (not the object kind)
                let len = match &object.ty {
                    Type::Array(_, len) => *len,
                    _ => bug_report!("Indexing non-array type"),
                };

                // Get the element type from the current object type
                let element_type = match &object.ty {
                    Type::Array(element_type, _) => *element_type.clone(),
                    _ => Type::Error,
                };

                let span_clone = expr.span.clone();
                let length_expr = self.create_expression(HIRExprKind::Usize(len), Type::Usize, span_clone);

                // Create a new index operation for each dimension
                object = self.create_expression(
                    HIRExprKind::Index {
                        object: Box::new(object),
                        index: Box::new(index),
                        bounds_check: true, // Done as a default
                        length: Box::new(length_expr),
                    },
                    element_type,
                    expr.span.clone()
                );

                return object;
            },
            ExpressionKind::Tuple(tuple_expr) => {
                let elements = tuple_expr.elements.iter()
                    .map(|elem_id| self.build_expression(*elem_id, ast, global_scope, ctx, true))
                    .collect::<Vec<_>>();
                let mut element_types = vec![];

                for element in &elements {
                    let element_type = element.ty.clone();
                    element_types.push(Box::new(element_type));
                }

                HIRExprKind::Tuple {
                    elements,
                    element_types,
                }
            },
            ExpressionKind::FieldExpression(tuple_index_expr) => {
                let mut object = self.build_expression(tuple_index_expr.object, ast, global_scope, ctx, true);
                let mut field = self.build_expression(tuple_index_expr.field.idx_no, ast, global_scope, ctx, true);

                let element_type = match &object.ty {
                    Type::Object(object_type) => {
                        match &object_type.kind {
                            ObjectKind::Tuple => {
                                let idx = match &field.kind {
                                    HIRExprKind::Usize(n) => *n,
                                    HIRExprKind::Number(n) => {
                                        if *n < 0 {
                                            bug_report!("Tuple index cannot be negative");
                                        }
                                        *n as usize
                                    },
                                    _ => bug_report!("Tuple index is not a constant usize or number"),
                                };
                                if idx >= object_type.fields.len() {
                                    Type::Error
                                } else {
                                    object_type.fields[idx].ty.as_ref().clone()
                                }
                            },
                            ObjectKind::Struct(_struct_idx) => {
                                let field_ast_expr = ast.query_expression(tuple_index_expr.field.idx_no);
                                let field_name = match &field_ast_expr.kind {
                                    ExpressionKind::Variable(var_expr) => {
                                        var_expr.identifier.span.literal.clone()
                                    }
                                    _ => {
                                        bug_report!("Expected variable expression for struct field name, got {:?}", field_ast_expr.kind);
                                    }
                                };

                                if let Some((field_index, field_def)) = object_type.fields.iter().enumerate().find(|(_, f)| {
                                    if let Some(name) = &f.name {
                                        name == &field_name
                                    } else {
                                        false
                                    }
                                }) {
                                    // Convert the field name to a constant index
                                    field = self.create_expression(
                                        HIRExprKind::Usize(field_index),
                                        Type::Usize,
                                        field_ast_expr.span.clone()
                                    );
                                    field_def.ty.as_ref().clone()
                                } else {
                                    Type::Error
                                }
                            }
                        }
                    },
                    _ => {
                        Type::Error
                    },
                };

                // Create a new field access operation
                object = self.create_expression(
                    HIRExprKind::Field {
                        object: Box::new(object),
                        field: Box::new(field),
                    },
                    element_type,
                    expr.span.clone()
                );

                return object;
            },
            ExpressionKind::Struct(struct_expr) => {
                HIRExprKind::Struct {
                    fields: struct_expr.fields.iter().map(|field| {
                        let field_expr = self.build_expression(field.expr.id, ast, global_scope, ctx, true);
                        HIRExprField {
                            identifier: field.identifier.clone(),
                            expr: field_expr,
                            is_shorthand: field.is_shorthand,
                        }
                    }).collect(),
                    tail_expr: match &struct_expr.rest {
                        StructRest::None => HIRStructTailExpr::None,
                        StructRest::Rest(span) => HIRStructTailExpr::Default(span.clone()),
                    },
                }
            },
            ExpressionKind::Error(_) => bug_report!("Error expression in HIR builder"),
        };

        self.create_expression(kind, expr.ty.clone(), expr.span.clone())
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