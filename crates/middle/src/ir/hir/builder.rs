use std::{cell::Cell, collections::HashMap};

use snowflake_common::{bug_report, diagnostics::DiagnosticsReportCell, token::{Token, TokenKind}, typings::ObjectKind, Idx};
use snowflake_front::{
    ast::{Ast, ExprIndex, ExpressionKind, ItemIndex, ItemKind, Path, PathSegment, Pattern, PatternKind, StatementKind, StmtIndex, StructRest, VariantData},
    compilation_unit::{GlobalScope, VariableIndex}
};
use snowflake_common::{text::span::TextSpan, typings::TypeKind};

use crate::ir::hir::{AllocType, Block, HIRContext, HIRExprField, HIRExprKind, HIRExpression, HIRItemId, HIRNodeId, HIRStatement, HIRStmtKind, HIRStructTailExpr, QualifiedPath, ScopeId, HIR};


struct Ctx {
    statements: Vec<HIRStatement>,
    current_fx_idx: Option<ItemIndex>,
}

impl Ctx {
    fn new() -> Self {
        Self { statements: vec![], current_fx_idx: None }
    }

    fn with_capacity(capacity: usize) -> Self {
        Self { statements: Vec::with_capacity(capacity), current_fx_idx: None }
    }
    
    fn with_function(current_fx_idx: ItemIndex) -> Self {
        Self { statements: vec![], current_fx_idx: Some(current_fx_idx) }
    }
    
    /// Create a new context with the same function context as the parent
    fn new_child(&self) -> Self {
        Self { statements: vec![], current_fx_idx: self.current_fx_idx }
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
    fn create_expression(&mut self, kind: HIRExprKind, ty: TypeKind, span: TextSpan) -> HIRExpression {
        let id = self.next_node_id();
        self.hir.source_map.insert(id, span.clone());
        HIRExpression { kind, ty, id, span }
    }

    fn path_from_pattern_identifier(&self, pattern: &Pattern) -> Path {
        match &pattern.kind {
            PatternKind::Identifier(_, token) => {
                Path {
                    span: token.span.clone(),
                    segments: vec![PathSegment {
                        identifier: token.clone(),
                        arguments: None,
                    }],
                    tokens: vec![token.clone()],
                }
            }
            _ => todo!("Unsupported pattern kind {:?} for path extraction", pattern.kind),
        }
    }
    
    /// Look up a struct by name, checks local scope first if in a function
    fn lookup_struct_with_context(&self, struct_name: &str, global_scope: &GlobalScope, ctx: &Ctx) -> Option<ItemIndex> {
        if let Some(fx_idx) = ctx.current_fx_idx {
            let function = global_scope.functions.get(fx_idx);
            let scoped_name = format!("{}::{}", function.name, struct_name);
            if let Some(struct_idx) = global_scope.lookup_struct(&scoped_name) {
                return Some(struct_idx);
            }
        }
        
        global_scope.lookup_struct(struct_name)
    }

    pub fn build(mut self, ast: &Ast, global_scope: &mut GlobalScope) -> HIR {
        for item in ast.items.iter() {
            if item.is_local {
                continue;
            }
            
            match &item.kind {
                ItemKind::Function(fx_decl) => {
                    let mut ctx = Ctx::with_function(fx_decl.index);
                    let statement_count = fx_decl.body.statements.len();
                    for (idx, stmt_id) in fx_decl.body.statements.iter().enumerate() {
                        let is_last = idx == statement_count - 1;
                        self.build_statement(*stmt_id, ast, global_scope, &mut ctx, false, is_last);
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

                    let const_name = self.path_from_pattern_identifier(&const_decl.identifier);
                    let var_idx = global_scope.lookup_global_variable_by_path(&const_name)
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

                    self.hir.top_statements.entry(struct_idx)
                        .or_insert_with(Vec::new)
                        .push(struct_stmt);
                }
                ItemKind::Impl(impl_item) => {
                    let type_name = match &*impl_item.self_type {
                        snowflake_front::ast::AstType::Simple { type_name } => {
                            type_name.span.literal.clone()
                        }
                        snowflake_front::ast::AstType::Path(_, path) => {
                            path.segments.last().unwrap().identifier.span.literal.clone()
                        }
                        _ => continue, // Skip complex types
                    };
                    
                    for assoc_item in &impl_item.items {
                        if let snowflake_front::ast::AssociatedItemKind::Function(fx_decl) = &assoc_item.kind {
                            let method_name = fx_decl.identifier.span.literal.clone();
                            
                            // Look up the actual function by path
                            let path = format!("{}::{}", type_name, method_name);
                            let fx_idx = global_scope.functions.indexed_iter()
                                .find(|(_, fx)| fx.name == path)
                                .map(|(idx, _)| idx);
                            
                            if let Some(fx_idx) = fx_idx {
                                let mut ctx = Ctx::with_function(fx_idx);
                                let statement_count = fx_decl.body.statements.len();
                                for (idx, stmt_id) in fx_decl.body.statements.iter().enumerate() {
                                    let is_last = idx == statement_count - 1;
                                    self.build_statement(*stmt_id, ast, global_scope, &mut ctx, false, is_last);
                                }
                                self.hir.functions.insert(fx_idx, ctx.statements);
                            }
                        }
                    }
                }
                ItemKind::Enum(name, generics, _) => {
                    let enum_name = &name.span.literal;
                    let enum_idx = global_scope.lookup_enum(enum_name)
                        .expect("Enum should be declared during resolution phase");
                    let span = TextSpan::combine_two(&name.span, &generics.span);

                    let enum_stmt = HIRStatement {
                        kind: HIRStmtKind::Item { item_id: HIRItemId { from: enum_idx } },
                        id: self.next_node_id(),
                        span,
                    };

                    self.hir.top_statements.entry(enum_idx)
                        .or_insert_with(Vec::new)
                        .push(enum_stmt);
                }
            }
        }

        self.hir
    }

    fn build_statement(&mut self, stmt_id: StmtIndex, ast: &Ast, global_scope: &mut GlobalScope, ctx: &mut Ctx, _temp_needed: bool, is_last: bool) {
        let statement = ast.query_statement(stmt_id);
        let span = statement.span.clone();
        let kind = match &statement.kind {
            StatementKind::SemiExpression(expr) => {
                let expr = self.build_expression(*expr, ast, global_scope, ctx, false);
                HIRStmtKind::Expression { expr }
            }
            StatementKind::Expression(expr) => {
                let expr = self.build_expression(*expr, ast, global_scope, ctx, false);
                // Only treat as tail expression if it's the last statement
                if is_last {
                    HIRStmtKind::TailExpression { expr }
                } else {
                    HIRStmtKind::Expression { expr }
                }
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
            StatementKind::Const(const_statement) => {
                let expr = self.build_expression(const_statement.expr, ast, global_scope, ctx, true);
                
                HIRStmtKind::Const { 
                    var_idx: const_statement.variable_index, 
                    init_expr: Some(expr),
                }
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
                            expr: self.create_expression(HIRExprKind::Unit, TypeKind::Void, ast_item.span.clone()) 
                        }
                    }
                    ItemKind::Const(_) => {
                        HIRStmtKind::Item { item_id: HIRItemId { from: *item_id } }
                    }
                    ItemKind::Impl(_) => {
                        // Placeholder for impl blocks
                        HIRStmtKind::Item { item_id: HIRItemId { from: *item_id } }
                    }
                    ItemKind::Enum(..) => {
                        todo!("Enum items not yet supported in HIR")
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
                let mut then_ctx = ctx.new_child();

                let then_count = if_expr.then_branch.statements.len();
                for (idx, stmt_id) in if_expr.then_branch.statements.iter().enumerate() {
                    let is_last = idx == then_count - 1;
                    self.build_statement(*stmt_id, ast, global_scope, &mut then_ctx, false, is_last);
                }

                let mut else_ctx = ctx.new_child();
                if let Some(else_branch) = &if_expr.else_branch {
                    let else_count = else_branch.body.statements.len();
                    for (idx, stmt_id) in else_branch.body.statements.iter().enumerate() {
                        let is_last = idx == else_count - 1;
                        self.build_statement(*stmt_id, ast, global_scope, &mut else_ctx, false, is_last);
                    }
                }
                let current_scope = self.current_scope_id();
                let then_block = HIRExprKind::Block {
                    body: Box::new(Block {
                        statements: then_ctx.statements.into_iter().map(Box::new).collect(),
                        span: expr.span.clone(),
                    }),
                    scope_id: current_scope,
                };
                let else_block = if !else_ctx.statements.is_empty() {
                    Some(HIRExprKind::Block {
                        body: Box::new(Block {
                            statements: else_ctx.statements.into_iter().map(Box::new).collect(),
                            span: expr.span.clone(),
                        }),
                        scope_id: current_scope,
                    })
                } else {
                    None
                };
                let then_expr = self.create_expression(then_block, expr.ty.clone(), expr.span.clone());
                let else_expr = else_block.map(|eb| self.create_expression(eb, expr.ty.clone(), expr.span.clone()));
                HIRExprKind::If {
                    condition: Box::new(condition),
                    then_block: Box::new(then_expr),
                    else_block: else_expr.map(Box::new),
                }
            },
            ExpressionKind::Block(block_expr) => {
                let mut block_ctx = ctx.new_child();
                let block_count = block_expr.statements.len();
                for (idx, stmt_id) in block_expr.statements.iter().enumerate() {
                    let is_last = idx == block_count - 1;
                    self.build_statement(*stmt_id, ast, global_scope, &mut block_ctx, false, is_last);
                }
                let block_expr = HIRExprKind::Block {
                    body: Box::new(crate::ir::hir::Block {
                        statements: block_ctx.statements.into_iter().map(Box::new).collect(),
                        span: expr.span.clone(),
                    }),
                    scope_id: self.current_scope_id(),
                };
                block_expr
            },
            ExpressionKind::Call(call_expr) => {
                let args: Vec<HIRExpression> = call_expr.arguments.iter()
                    .map(|expr_id| self.build_expression(*expr_id, ast, global_scope, ctx, true))
                    .collect();

                // Check if this is a tuple struct/enum variant constructor or a function call
                if call_expr.idx_ref == ItemIndex::unreachable() && (matches!(expr.ty, TypeKind::Object(_)) || matches!(expr.ty, TypeKind::Enum { .. })) {
                    // Tuple struct or enum variant constructor
                    let path_len = call_expr.callee.segments.len();
                    let variant_name = call_expr.callee.segments.last().unwrap().identifier.span.literal.clone();
                    
                    // Try struct first, then enum variant
                    let item_result = if let Some(struct_idx) = global_scope.lookup_struct(&variant_name) {
                        Some((struct_idx, None)) // (index, variant_discriminant)
                    } else if path_len >= 2 {
                        // Check for enum variant
                        let enum_name = &call_expr.callee.segments[path_len - 2].identifier.span.literal;
                        if let Some((enum_idx, variant)) = global_scope.lookup_enum_variant(enum_name, &variant_name) {
                            Some((enum_idx, Some(variant.discriminant)))
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    
                    let (item_idx, variant_discriminant) = item_result
                        .expect("Tuple struct/enum variant should be resolved during semantic analysis");
                    
                    let item = if variant_discriminant.is_some() {
                        let enum_info = global_scope.enums.get(item_idx);
                        ast.query_item(enum_info.id)
                    } else {
                        global_scope.structs.get(item_idx)
                    };

                    let field_spans = match &item.kind {
                        ItemKind::Struct(_, _, struct_def) => {
                            match struct_def {
                                VariantData::Tuple(fields) => {
                                    fields.iter().map(|f| {
                                        if f.identifier.is_some() {
                                            f.identifier.as_ref().unwrap().span.clone()
                                        } else {
                                            TextSpan::default()
                                        }
                                    }).collect::<Vec<_>>()
                                }
                                _ => bug_report!("Expected tuple struct definition for tuple struct constructor"),
                            }
                        }
                        ItemKind::Enum(_, _, enum_def) => {
                            let variant = enum_def.variants.iter()
                                .find(|v| v.identifier.span.literal == variant_name)
                                .expect("Enum variant should exist");
                            
                            match &variant.data {
                                VariantData::Tuple(fields) => {
                                    fields.iter().map(|f| {
                                        if f.identifier.is_some() {
                                            f.identifier.as_ref().unwrap().span.clone()
                                        } else {
                                            TextSpan::default()
                                        }
                                    }).collect::<Vec<_>>()
                                }
                                _ => bug_report!("Expected tuple variant for enum variant constructor"),
                            }
                        }
                        _ => bug_report!("Expected struct or enum item for constructor"),
                    };

                    let fields = args.into_iter().enumerate().map(|(idx, arg)| {
                        HIRExprField {
                            identifier: Token::new(
                                TokenKind::Identifier,
                                field_spans.get(idx).cloned().unwrap_or_else(TextSpan::default)
                            ),
                            expr: arg,
                            is_shorthand: false,
                        }
                    }).collect::<Vec<_>>();
                    
                    let path = if let Some(discriminant) = variant_discriminant {
                        QualifiedPath::ResolvedEnumVariant(item_idx, discriminant)
                    } else {
                        QualifiedPath::ResolvedType(item_idx)
                    };
                    
                    HIRExprKind::Struct {
                        path,
                        fields,
                        tail_expr: HIRStructTailExpr::None,
                    }
                } else {
                    // Function call
                    HIRExprKind::Call { fx_idx: call_expr.idx_ref, args }
                }
            },
            ExpressionKind::Return(ret_expr) => {
                let expr = ret_expr.return_value.as_ref().copied()
                    .map(|expr_id| self.build_expression(expr_id, ast, global_scope, ctx, true))
                    .unwrap_or_else(|| {
                        match ret_expr.return_value {
                            Some(value) => self.create_expression(HIRExprKind::Unit, TypeKind::Void, ast.query_expression(value).span.clone()),
                            None => self.create_expression(HIRExprKind::Unit, TypeKind::Void, ret_expr.return_keyword.span.clone()),
                        }
                    });

                HIRExprKind::Return { expr: Box::new(expr) }
            }
            ExpressionKind::While(while_statement) => {
                let condition = self.build_expression(while_statement.condition, ast, global_scope, ctx, false);
                let mut body_ctx = ctx.new_child();
                body_ctx.statements.reserve(while_statement.body.statements.len() + 1);

                let while_span = TextSpan::combine_refs(&[&while_statement.while_keyword.span, &condition.span]);
                
                let false_expr = self.create_expression(HIRExprKind::Bool(false), TypeKind::Bool, while_span.clone());
                let condition_false = self.create_expression(
                    HIRExprKind::Binary {
                        operator: snowflake_front::ast::BinaryOpKind::Equals,
                        left: Box::new(condition.clone()),
                        right: Box::new(false_expr),
                    },
                    TypeKind::Bool,
                    while_span.clone(),
                );

                let break_expr = self.create_expression(HIRExprKind::Break, TypeKind::Void, while_span.clone());
                let break_stmt = self.create_statement(HIRStmtKind::Expression { expr: break_expr }, while_span.clone());
                
                let then_block = self.create_expression(HIRExprKind::Block {
                    body: Box::new(Block {
                        statements: vec![Box::new(break_stmt)],
                        span: while_span.clone(),
                    }),
                    scope_id: self.current_scope_id(),
                }, TypeKind::Void, while_span.clone());
                
                let condition_check_expr = self.create_expression(
                    HIRExprKind::If {
                        condition: Box::new(condition_false),
                        then_block: Box::new(then_block),
                        else_block: None,
                    },
                    TypeKind::Void,
                    while_span.clone(),
                );

                let condition_check = self.create_statement(HIRStmtKind::Expression { expr: condition_check_expr }, while_span.clone());
                body_ctx.statements.push(condition_check);

                let while_body_count = while_statement.body.statements.len();
                for (idx, stmt_id) in while_statement.body.statements.iter().enumerate() {
                    let is_last = idx == while_body_count - 1;
                    self.build_statement(*stmt_id, ast, global_scope, &mut body_ctx, false, is_last);
                }

                HIRExprKind::Loop { body: body_ctx.statements }
            }
            ExpressionKind::Break(_) => HIRExprKind::Break,
            ExpressionKind::Continue(_) => HIRExprKind::Continue,
            ExpressionKind::Array(array_expr) => {
                let elements = array_expr.elements.iter()
                    .map(|elem_id| self.build_expression(*elem_id, ast, global_scope, ctx, true))
                    .collect::<Vec<_>>();

                let element_type = if let Some(first_elem) = elements.first() {
                    first_elem.ty.clone()
                } else {
                    TypeKind::from_token(&array_expr.type_decl)
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
                    TypeKind::Array(_, len) => *len,
                    _ => bug_report!("Indexing non-array type"),
                };

                // Get the element type from the current object type
                let element_type = match &object.ty {
                    TypeKind::Array(element_type, _) => *element_type.clone(),
                    _ => TypeKind::Error,
                };

                let span_clone = expr.span.clone();
                let length_expr = self.create_expression(HIRExprKind::Usize(len), TypeKind::Usize, span_clone);

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
                
                // Build field expr or extract field name
                let is_struct_or_enum = match &object.ty {
                    TypeKind::Object(object_type) => matches!(object_type.kind, ObjectKind::Struct(_)),
                    TypeKind::Enum { variant_name: Some(_), .. } => true,
                    _ => false,
                };

                let mut field = if !is_struct_or_enum {
                    // Build field expr for tuples
                    self.build_expression(tuple_index_expr.field.idx_no, ast, global_scope, ctx, true)
                } else {
                    // Temp field expr for structs and enums (resolved below)
                    self.create_expression(
                        HIRExprKind::Usize(0),
                        TypeKind::Usize,
                        TextSpan::default()
                    )
                };

                let element_type = match &object.ty {
                    TypeKind::Object(object_type) => {
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
                                    TypeKind::Error
                                } else {
                                    object_type.fields[idx].ty.as_ref().clone()
                                }
                            },
                            ObjectKind::Struct(_struct_idx) => {
                                let field_ast_expr = ast.query_expression(tuple_index_expr.field.idx_no);
                                match &field_ast_expr.kind {
                                    ExpressionKind::Path(path_expr) => {
                                        // Named field access
                                        let field_name = path_expr.path.tokens.last().unwrap().span.literal.clone();
                                        
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
                                                TypeKind::Usize,
                                                field_ast_expr.span.clone()
                                            );
                                            field_def.ty.as_ref().clone()
                                        } else {
                                            TypeKind::Error
                                        }
                                    }
                                    ExpressionKind::Number(num_expr) => {
                                        // Numeric field access for tuple structs
                                        let idx = num_expr.number as usize;
                                        if idx >= object_type.fields.len() {
                                            TypeKind::Error
                                        } else {
                                            field = self.create_expression(
                                                HIRExprKind::Usize(idx),
                                                TypeKind::Usize,
                                                field_ast_expr.span.clone()
                                            );
                                            object_type.fields[idx].ty.as_ref().clone()
                                        }
                                    }
                                    ExpressionKind::Usize(usize_expr) => {
                                        let idx = usize_expr.number;
                                        if idx >= object_type.fields.len() {
                                            TypeKind::Error
                                        } else {
                                            object_type.fields[idx].ty.as_ref().clone()
                                        }
                                    }
                                    _ => {
                                        bug_report!("Expected variable or numeric expression for struct field access, got {:?}", field_ast_expr.kind);
                                    }
                                }
                            }
                        }
                    },
                    TypeKind::Enum { enum_name, variant_name: Some(variant_name) } => {
                        let field_ast_expr = ast.query_expression(tuple_index_expr.field.idx_no);
                        let field_name = match &field_ast_expr.kind {
                            ExpressionKind::Path(path_expr) => {
                                path_expr.path.tokens.last().unwrap().span.literal.clone()
                            }
                            _ => {
                                bug_report!("Expected variable expression for enum field name, got {:?}", field_ast_expr.kind);
                            }
                        };

                        // Get field information
                        if let Some(enum_idx) = global_scope.lookup_enum(enum_name) {
                            let enum_def = global_scope.get_enum(enum_idx);
                            if let Some(variant) = enum_def.variants.iter().find(|v| &v.name == variant_name) {
                                match &variant.data {
                                    VariantData::Struct { fields } => {
                                        if let Some((field_index, _field_def)) = fields.iter().enumerate().find(|(_, f)| {
                                            f.identifier.as_ref().map(|id| &id.span.literal) == Some(&field_name)
                                        }) {
                                            // Convert the field name to a constant index
                                            // For enum variants, add 1 to account for the discriminant at index 0
                                            field = self.create_expression(
                                                HIRExprKind::Usize(field_index + 1),
                                                TypeKind::Usize,
                                                field_ast_expr.span.clone()
                                            );
                                            // Type is already set in the AST expression
                                            expr.ty.clone()
                                        } else {
                                            TypeKind::Error
                                        }
                                    }
                                    _ => TypeKind::Error
                                }
                            } else {
                                TypeKind::Error
                            }
                        } else {
                            TypeKind::Error
                        }
                    },
                    _ => {
                        TypeKind::Error
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
                let path_len = struct_expr.path.segments.len();
                let struct_name = struct_expr.path.segments.last()
                    .expect("Struct path should have at least one segment")
                    .identifier.span.literal.clone();
                
                let path = if let Some(struct_idx) = self.lookup_struct_with_context(&struct_name, global_scope, ctx) {
                    QualifiedPath::ResolvedType(struct_idx)
                } else if path_len >= 2 {
                    let enum_name = &struct_expr.path.segments[path_len - 2].identifier.span.literal;
                    if let Some((enum_idx, variant)) = global_scope.lookup_enum_variant(enum_name, &struct_name) {
                        QualifiedPath::ResolvedEnumVariant(enum_idx, variant.discriminant)
                    } else {
                        panic!("Struct/enum variant '{}' should be resolved during semantic analysis", struct_name);
                    }
                } else {
                    panic!("Struct '{}' should be resolved during semantic analysis", struct_name);
                };

                HIRExprKind::Struct {
                    path,
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
            ExpressionKind::Path(path_expr) => {
                if let Some(var_idx) = path_expr.resolved_variable {
                    HIRExprKind::Var { var_idx }
                } else {
                    // Path didn't resolve to a variable during semantic analysis
                    // Check if it's a unit struct or enum variant
                    let path_len = path_expr.path.segments.len();
                    let identifier = path_expr.path.segments.last().unwrap().identifier.span.literal.clone();
                    
                    let path = if let Some(struct_idx) = self.lookup_struct_with_context(&identifier, global_scope, ctx) {
                        Some(QualifiedPath::ResolvedType(struct_idx))
                    } else if path_len >= 2 {
                        let enum_name = &path_expr.path.segments[path_len - 2].identifier.span.literal;
                        if let Some((enum_idx, variant)) = global_scope.lookup_enum_variant(enum_name, &identifier) {
                            Some(QualifiedPath::ResolvedEnumVariant(enum_idx, variant.discriminant))
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    
                    if let Some(resolved_path) = path {
                        HIRExprKind::Struct {
                            path: resolved_path,
                            fields: vec![],
                            tail_expr: HIRStructTailExpr::None,
                        }
                    } else {
                        bug_report!("Path expression '{}' could not be resolved to a variable, unit struct, or enum variant during semantic analysis", identifier);
                    }
                }
            },
            ExpressionKind::MethodCall(method_call) => {
                // Desugar method call to regular function call
                // receiver.method(args) => method(receiver, args)
                let receiver = self.build_expression(method_call.receiver, ast, global_scope, ctx, true);
                
                let mut args = vec![receiver];
                for arg_id in &method_call.arguments {
                    args.push(self.build_expression(*arg_id, ast, global_scope, ctx, true));
                }
                
                HIRExprKind::Call {
                    fx_idx: method_call.resolved_fx,
                    args,
                }
            },
            ExpressionKind::Error(_) => bug_report!("Error expression in HIR builder"),
        };

        self.create_expression(kind, expr.ty.clone(), expr.span.clone())
    }

    fn declare_next_temp_var(&self, global_scope: &mut GlobalScope, ty: TypeKind) -> VariableIndex {
        global_scope.declare_variable(&self.next_temp_var(), ty, false, false)
    }

    fn next_temp_var(&self) -> Path {
        let temp_var_idx = self.temp_var_count.get();
        self.temp_var_count.set(temp_var_idx + 1);

        let temp_var_name = format!("%{}", temp_var_idx);

        Path {
            span: TextSpan::default(),
            segments: vec![PathSegment {
                identifier: Token {
                    span: TextSpan::default_with_name(&temp_var_name),
                    kind: TokenKind::Identifier,
                },
                arguments: None,
            }],
            tokens: vec![Token {
                span: TextSpan::default_with_name(&temp_var_name),
                kind: TokenKind::Identifier,
            }]
        }
    }
}