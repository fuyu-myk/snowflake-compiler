use snowflake_common::{bug_report, idx, Idx, IndexVec};
use snowflake_common::typings::{Type, ObjectKind};

use crate::ast::{ArrayExpression, AssignExpression, AssignmentOpKind, Ast, BinaryExpression, BinaryOp, BinaryOpKind, BlockExpression, Body, BoolExpression, BreakExpression, CallExpression, CompoundBinaryExpression, ConstStatement, ConstantItem, ContinueExpression, Expression, ExpressionKind, FieldExpression, FloatExpression, FxDeclaration, Generics, IfExpression, IndexExpression, Item, ItemIndex, ItemKind, LetStatement, NumberExpression, ParenExpression, ReturnStatement, Statement, StatementKind, StaticTypeAnnotation, StringExpression, StructExpression, TupleExpression, TypeKind, UnaryExpression, UnaryOpKind, UsizeExpression, VarExpression, VariantData, WhileStatement};
use crate::ast::visitor::ASTVisitor;
use crate::ast::eval::ASTEvaluator;
use snowflake_common::diagnostics::{DiagnosticsReportCell};
use snowflake_common::text;
use crate::ast::lexer::Lexer;
use snowflake_common::token::{Token, TokenKind};
use crate::ast::parser::Parser;
use snowflake_common::text::span::TextSpan;

use std::collections::HashMap;
use std::rc::Rc;
use std::cell::RefCell;
use snowflake_common::diagnostics;
use snowflake_common::diagnostics::printer::DiagnosticsPrinter;


idx!(VariableIndex);

#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub parameters: Vec<VariableIndex>,
    pub body: Body,
    pub return_type: Type,
}

#[derive(Debug, Clone)]
pub struct Variable {
    pub name: String,
    pub ty: Type,
    pub is_shadowing: bool,
}

pub struct GlobalScope {
    pub variables: IndexVec<VariableIndex, Variable>,
    pub functions: IndexVec<ItemIndex, Function>,
    pub structs: IndexVec<ItemIndex, Item>,
    pub global_variables: Vec<VariableIndex>,
}

impl GlobalScope {
    fn new() -> Self {
        GlobalScope {
            variables: IndexVec::new(),
            functions: IndexVec::new(),
            structs: IndexVec::new(),
            global_variables: Vec::new(),
        } 
    }

    pub fn declare_variable(&mut self, identifier: &str, ty: Type, is_global: bool, is_shadowing: bool) -> VariableIndex {
        let variable = Variable { name: identifier.to_string(), ty, is_shadowing };
        let variable_index = self.variables.push(variable);

        if is_global {
            self.global_variables.push(variable_index);
        }

        variable_index
    }

    fn lookup_global_variable(&self, identifier: &str) -> Option<VariableIndex> {
        self.global_variables.iter().rev()
            .map(|variable_index| (*variable_index, self.variables.get(*variable_index)))
            .find(|(_, variable)| variable.name == identifier)
            .map(|(variable_index, _) | variable_index)
    }

    pub fn lookup_global_variable_by_name(&self, identifier: &str) -> Option<VariableIndex> {
        self.lookup_global_variable(identifier)
    }

    pub fn create_function(&mut self, identifier: String, function_body: Body, parameters: Vec<VariableIndex>, return_type: Type) -> Result<ItemIndex, ItemIndex> {
        if let Some(existing_fx_idx) = self.lookup_fx(&identifier) {
            return Err(existing_fx_idx);
        }

        let function = Function { name: identifier, parameters: parameters, body: function_body, return_type };
        return Ok(self.functions.push(function));
    }

    fn set_variable_type(&mut self, var_idx: VariableIndex, ty: Type) {
        self.variables[var_idx].ty = ty;
    }

    pub fn get_variable_type(&self, var_idx: &VariableIndex) -> Option<Type> {
        Some(self.variables.get(*var_idx).ty.clone())
    }

    pub fn lookup_fx(&self, identifier: &str) -> Option<ItemIndex> {
        self.functions.indexed_iter().find(|(_, function)| function.name == identifier).map(|(idx, _)| idx)
    }

    pub fn declare_struct(&mut self, item: Item) -> Result<ItemIndex, ItemIndex> {
        let struct_name = match &item.kind {
            crate::ast::ItemKind::Struct(name, _, _) => &name.span.literal,
            _ => panic!("Expected struct item in declare_struct"),
        };

        if let Some(existing_struct_idx) = self.lookup_struct(struct_name) {
            return Err(existing_struct_idx);
        }

        Ok(self.structs.push(item))
    }

    pub fn lookup_struct(&self, identifier: &str) -> Option<ItemIndex> {
        self.structs.indexed_iter()
            .find(|(_, item)| {
                match &item.kind {
                    crate::ast::ItemKind::Struct(name, _, _) => name.span.literal == identifier,
                    _ => false,
                }
            })
            .map(|(idx, _)| idx)
    }

    pub fn get_struct(&self, struct_idx: ItemIndex) -> &Item {
        self.structs.get(struct_idx)
    }
    
    /// Convert a resolved struct type back to StructIndex
    pub fn struct_index_from_resolved(&self, resolved_index: u32) -> ItemIndex {
        ItemIndex::new(resolved_index as usize)
    }

    /// Resolve all unresolved struct types to struct indices
    pub fn resolve_struct_types(&mut self) -> Result<(), Vec<Token>> {
        let mut unresolved_types = Vec::new();
        let mut struct_lookup = std::collections::HashMap::new();

        for (struct_idx, item) in self.structs.indexed_iter() {
            if item.is_local {
                continue;
            }
            
            match &item.kind {
                crate::ast::ItemKind::Struct(name, _, _) => {
                    struct_lookup.insert(name.span.literal.clone(), struct_idx);
                }
                _ => continue,
            }
        }
        
        let function_indices: Vec<_> = self.functions.indices().collect();
        let variable_indices: Vec<_> = self.variables.indices().collect();

        for func_idx in function_indices {
            let param_indices = self.functions[func_idx].parameters.clone();
            for param_idx in param_indices {
                if let Err(unresolved) = Self::resolve_type_recursive_static(
                    &mut self.variables[param_idx].ty, &struct_lookup
                ) {
                    unresolved_types.extend(unresolved);
                }
            }
            
            if let Err(unresolved) = Self::resolve_type_recursive_static(
                &mut self.functions[func_idx].return_type, &struct_lookup
            ) {
                unresolved_types.extend(unresolved);
            }
        }
        
        for var_idx in variable_indices {
            if let Err(unresolved) = Self::resolve_type_recursive_static(
                &mut self.variables[var_idx].ty, &struct_lookup
            ) {
                unresolved_types.extend(unresolved);
            }
        }
        
        if unresolved_types.is_empty() {
            Ok(())
        } else {
            Err(unresolved_types)
        }
    }
    
    /// Static helper for type resolution
    fn resolve_type_recursive_static(ty: &mut Type, struct_names: &HashMap<String, ItemIndex>) -> Result<(), Vec<Token>> {
        match ty {
            Type::ObjectUnresolved(name) => {
                if let Some(_) = struct_names.get(name.span.literal.as_str()) {
                    *ty = Type::struct_resolved(name.span.literal.clone(), vec![]);
                    Ok(())
                } else {
                    Err(vec![name.clone()])
                }
            }
            Type::Array(element_type, _) => {
                Self::resolve_type_recursive_static(element_type, struct_names)
            }
            Type::Object(object_type) => {
                let mut all_unresolved = Vec::new();
                for field in &mut object_type.fields {
                    if let Err(unresolved) = Self::resolve_type_recursive_static(&mut field.ty, struct_names) {
                        all_unresolved.extend(unresolved);
                    }
                }
                if all_unresolved.is_empty() {
                    Ok(())
                } else {
                    Err(all_unresolved)
                }
            }
            _ => Ok(()),
        }
    }
}

struct LocalScope {
    locals: Vec<VariableIndex>,
    function: Option<ItemIndex>,
    structs: Vec<ItemIndex>,
}

impl LocalScope {
    fn new(function: Option<ItemIndex>) -> Self {
        LocalScope { locals: Vec::new(), function, structs: Vec::new() }
    }

    fn add_local_var(&mut self, local: VariableIndex) {
        self.locals.push(local);
    }

    fn add_local_struct(&mut self, struct_idx: ItemIndex) {
        self.structs.push(struct_idx);
    }
}

struct ScopeStack {
    local_scopes: Vec<LocalScope>,
    global_scope: GlobalScope,
}

impl ScopeStack {
    fn new() -> Self {
        ScopeStack { local_scopes: Vec::new(), global_scope: GlobalScope::new() }
    }

    fn enter_scope(&mut self) {
        self._enter_scope(None);
    }

    fn _enter_scope(&mut self, fx_idx: Option<ItemIndex>) {
        self.local_scopes.push(LocalScope::new(fx_idx));
    }

    fn enter_fx_scope(&mut self, fx_idx: ItemIndex) {
        self._enter_scope(Some(fx_idx));
    }
    
    fn exit_scope(&mut self) {
        self.local_scopes.pop();
    }

    fn exit_fx_scope(&mut self) {
        assert!(self.local_scopes.last().unwrap().function.is_some());
        self.exit_scope();
    }

    fn declare_variable(&mut self, identifier: &str, ty: Type) -> VariableIndex {
        let is_inside_global_scope = self.is_inside_local_scope();
        let index = self._declare_variable(identifier, ty, !is_inside_global_scope);

        if is_inside_global_scope {
            self.current_local_scope_mut().add_local_var(index);
        }

        return index;
    }

    fn _declare_variable(&mut self, identifier: &str, ty: Type, is_global: bool) -> VariableIndex {
        let is_shadowing = match self.current_local_scope() {
            None => false,
            Some(scope) => scope.locals.iter().any(|local| {
                let local = self.global_scope.variables.get(*local);
                local.name == identifier
            }),
        };

        self.global_scope.declare_variable(identifier, ty, is_global, is_shadowing)
    }

    fn lookup_variable(&mut self, identifier: &str) -> Option<VariableIndex> { // top-down lookup
        for scope in self.local_scopes.iter_mut().rev() {
            if let Some((index, _variable)) = scope.locals.iter() // loop local var idxs
                .map(|idx| (*idx, self.global_scope.variables.get(*idx))) // lookup idx in global_scope
                .find(|(_idx, variable)| variable.name == identifier) { // use name to lookup var

                return Some(index)
            }
        }

        self.global_scope.lookup_global_variable(identifier)
    }

    fn is_inside_local_scope(&self) -> bool { // checks if variable is in local scope
        !self.local_scopes.is_empty()
    }

    fn from_global_scope(global_scope: GlobalScope) -> Self {
        ScopeStack {
            local_scopes: Vec::new(),
            global_scope,
        }
    }

    fn surrounding_function(&self) -> Option<&Function> {
        return self.surrounding_function_idx()
        .map(|fx| self.global_scope.functions.get(fx));
    }

    fn surrounding_function_idx(&self) -> Option<ItemIndex> {
        self.local_scopes.iter().rev()
            .filter_map(|scope| scope.function)
            .next()
    }

    fn current_local_scope(&self) -> Option<&LocalScope> {
        self.local_scopes.last()
    }

    fn current_local_scope_mut(&mut self) -> &mut LocalScope {
        self.local_scopes.last_mut().unwrap()
    }

    fn declare_local_struct(&mut self, item: Item) -> Result<ItemIndex, ItemIndex> {
        // For local structs, allow shadowing of global structs
        // Check if there's already a local struct with the same name in the current scope
        if let Some(current_scope) = self.local_scopes.last() {
            let struct_name = match &item.kind {
                ItemKind::Struct(name, _, _) => &name.span.literal,
                _ => return Err(ItemIndex::new(0)), // Should never happen
            };
            
            let unscoped_name = if let Some(last_part) = struct_name.split("::").last() {
                last_part
            } else {
                struct_name
            };
            
            // Check for conflicts only within current local scope
            for &existing_struct_idx in &current_scope.structs {
                let existing_struct = self.global_scope.get_struct(existing_struct_idx);
                if let ItemKind::Struct(existing_name, _, _) = &existing_struct.kind {
                    let existing_unscoped = if let Some(last_part) = existing_name.span.literal.split("::").last() {
                        last_part
                    } else {
                        &existing_name.span.literal
                    };
                    
                    if existing_unscoped == unscoped_name {
                        return Err(existing_struct_idx);
                    }
                }
            }
        }
        
        let struct_idx = self.global_scope.structs.push(item);
        
        // Add to current local scope for scoping
        if let Some(current_scope) = self.local_scopes.last_mut() {
            current_scope.add_local_struct(struct_idx);
        }
        
        Ok(struct_idx)
    }

    fn lookup_local_struct(&self, identifier: &str) -> Option<ItemIndex> {
        for scope in self.local_scopes.iter().rev() {
            for &struct_idx in &scope.structs {
                let struct_item = self.global_scope.get_struct(struct_idx);
                if let ItemKind::Struct(name, _, _) = &struct_item.kind {
                    let struct_name = if let Some(last_part) = name.span.literal.split("::").last() {
                        last_part
                    } else {
                        &name.span.literal
                    };
                    
                    if struct_name == identifier {
                        return Some(struct_idx);
                    }
                }
            }
        }
        None
    }

    fn lookup_struct_with_local(&self, identifier: &str) -> Option<ItemIndex> {
        if let Some(local_struct) = self.lookup_local_struct(identifier) {
            return Some(local_struct);
        }
        
        self.global_scope.lookup_struct(identifier)
    }
}

struct Resolver {
    scopes: ScopeStack,
    diagnostics: DiagnosticsReportCell,
    loop_depth: usize,
    expected_array_type: Option<Type>, // Track expected array type for better error reporting
    visited_local_items: std::collections::HashSet<ItemIndex>,
}

fn expect_type(diagnostics: &DiagnosticsReportCell, expected: Type, actual: &Type, span: &TextSpan) -> Type {
    if matches!(expected, Type::ObjectUnresolved(_)) || matches!(actual, Type::ObjectUnresolved(_)) {
        return expected;
    }
    
    // Implicit conversion from Int to Usize
    let is_compatible = actual.is_assignable_to(&expected) || 
                       (matches!(expected, Type::Usize) && matches!(actual, Type::Int));
    
    if !is_compatible {
        diagnostics.borrow_mut().report_type_mismatch(&expected, actual, span);
    }

    expected
}

impl Resolver {
    fn new(diagnostics: DiagnosticsReportCell, scopes: ScopeStack) -> Self {
        Resolver {
            scopes,
            diagnostics,
            loop_depth: 0,
            expected_array_type: None,
            visited_local_items: std::collections::HashSet::new(),
        }
    }

    fn expect_type(&self, expected: Type, actual: &Type, span: &TextSpan) -> Type {
        expect_type(&self.diagnostics, expected, actual, span)
    }

    fn expect_index_type(&self, expected: Type, actual: &Type, span: &TextSpan, is_neg_idx: bool) {
        // Implicit conversion from Int to Usize for array indexing
        let is_compatible = actual.is_assignable_to(&expected) || 
                           (matches!(expected, Type::Usize) && matches!(actual, Type::Int));
        
        if !is_compatible && !is_neg_idx {
            self.diagnostics.borrow_mut().report_index_type_mismatch(expected, actual, span);
        }
    }

    fn is_constant_zero(&self, ast: &Ast, expr: &Expression) -> bool {
        match &expr.kind {
            ExpressionKind::Number(number_expr) => number_expr.number == 0,
            ExpressionKind::Parenthesised(paren_expr) => {
                let inner_expr = ast.query_expression(paren_expr.expression);
                self.is_constant_zero(ast, inner_expr)
            }
            _ => false,
        }
    }

    pub fn resolve(&mut self, ast: &mut Ast) {
        for id in ast.items.cloned_indices() {
            let item = ast.query_item(id);
            if item.is_local {
                continue;
            }
            self.visit_item(ast, id);
        }
    }

    pub fn resolve_binary_expression(&self, ast: &Ast, left: &Expression, right: &Expression, operator: &BinaryOpKind) -> Type {
        let left_ty = &left.ty;
        let right_ty = &right.ty;
        
        let result_type = match operator {
            BinaryOpKind::Equals | BinaryOpKind::NotEquals | 
            BinaryOpKind::LessThan | BinaryOpKind::GreaterThan | 
            BinaryOpKind::LessThanOrEqual | BinaryOpKind::GreaterThanOrEqual => {
                self.expect_type(left_ty.clone(), right_ty, &right.span(&ast));
                Type::Bool
            },
            BinaryOpKind::Plus | BinaryOpKind::Minus | BinaryOpKind::Multiply | BinaryOpKind::Divide => {
                if left_ty.is_assignable_to(right_ty) {
                    left_ty.clone()
                } else if right_ty.is_assignable_to(left_ty) {
                    self.expect_type(left_ty.clone(), right_ty, &right.span(&ast));
                    left_ty.clone()
                } else {
                    self.expect_type(left_ty.clone(), right_ty, &right.span(&ast));
                    left_ty.clone()
                }
            },
            BinaryOpKind::Power | BinaryOpKind::Modulo | 
            BinaryOpKind::BitwiseAnd | BinaryOpKind::BitwiseXor | BinaryOpKind::BitwiseOr |
            BinaryOpKind::ShiftLeft | BinaryOpKind::ShiftRight => {
                self.expect_type(Type::Int, left_ty, &left.span(&ast));
                self.expect_type(Type::Int, right_ty, &right.span(&ast));
                Type::Int
            },
        };

        // Check for division by zero at compile time
        match operator {
            BinaryOpKind::Divide | BinaryOpKind::Modulo => {
                if self.is_constant_zero(ast, right) && !right.kind.is_from_compound() {
                    let operator_str = match operator {
                        BinaryOpKind::Divide => "/",
                        BinaryOpKind::Modulo => "%",
                        _ => unreachable!(),
                    };
                    self.diagnostics.borrow_mut().report_division_by_zero(operator_str, &right.span(ast));
                }
            }
            _ => {}
        }

        result_type
    }

    pub fn resolve_compound_binary_expression(&self, ast: &Ast, left: &Expression, right: &Expression, operator: &AssignmentOpKind) -> Type {
        // First, validate that the left-hand side is a valid l-value (variable)
        // If it's not, we'll let the type checker catch it when we return void
        // This will generate errors like "binary operation '+=' cannot be applied to type 'int' and 'void'"
        match &left.kind {
            ExpressionKind::Variable(_) => {
                // Valid l-value, proceed with normal type checking
                let type_matrix: (Type, Type) = match operator {
                    AssignmentOpKind::PlusAs | AssignmentOpKind::MinusAs | 
                    AssignmentOpKind::MultiplyAs | AssignmentOpKind::DivideAs => (Type::Int, Type::Int),
                    AssignmentOpKind::ModuloAs | AssignmentOpKind::BitwiseAndAs | 
                    AssignmentOpKind::BitwiseOrAs | AssignmentOpKind::BitwiseXorAs | 
                    AssignmentOpKind::ShiftLeftAs | AssignmentOpKind::ShiftRightAs => (Type::Int, Type::Int),
                };

                self.expect_type(type_matrix.0, &left.ty, &left.span(&ast));
                self.expect_type(type_matrix.1, &right.ty, &right.span(&ast));
            }
            _ => {
                // Invalid l-value (like another assignment expression)
                // Still check the right side for completeness, but left side will have void type
                // This will naturally cause the intended error message when this void type
                // is used in subsequent operations
                let expected_right_type = match operator {
                    AssignmentOpKind::PlusAs | AssignmentOpKind::MinusAs | 
                    AssignmentOpKind::MultiplyAs | AssignmentOpKind::DivideAs | 
                    AssignmentOpKind::ModuloAs | AssignmentOpKind::BitwiseAndAs | 
                    AssignmentOpKind::BitwiseOrAs | AssignmentOpKind::BitwiseXorAs | 
                    AssignmentOpKind::ShiftLeftAs | AssignmentOpKind::ShiftRightAs => Type::Int,
                };
                
                self.expect_type(expected_right_type, &right.ty, &right.span(&ast));
            }
        }

        Type::Void
    }

    pub fn resolve_unary_expression(&self, ast: &Ast, operand: &Expression, operator: &UnaryOpKind) -> Type {
        let type_matrix: (Type, Type) = match operator {
            UnaryOpKind::Negation => (Type::Int, Type::Int),
            UnaryOpKind::BitwiseNot => (Type::Int, Type::Int),
        };

        self.expect_type(type_matrix.0, &operand.ty, &operand.span(&ast));

        type_matrix.1
    }

    /// Resolve type from annotation with scope awareness
    pub fn resolve_type_from_annotation(&self, type_annotation: &StaticTypeAnnotation) -> Type {
        match &type_annotation.type_kind {
            TypeKind::Array { element_type, length, .. } => {
                let resolved_element_type = self.resolve_type_kind(element_type);
                let length_str = &length.span.literal;
                match length_str.parse::<usize>() {
                    Ok(len) => Type::Array(Box::new(resolved_element_type), len),
                    Err(_) => {
                        // TODO: Proper reporting of wrong array len
                        self.diagnostics.borrow_mut().report_undeclared_type(length);
                        Type::Error
                    }
                }
            },
            TypeKind::Slice { element_type, .. } => {
                let _resolved_element_type = self.resolve_type_kind(element_type);
                // TODO: Implement slices
                Type::Error
            },
            TypeKind::Simple { type_name } => {
                self.resolve_type_from_string(type_name)
            }
            TypeKind::Tuple { element_types, .. } => {
                let mut resolved_types = Vec::new();
                for elem_type in element_types {
                    let resolved_type = self.resolve_type_kind(elem_type);
                    resolved_types.push(resolved_type);
                }
                Type::tuple(resolved_types)
            }
        }
    }

    /// Resolve type kind with scope awareness
    pub fn resolve_type_kind(&self, type_kind: &TypeKind) -> Type {
        match type_kind {
            TypeKind::Array { element_type, length, .. } => {
                let resolved_element_type = self.resolve_type_kind(element_type);
                let length_str = &length.span.literal;
                match length_str.parse::<usize>() {
                    Ok(len) => Type::Array(Box::new(resolved_element_type), len),
                    Err(_) => {
                        // TODO: Proper reporting of wrong array len
                        self.diagnostics.borrow_mut().report_undeclared_type(length);
                        Type::Error
                    }
                }
            },
            TypeKind::Slice { element_type, .. } => {
                let _resolved_element_type = self.resolve_type_kind(element_type);
                // TODO: Implement slices
                Type::Error
            },
            TypeKind::Simple { type_name } => {
                self.resolve_type_from_string(type_name)
            }
            TypeKind::Tuple { element_types, .. } => {
                let mut resolved_types = Vec::new();
                for elem_type in element_types {
                    let resolved_type = self.resolve_type_kind(elem_type);
                    resolved_types.push(resolved_type);
                }
                Type::tuple(resolved_types)
            }
        }
    }

    /// Resolve type from string with scope awareness for struct types
    pub fn resolve_type_from_string(&self, type_name: &Token) -> Type {
        let builtin_type = Type::from_token(type_name);
        if !matches!(builtin_type, Type::ObjectUnresolved(_)) {
            return builtin_type;
        }
        
        if let Some(struct_idx) = self.scopes.lookup_struct_with_local(&type_name.span.literal) {
            let struct_item = self.scopes.global_scope.get_struct(struct_idx);
            if let ItemKind::Struct(identifier, _, variant_data) = &struct_item.kind {
                match variant_data {
                    VariantData::Struct { fields } => {
                        let mut field_types = Vec::new();
                        for field in fields {
                            if let Some(field_name) = &field.identifier {
                                let field_type = self.resolve_type_kind(&field.ty);
                                field_types.push((field_name.span.literal.clone(), field_type));
                            }
                        }

                        return Type::struct_resolved(identifier.span.literal.clone(), field_types);
                    }
                }
            }
        }
        
        self.diagnostics.borrow_mut().report_undeclared_type(type_name);
        Type::ObjectUnresolved(type_name.clone())
    }
}

impl ASTVisitor for Resolver {
    fn visit_let_statement(&mut self, ast: &mut Ast, let_statement: &LetStatement, statement: &Statement) {
        let identifier = let_statement.identifier.span.literal.clone();
        
        // Set expected array type if we have an array type annotation
        let expected_type = match &let_statement.type_annotation {
            Some(type_annotation) => {
                let ty = self.resolve_type_from_annotation(type_annotation);
                if matches!(ty, Type::Array(_, _)) {
                    self.expected_array_type = Some(ty.clone());
                }
                Some(ty)
            }
            None => None,
        };
        
        self.visit_expression(ast, let_statement.initialiser);
        let initialiser_expression = &ast.query_expression(let_statement.initialiser);

        self.expected_array_type = None;

        let ty = match expected_type {
            Some(expected_ty) => {
                self.expect_type(expected_ty.clone(), &initialiser_expression.ty, &initialiser_expression.span(&ast));
                expected_ty
            }
            None => initialiser_expression.ty.clone(),
        };

        let variable = self.scopes.declare_variable(&identifier, ty);
        ast.set_variable_for_statement(&statement.id, variable);
    }

    fn visit_const_statement(&mut self, ast: &mut Ast, const_statement: &ConstStatement, statement: &Statement) {
        let identifier = const_statement.identifier.span.literal.clone();

        if identifier.chars().any(|c| c.is_lowercase()) {
            self.diagnostics.borrow_mut().warn_non_upper_case(&identifier, &const_statement.identifier.span);
        }
        
        let ty = self.resolve_type_from_annotation(&const_statement.type_annotation);
        if matches!(ty, Type::Array(_, _)) {
            self.expected_array_type = Some(ty.clone());
        }
        
        self.visit_expression(ast, const_statement.expr);
        let initialiser_expression = &ast.query_expression(const_statement.expr);

        self.expected_array_type = None;

        let ty = self.expect_type(ty.clone(), &initialiser_expression.ty, &initialiser_expression.span(&ast));

        let variable = self.scopes.declare_variable(&identifier, ty);
        ast.set_variable_for_statement(&statement.id, variable);
    }

    fn visit_variable_expression(&mut self, ast: &mut Ast, variable_expression: &VarExpression, expr: &Expression) {
        let variable_name = &variable_expression.identifier.span.literal;
        match self.scopes.lookup_variable(variable_name) {
            None => {
                let mut diagnostics = self.diagnostics.borrow_mut();
                diagnostics.report_undeclared_variable(&variable_expression.identifier.span.literal, &variable_expression.identifier.span);
                ast.set_type(expr.id, Type::Error);
            }
            Some(variable_index) => {
                let variable = self.scopes.global_scope.variables.get(variable_index);
                ast.set_type(expr.id, variable.ty.clone());
                ast.set_variable(expr.id, variable_index);
            }
        };
    }

    fn visit_number_expression(&mut self, ast: &mut Ast, _number: &NumberExpression, expr: &Expression) {
        ast.set_type(expr.id, Type::Int);
    }

    fn visit_float_expression(&mut self, ast: &mut Ast, _float: &FloatExpression, expr: &Expression) {
        ast.set_type(expr.id, Type::Float);
    }

    fn visit_usize_expression(&mut self, ast: &mut Ast, _number: &UsizeExpression, expr: &Expression) {
        ast.set_type(expr.id, Type::Usize);
    }

    fn visit_string_expression(&mut self, ast: &mut Ast, _string: &StringExpression, expr: &Expression) {
        ast.set_type(expr.id, Type::String);
    }

    fn visit_unary_expression(&mut self, ast: &mut Ast, unary_expression: &UnaryExpression, expr: &Expression) {
        self.visit_expression(ast, unary_expression.operand);

        let operand = ast.query_expression(unary_expression.operand);
        let ty = self.resolve_unary_expression(ast, &operand, &unary_expression.operator.kind);

        ast.set_type(expr.id, ty);
    }

    fn visit_binary_expression(&mut self, ast: &mut Ast, binary_expression: &BinaryExpression, expr: &Expression) {
        self.visit_expression(ast, binary_expression.left);
        self.visit_expression(ast, binary_expression.right);
        
        let left = ast.query_expression(binary_expression.left);
        let right = ast.query_expression(binary_expression.right);

        let ty = self.resolve_binary_expression(ast, &left, &right, &binary_expression.operator.kind);
        ast.set_type(expr.id, ty);
    }

    fn visit_compound_binary_expression(&mut self, ast: &mut Ast, compound_expression: &CompoundBinaryExpression, expr: &Expression) {
        self.visit_expression(ast, compound_expression.left);
        self.visit_expression(ast, compound_expression.right);

        let left = ast.query_expression(compound_expression.left);
        let right = ast.query_expression(compound_expression.right);

        match &left.kind {
            ExpressionKind::Variable(var_expr) => {
                // Valid assignment target - perform desugaring
                // Transform `a += b` into `a = (a + b)`
                let ty = self.resolve_compound_binary_expression(ast, &left, &right, &compound_expression.operator);
                
                let var_identifier = var_expr.identifier.clone();
                let var_idx = var_expr.variable_index;
                let left_expr_id = compound_expression.left;
                let right_expr_id = compound_expression.right;
                let operator = compound_expression.operator;
                
                // Desugaring: create the binary operation (a + b)
                let binary_op_kind = self.assignment_to_binary_op(operator);
                let binary_op = BinaryOp::new(binary_op_kind, self.desugared_token(&compound_expression.operator_token));
                let binary_expr_id = ast.binary_expression(binary_op, left_expr_id, right_expr_id, true).id;
                
                // Visit the newly created binary expression to resolve its type
                self.visit_expression(ast, binary_expr_id);
                
                // Create the assignment expression (a = (a + b))
                let left_hand_side_expr_id = ast.variable_expression(var_identifier.clone()).id;
                let assignment_expr = AssignExpression {
                    lhs: left_hand_side_expr_id,
                    equals: self.create_synthetic_equals_token(&var_identifier),
                    expression: binary_expr_id,
                    variable_index: var_idx,
                };
                
                // Replace the current expression with the desugared assignment
                let expr_mut = ast.query_expression_mut(expr.id);
                expr_mut.kind = ExpressionKind::Assignment(assignment_expr);
                expr_mut.ty = ty;
            }
            _ => {
                let operator_str = format!("{}=", match compound_expression.operator {
                    AssignmentOpKind::PlusAs => "+",
                    AssignmentOpKind::MinusAs => "-",
                    AssignmentOpKind::MultiplyAs => "*",
                    AssignmentOpKind::DivideAs => "/",
                    AssignmentOpKind::ModuloAs => "%",
                    AssignmentOpKind::BitwiseAndAs => "&",
                    AssignmentOpKind::BitwiseOrAs => "|",
                    AssignmentOpKind::BitwiseXorAs => "^",
                    AssignmentOpKind::ShiftLeftAs => "<<",
                    AssignmentOpKind::ShiftRightAs => ">>",
                });
                
                self.diagnostics.borrow_mut().report_invalid_assignment_target(&operator_str, &expr.span(ast));
                ast.set_type(expr.id, Type::Void);
            }
        }
    }

    fn visit_parenthesised_expression(&mut self, ast: &mut Ast, parenthesised_expression: &ParenExpression, expr: &Expression) {
        self.visit_expression(ast, parenthesised_expression.expression);

        let expression = ast.query_expression(parenthesised_expression.expression);

        ast.set_type(expr.id, expression.ty.clone());
    }

    fn visit_block_expression(&mut self, ast: &mut Ast, block_expression: &BlockExpression, expr: &Expression) {
        self.scopes.enter_scope();

        for statement in &block_expression.statements {
            self.visit_statement(ast, *statement);
        }

        self.scopes.exit_scope();

        let ty = block_expression.statements.last().map(|statement| {
            let statement = ast.query_statement(*statement);
            match statement.kind {
                StatementKind::Expression(expr_id) => {
                    let expr = ast.query_expression(expr_id);
                    expr.ty.clone()
                }
                _ => Type::Void,
            }
        }).unwrap_or(Type::Void);
        ast.set_type(expr.id, ty);
    }

    fn visit_boolean_expression(&mut self, ast: &mut Ast, _boolean: &BoolExpression, expr: &Expression) {
        ast.set_type(expr.id, Type::Bool);
    }

    fn visit_if_expression(&mut self, ast: &mut Ast, if_statement: &IfExpression, expr: &Expression) {
        self.scopes.enter_scope();
        self.visit_expression(ast, if_statement.condition);

        // conditional expression type check
        let conditional_expression = ast.query_expression(if_statement.condition);
        self.expect_type(Type::Bool, &conditional_expression.ty, &conditional_expression.span(&ast));

        self.visit_body(ast, &if_statement.then_branch);
        let mut ty = Type::Void;
        self.scopes.exit_scope();

        if let Some(else_branch) = &if_statement.else_branch {
            self.scopes.enter_scope();

            self.visit_body(ast, &else_branch.body);

            let then_expression_type = if_statement.then_branch.type_or_void(ast);
            let else_expression_type = else_branch.body.type_or_void(ast);
            
            // Only perform type unification if both branches return non-void types
            if !matches!(then_expression_type, Type::Void) && !matches!(else_expression_type, Type::Void) {
                let else_span = else_branch.body.span(ast);
                ty = self.expect_type(then_expression_type, &else_expression_type, &else_span);
            } else {
                ty = Type::Void;
            }

            self.scopes.exit_scope();
        }

        ast.set_type(expr.id, ty);
    }
    
    fn visit_fx_decl(&mut self, ast: &mut Ast, fx_decl: &FxDeclaration, _item_id: ItemIndex) {
        // fetching fx idx
        let fx_idx = fx_decl.index;

        self.scopes.enter_fx_scope(fx_idx);

        let function = self.scopes.global_scope.functions.get(fx_idx);
        
        for parameter in function.parameters.clone() {
            let unresolved_token = {
                let param_var = self.scopes.global_scope.variables.get(parameter);
                if let Type::ObjectUnresolved(ref token) = param_var.ty {
                    Some(token.clone())
                } else {
                    None
                }
            };
            
            if let Some(token) = unresolved_token {
                let resolved_type = self.resolve_type_from_string(&token);
                let param_var = self.scopes.global_scope.variables.get_mut(parameter);
                param_var.ty = resolved_type;
            }
            
            self.scopes.current_local_scope_mut().locals.push(parameter);
        }

        let return_type = if fx_decl.return_type.is_some() {
            self.resolve_type_kind(&fx_decl.return_type.as_ref().unwrap().ty)
        } else {
            Type::Void
        };
        
        let function = self.scopes.global_scope.functions.get_mut(fx_idx);
        function.return_type = return_type;

        let function = self.scopes.global_scope.functions.get(fx_idx);
        for stmt_id in (*function.body).clone() {
            let statement = ast.query_statement(stmt_id);
            match &statement.kind {
                StatementKind::Return(return_statement) => {
                    let return_statement = return_statement.clone();
                    self.visit_return_statement(ast, &return_statement);
                    break; // Exit the loop but continue to cleanup
                }
                _ => {
                    self.visit_statement(ast, statement.id);
                }
            }
        }

        self.scopes.exit_fx_scope();
    }

    fn visit_return_statement(&mut self, ast: &mut Ast, return_statement: &ReturnStatement) {
        let return_keyword = return_statement.return_keyword.clone();
        // todo: do not clone this
        match self.scopes.surrounding_function().cloned() {
            None => {
                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                diagnostics_binding.report_return_outside_function(&return_statement.return_keyword);
            }
            Some(function) => {
                if let Some(return_expression) = &return_statement.return_value {
                    self.visit_expression(ast, *return_expression);
                    let return_expression = ast.query_expression(*return_expression);
                    self.expect_type(function.return_type.clone(), &return_expression.ty, &return_expression.span(&ast));
                } else {
                    self.expect_type(function.return_type.clone(), &Type::Void, &return_keyword.span);
                }
            }
        }
    }

    fn visit_call_expression(&mut self, ast: &mut Ast, call_expression: &CallExpression, expr: &Expression) {
        let function = self.scopes.global_scope.lookup_fx(&call_expression.callee.span.literal);

        let ty = match function {
            None => {
                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                diagnostics_binding.report_undeclared_function(&call_expression.callee);

                Type::Error
            }
            Some(fx_idx) => {
                let function = self.scopes.global_scope.functions.get(fx_idx);
                ast.set_function(expr.id, fx_idx);
                if function.parameters.len() != call_expression.arguments.len() {
                    let mut diagnostics_binding = self.diagnostics.borrow_mut();
                    diagnostics_binding.report_invalid_arg_count(
                        &call_expression.callee.span,
                        function.parameters.len(),
                        call_expression.arguments.len(),
                    );
                }

                let return_type = function.return_type.clone();
                for (argument, parameter) in call_expression.arguments.iter().zip(function.parameters.clone().iter()) {
                    self.visit_expression(ast, *argument);

                    let argument_expression = ast.query_expression(*argument);
                    let parameter = self.scopes.global_scope.variables.get(*parameter);
                    self.expect_type(parameter.ty.clone(), &argument_expression.ty, &argument_expression.span(&ast));
                }

                return_type
            }
        };

        ast.set_type(expr.id, ty);
    }

    fn visit_assignment_expression(&mut self, ast: &mut Ast, assignment_expression: &AssignExpression, expr: &Expression) {
        self.visit_expression(ast, assignment_expression.expression);
        self.visit_expression(ast, assignment_expression.lhs);
        
        let lhs_expr = ast.query_expression(assignment_expression.lhs);
        let rhs_expr = ast.query_expression(assignment_expression.expression);
        
        self.expect_type(lhs_expr.ty.clone(), &rhs_expr.ty, &rhs_expr.span(ast));
        
        ast.set_type(expr.id, rhs_expr.ty.clone());
    }

    fn visit_while_statement(&mut self, ast: &mut Ast, while_statement: &WhileStatement) {
        self.visit_expression(ast, while_statement.condition);
        let condition = ast.query_expression(while_statement.condition);
        self.expect_type(Type::Bool, &condition.ty, &condition.span(&ast));

        self.loop_depth += 1;
        self.visit_body(ast, &while_statement.body);
        self.loop_depth -= 1;
    }

    fn visit_break_expression(&mut self, ast: &mut Ast, break_expression: &BreakExpression, expr: &Expression) {
        if self.loop_depth == 0 {
            let mut diagnostics_binding = self.diagnostics.borrow_mut();
            diagnostics_binding.report_loop_keyword_outside_loop(&break_expression.break_keyword);
        }
        ast.set_type(expr.id, Type::Void);
    }

    fn visit_continue_expression(&mut self, ast: &mut Ast, continue_expression: &ContinueExpression, expr: &Expression) {
        if self.loop_depth == 0 {
            let mut diagnostics_binding = self.diagnostics.borrow_mut();
            diagnostics_binding.report_loop_keyword_outside_loop(&continue_expression.continue_keyword);
        }
        ast.set_type(expr.id, Type::Void);
    }

    fn visit_array_expression(&mut self, ast: &mut Ast, array_expression: &ArrayExpression, expr: &Expression) {
        for element in &array_expression.elements {
            self.visit_expression(ast, *element);
        }

        // Infer the array element type from the first element (if any)
        let inferred_element_type = if let Some(first_element_id) = array_expression.elements.first() {
            let first_element = ast.query_expression(*first_element_id);
            first_element.ty.clone()
        } else {
            self.resolve_type_from_string(&array_expression.type_decl)
        };
        
        let actual_array_type = Type::Array(Box::new(inferred_element_type.clone()), array_expression.elements.len());

        ast.set_type(expr.id, actual_array_type.clone());

        let should_report_element_mismatches = if let Some(expected) = &self.expected_array_type {
            match expected {
                Type::Array(expected_element_type, expected_length) => {
                    let length_matches = *expected_length == array_expression.elements.len();
                    
                    // Check if ALL elements would match the expected type
                    let all_elements_match_expected = array_expression.elements.iter().all(|element_id| {
                        let element = ast.query_expression(*element_id);
                        element.ty.is_assignable_to(expected_element_type)
                    });
                    
                    if !length_matches && !all_elements_match_expected {
                        false
                    } else {
                        true
                    }
                }
                _ => true,
            }
        } else {
            true
        };

        // Check that all elements match the inferred element type
        if should_report_element_mismatches && !array_expression.elements.is_empty() {
            for element_id in &array_expression.elements {
                let element = ast.query_expression(*element_id);
                if !element.ty.is_assignable_to(&inferred_element_type) {
                    self.diagnostics.borrow_mut().report_type_mismatch(
                        &inferred_element_type,
                        &element.ty,
                        &element.span(ast)
                    );
                }
            }
        }
    }

    fn visit_index_expression(&mut self, ast: &mut Ast, index_expression: &IndexExpression, expr: &Expression) {
        self.visit_expression(ast, index_expression.object);
        
        let object = ast.query_expression(index_expression.object);
        let mut current_type = object.ty.clone();
        let object_span = object.span(ast);

        self.visit_expression(ast, index_expression.index.idx_no);

        let index = ast.query_expression(index_expression.index.idx_no);
        let index_ty = index.ty.clone();
        let index_span = index.span(ast);
        let index_literal = index_span.literal.clone();

        // Check for negative array index patterns
        let is_neg_idx = self.check_for_negative_array_index(ast, index, &index_span);

        self.expect_index_type(Type::Usize, &index_ty, &index_span, is_neg_idx);

        match &current_type {
            Type::Array(element_type, array_size) => {
                let element_type_cloned = *element_type.clone();
                let array_size_cloned = *array_size;

                // Compile-time bounds checking for constant indices
                if let Ok(idx) = index_literal.parse::<usize>() {
                    if idx >= array_size_cloned {
                        self.diagnostics.borrow_mut().report_array_index_out_of_bounds(
                            &index_span,
                            array_size_cloned.to_string(),
                            &object_span,
                        );
                    }
                }
                
                current_type = element_type_cloned;
            }
            _ => {
                // Error: trying to index a non-array type
                self.diagnostics.borrow_mut().report_cannot_index_type(&current_type, &object_span);
                current_type = Type::Error;
            }
        }
        
        ast.set_type(expr.id, current_type);
    }

    fn visit_tuple_expression(&mut self, ast: &mut Ast, tuple_expression: &TupleExpression, expr: &Expression) {
        for element in &tuple_expression.elements {
            self.visit_expression(ast, *element);
        }

        let element_types: Vec<Type> = tuple_expression.elements.iter()
            .map(|element_id| {
                let element = ast.query_expression(*element_id);
                element.ty.clone()
            })
            .collect();

        let tuple_type = Type::tuple(element_types);
        ast.set_type(expr.id, tuple_type);
    }

    fn visit_field_expression(&mut self, ast: &mut Ast, field_expression: &FieldExpression, expr: &Expression) {
        self.visit_expression(ast, field_expression.object);
        
        let target_obj = ast.query_expression(field_expression.object);
        let mut current_type = target_obj.ty.clone();
        let target_type_str = format!("{}", current_type);
        let target_span = target_obj.span(ast);
        let should_visit_field = match &current_type {
            Type::Object(object_type) if matches!(object_type.kind, ObjectKind::Struct(_)) => false,
            _ => true,
        };
        
        if should_visit_field {
            self.visit_expression(ast, field_expression.field.idx_no);
        }

        let field_expr = ast.query_expression(field_expression.field.idx_no);
        let field_span = field_expr.span(ast);
        let field_expr_kind = field_expr.kind.clone();

        match &current_type {
            Type::Object(object_type) if matches!(object_type.kind, ObjectKind::Tuple) => {
                // Tuple field access
                let index_ty = field_expr.ty.clone();
                let index_literal = field_span.literal.clone();

                self.expect_index_type(Type::Usize, &index_ty, &field_span, false);

                let tuple_size = object_type.fields.len();

                // Compile-time bounds checking for constant indices
                if let Ok(idx) = index_literal.parse::<usize>() {
                    if idx >= tuple_size {
                        self.diagnostics.borrow_mut().report_tuple_unknown_field(
                            &field_span,
                            target_type_str,
                        );
                        current_type = Type::Error;
                    } else {
                        current_type = object_type.fields[idx].ty.as_ref().clone();
                    }
                };
            }
            Type::Object(object_type) if matches!(object_type.kind, ObjectKind::Struct(_)) => {
                let field_name = match &field_expr_kind {
                    ExpressionKind::Variable(var_expr) => {
                        var_expr.identifier.span.literal.clone()
                    }
                    _ => {
                        self.diagnostics.borrow_mut().report_invalid_field_kind(
                            format!("{:?}", field_expr_kind),
                            &field_span
                        );
                        field_span.literal.clone()
                    }
                };
                
                // For struct types, use the concrete field types from the object instance
                // instead of looking up the generic definition
                if let Some(field_info) = object_type.fields.iter().find(|f| {
                    if let Some(ref name) = f.name {
                        *name == field_name
                    } else {
                        false
                    }
                }) {
                    current_type = field_info.ty.as_ref().clone();
                } else {
                    // Field not found in the instantiated type, report error
                    self.diagnostics.borrow_mut().report_unknown_field_in_object(
                        field_name,
                        target_type_str,
                        &field_span,
                    );

                    current_type = Type::Error;
                }
            }
            _ => {
                self.diagnostics.borrow_mut().report_no_fields_to_access(&current_type, &target_span, &field_span);
                current_type = Type::Error;
            }
        }
        
        ast.set_type(expr.id, current_type);
    }

    fn visit_constant_item(&mut self, ast: &mut Ast, constant_item: &ConstantItem, _item_id: ItemIndex) {
        let identifier = constant_item.identifier.span.literal.clone();

        if identifier.chars().any(|c| c.is_lowercase()) {
            self.diagnostics.borrow_mut().warn_non_upper_case(&identifier, &constant_item.identifier.span);
        }

        let mut ty = self.resolve_type_from_annotation(&constant_item.type_annotation);
        if matches!(ty, Type::Array(_, _)) {
            self.expected_array_type = Some(ty.clone());
        }

        if constant_item.expr.is_some() {
            let const_item_expr = **constant_item.expr.as_ref().unwrap();
            self.visit_expression(ast, const_item_expr);
            let initialiser_expression = &ast.query_expression(const_item_expr);

            self.expected_array_type = None;
    
            ty = self.expect_type(ty.clone(), &initialiser_expression.ty, &initialiser_expression.span(&ast));
        }

        self.scopes.global_scope.declare_variable(&identifier, ty, true, false);
    }

    fn visit_struct_item(&mut self, ast: &mut Ast, _generics: &Generics, _variant_data: &VariantData, item_id: ItemIndex) {
        let item = ast.query_item(item_id).clone();
        match &item.kind {
            ItemKind::Struct(name, _, _) => {
                let struct_name = &name.span.literal;
                if !struct_name.chars().next().unwrap().is_uppercase() || struct_name.contains('_') {
                    self.diagnostics.borrow_mut().warn_non_upper_camel_case(struct_name, &name.span);
                }
            }
            _ => {
                // This should never happen
                bug_report!("Internal compiler error: Expected struct item");
            }
        }
        let is_local_struct = self.scopes.is_inside_local_scope();
        
        if !is_local_struct && self.visited_local_items.contains(&item_id) {
            return;
        }
        
        if is_local_struct {
            self.visited_local_items.insert(item_id);
            
            let scoped_item = self.create_scoped_struct_item(item);
            match self.scopes.declare_local_struct(scoped_item) {
                Ok(_struct_idx) => {
                    // Local struct successfully registered in local scope
                },
                Err(existing_idx) => {
                    let duplicate = self.scopes.global_scope.get_struct(existing_idx);

                    match &duplicate.kind {
                        ItemKind::Struct(name, _, _) => {
                            let duplicate_name = &name.span.literal;
                            self.diagnostics.borrow_mut().report_duplicate_local_struct(duplicate_name.to_string(), &name.span);
                        },
                        _ => {
                            // This should never happen
                            bug_report!("Internal compiler error: Expected struct item");
                        }
                    }
                }
            }
        } else {
            match self.scopes.global_scope.declare_struct(item) {
                Ok(_struct_idx) => {
                    // Global struct successfully registered
                },
                Err(existing_idx) => {
                    let duplicate = self.scopes.global_scope.get_struct(existing_idx);

                    match &duplicate.kind {
                        ItemKind::Struct(name, _, _) => {
                            let duplicate_name = &name.span.literal;
                            self.diagnostics.borrow_mut().report_duplicate_global_struct(duplicate_name.to_string(), &name.span);
                        },
                        _ => {
                            // This should never happen
                            bug_report!("Internal compiler error: Expected struct item");
                        }
                    }
                }
            }
        }
    }

    fn visit_struct_expression(&mut self, ast: &mut Ast, struct_expression: &StructExpression, expr: &Expression) {
        let struct_name = &struct_expression.identifier.span.literal;
        let mut field_types: Vec<(String, Type)> = Vec::new();
        
        if let Some(ref_struct_idx) = self.scopes.lookup_struct_with_local(struct_name) {
            let ref_struct = self.scopes.global_scope.get_struct(ref_struct_idx).clone();

            match &ref_struct.kind {
                ItemKind::Struct(identifier, generics, variant_data) => {
                    match variant_data {
                        VariantData::Struct { fields: struct_fields } => {
                            for expr_field in &struct_expression.fields {
                                self.visit_expression(ast, expr_field.expr.id);
                            }

                            // Generic param type inference
                            let mut generic_substitutions = std::collections::HashMap::new();
                            
                            if !generics.is_empty() {
                                for struct_field in struct_fields {
                                    if let Some(field_name) = &struct_field.identifier {
                                        if let Some(expr_field) = struct_expression.fields.iter()
                                            .find(|f| f.identifier.span.literal == field_name.span.literal) {
                                            
                                            let field_expr_ty = &ast.query_expression(expr_field.expr.id).ty;
                                            
                                            if let TypeKind::Simple { type_name } = &*struct_field.ty {
                                                if generics.params.iter().any(
                                                    |param| param.identifier.span.literal == type_name.span.literal
                                                ) {
                                                    generic_substitutions.insert(
                                                        type_name.span.literal.clone(), field_expr_ty.clone()
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            
                            // Type substitution
                            for struct_field in struct_fields {
                                if let Some(field_name) = &struct_field.identifier {
                                    if let Some(expr_field) = struct_expression.fields.iter()
                                        .find(|f| f.identifier.span.literal == field_name.span.literal) {
                                        
                                        let field_expr_ty = &ast.query_expression(expr_field.expr.id).ty;
                                        field_types.push((field_name.span.literal.clone(), field_expr_ty.clone()));

                                        // Type check the field expression against the struct field type
                                        let expected_field_type = if let TypeKind::Simple { type_name } = &*struct_field.ty {
                                            if let Some(inferred_type) = generic_substitutions.get(&type_name.span.literal) {
                                                inferred_type.clone()
                                            } else {
                                                self.resolve_type_kind(&struct_field.ty)
                                            }
                                        } else {
                                            self.resolve_type_kind(&struct_field.ty)
                                        };
                                        
                                        self.expect_type(expected_field_type, field_expr_ty, &expr_field.expr.span(ast));
                                    } else {
                                        self.diagnostics.borrow_mut().report_unknown_field_in_object(
                                            field_name.span.literal.clone(),
                                            struct_name.to_string(),
                                            &struct_expression.identifier.span.clone()
                                        );
                                    }
                                }
                            }
                            
                            // Check for extra fields in the expression that don't exist in the struct
                            for expr_field in &struct_expression.fields {
                                let field_exists = struct_fields.iter().any(|sf| {
                                    if let Some(sf_name) = &sf.identifier {
                                        sf_name.span.literal == expr_field.identifier.span.literal
                                    } else {
                                        false
                                    }
                                });
                                
                                if !field_exists {
                                    self.diagnostics.borrow_mut().report_unknown_field_in_object(
                                        expr_field.identifier.span.literal.clone(),
                                        struct_name.to_string(),
                                        &expr_field.identifier.span
                                    );
                                }
                            }

                            let struct_type = Type::struct_resolved(identifier.span.literal.to_string(), field_types);
                            ast.query_expression_mut(expr.id).ty = struct_type;
                        }
                    }
                }
                _ => {
                    bug_report!("Internal compiler error: Expected struct item");
                }
            }
        } else {
            self.diagnostics.borrow_mut().report_undefined_struct(struct_name.to_string(), &struct_expression.identifier.span);
        }
    }

    fn visit_error(&mut self, _ast: &mut Ast, _span: &TextSpan) {

    }
}

impl Resolver {
    /// Check if the index expression represents a negative number (like -1, -5, etc.)
    fn check_for_negative_array_index(&self, ast: &Ast, index_expr: &Expression, index_span: &TextSpan) -> bool {
        match &index_expr.kind {
            ExpressionKind::Unary(unary_expr) => {
                // Check if this is a negation of a positive number
                if matches!(unary_expr.operator.kind, UnaryOpKind::Negation) {
                    let operand = ast.query_expression(unary_expr.operand);
                    match &operand.kind {
                        ExpressionKind::Number(_) | ExpressionKind::Usize(_) => {
                            self.diagnostics.borrow_mut().report_negative_array_index(index_span);
                            true
                        }
                        _ => false
                    }
                } else {
                    false
                }
            }
            ExpressionKind::Number(number_expr) => {
                if number_expr.number < 0 {
                    self.diagnostics.borrow_mut().report_negative_array_index(index_span);
                    true
                } else {
                    false
                }
            }
            _ => {
                false
            }
        }
    }

    fn assignment_to_binary_op(&self, op_kind: AssignmentOpKind) -> BinaryOpKind {
        match op_kind {
            AssignmentOpKind::PlusAs => BinaryOpKind::Plus,
            AssignmentOpKind::MinusAs => BinaryOpKind::Minus,
            AssignmentOpKind::MultiplyAs => BinaryOpKind::Multiply,
            AssignmentOpKind::DivideAs => BinaryOpKind::Divide,
            AssignmentOpKind::ModuloAs => BinaryOpKind::Modulo,
            AssignmentOpKind::BitwiseAndAs => BinaryOpKind::BitwiseAnd,
            AssignmentOpKind::BitwiseOrAs => BinaryOpKind::BitwiseOr,
            AssignmentOpKind::BitwiseXorAs => BinaryOpKind::BitwiseXor,
            AssignmentOpKind::ShiftLeftAs => BinaryOpKind::ShiftLeft,
            AssignmentOpKind::ShiftRightAs => BinaryOpKind::ShiftRight,
        }
    }

    fn desugared_token(&self, token: &Token) -> Token {
        let desugared_kind = token.kind.to_non_assignment()
            .expect("Token should be an assignment operator");
        
        let literal = format!("{}", desugared_kind);
        
        let start = token.span.start;
        let end = start + literal.len();
        
        Token {
            kind: desugared_kind,
            span: TextSpan {
                start,
                end,
                literal,
            },
        }
    }

    fn create_synthetic_equals_token(&self, identifier_token: &Token) -> Token {
        Token {
            kind: TokenKind::Equals,
            span: identifier_token.span.clone(),
        }
    }

    /// Create a scoped struct item to avoid name conflicts in local scopes
    fn create_scoped_struct_item(&self, mut item: Item) -> Item {
        if let Some(function_idx) = self.scopes.surrounding_function_idx() {
            if let crate::ast::ItemKind::Struct(ref mut name, generics, variant_data) = item.kind {
                let function_name = &self.scopes.global_scope.functions.get(function_idx).name;
                let scoped_name = format!("{}::{}", function_name, name.span.literal);
                let mut scoped_token = name.clone();
                scoped_token.span.literal = scoped_name;
                
                item.kind = crate::ast::ItemKind::Struct(scoped_token, generics, variant_data);
            }
        }
        item
    }
}

pub struct CompilationUnit {
    pub ast: Ast,
    pub diagnostics_report: DiagnosticsReportCell,
    pub global_scope: GlobalScope,
}

impl CompilationUnit {
    pub fn compile(input: &str) -> Result<CompilationUnit, DiagnosticsReportCell> {
        let text = text::SourceText::new(input.to_string());

        // lexer
        let mut lexer = Lexer::new(input);
        let mut tokens = Vec::new();

        while let Some(token) = lexer.next_token() {
            tokens.push(token);
        }

        // parser & ast
        let mut global_scope = GlobalScope::new(); // defining global scope
        let diagnostics_report: DiagnosticsReportCell = Rc::new(RefCell::new(diagnostics::DiagnosticsReport::new()));
        let mut ast = Ast::new();
        let mut parser = Parser::new(
            tokens, 
            Rc::clone(&diagnostics_report),
            &mut ast,
            &mut global_scope,
        );

        parser.parse();

        // error handling
        Self::check_error_diagnostics(&text, &diagnostics_report).map_err(|_| Rc::clone(&diagnostics_report))?;

        // symbol check
        let scopes = ScopeStack::from_global_scope(global_scope);
        let mut resolver = Resolver::new(Rc::clone(&diagnostics_report), scopes);
        resolver.resolve(&mut ast);

        ast.visualise();

        Self::check_error_diagnostics(&text, &diagnostics_report).map_err(|_| Rc::clone(&diagnostics_report))?;
        
        // Resolve struct types from unresolved to resolved indices
        let _ = resolver.scopes.global_scope.resolve_struct_types();

        Ok(CompilationUnit {
            global_scope: resolver.scopes.global_scope,
            ast, 
            diagnostics_report,
        })
    }

    pub fn maybe_run_compiler(&mut self) {
        if self.diagnostics_report.borrow().errors.len() > 0 {
            return;
        }

        self.run_compiler();
    }

    pub fn run_compiler(&mut self) {
        // evaluator (temp)
        let mut eval = ASTEvaluator::new(&self.global_scope);
        let main_function_ref = self.global_scope.lookup_fx("main");

        if let Some(function) = main_function_ref {
            let function = self.global_scope.functions.get(function);
            for statement in &*function.body {
                if eval.returned {
                    eval.returned = false;
                    break;
                }
                eval.visit_statement(&mut self.ast, *statement);
            }
        } else {
            self.ast.visit(&mut eval);
        }

        println!("Result: {:?}\n", eval.last_value);
    }

    fn check_error_diagnostics(text: &text::SourceText, diagnostics_report: &DiagnosticsReportCell) -> Result<(), ()> {
        let diagnostics_binding = diagnostics_report.borrow();
        
        if diagnostics_binding.errors.len() > 0 {
            let diagnostics_printer = DiagnosticsPrinter::new(text, &diagnostics_binding.errors);
            diagnostics_printer.print_error();
            return Err(());
        }

        Ok(())
    }

    pub fn output_warnings(text: &text::SourceText, diagnostics_report: &DiagnosticsReportCell) {
        let diagnostics_binding = diagnostics_report.borrow();

        if diagnostics_binding.warnings.len() > 0 {
            let diagnostics_printer = DiagnosticsPrinter::new(text, &diagnostics_binding.warnings);
            diagnostics_printer.print_warning();
            println!("");
        }
    }
}