use snowflake_common::{bug_report, idx, Idx, IndexVec};
use snowflake_common::typings::{FieldType, ObjectKind, ObjectType, TypeKind};

use crate::ast::{ArrayExpression, AssignExpression, AssignmentOpKind, AssociatedItemKind, Ast, AstType, BinaryExpression, BinaryOp, BinaryOpKind, BlockExpression, BoolExpression, BreakExpression, CallExpression, CompoundBinaryExpression, ConstStatement, ConstantItem, ContinueExpression, EnumDefinition, Expression, ExpressionKind, FieldExpression, FloatExpression, FxDeclaration, GenericParam, GenericParamKind, Generics, IfExpression, Impl, IndexExpression, Item, ItemIndex, ItemKind, LetStatement, MethodCallExpression, Mutability, NumberExpression, ParenExpression, Path, PathExpression, PathSegment, Pattern, PatternKind, ReturnExpression, Statement, StatementKind, StaticTypeAnnotation, StringExpression, StructExpression, TupleExpression, UnaryExpression, UnaryOpKind, UsizeExpression, VariantData, WhileExpression};
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
    pub body: BlockExpression,
    pub return_type: TypeKind,
}

#[derive(Debug, Clone)]
pub struct Variable {
    pub name: Path,
    pub ty: TypeKind,
    pub is_shadowing: bool,
    pub is_mutable: bool,
}

#[derive(Debug, Clone)]
pub struct EnumInfo {
    pub id: ItemIndex,
    pub name: String,
    pub variants: Vec<VariantInfo>,
}

#[derive(Debug, Clone)]
pub struct VariantInfo {
    pub discriminant: usize,
    pub name: String,
    pub data: VariantData,
}

pub struct GlobalScope {
    pub variables: IndexVec<VariableIndex, Variable>,
    pub functions: IndexVec<ItemIndex, Function>,
    pub structs: IndexVec<ItemIndex, Item<ItemKind>>,
    pub global_variables: Vec<VariableIndex>,
    pub enums: IndexVec<ItemIndex, EnumInfo>,
    pub impls: IndexVec<ItemIndex, Impl>,
    pub methods: HashMap<String, HashMap<String, ItemIndex>>, // type_name -> method_name -> function_index
}

impl GlobalScope {
    fn new() -> Self {
        GlobalScope {
            variables: IndexVec::new(),
            functions: IndexVec::new(),
            structs: IndexVec::new(),
            global_variables: Vec::new(),
            enums: IndexVec::new(),
            impls: IndexVec::new(),
            methods: HashMap::new(),
        } 
    }

    pub fn declare_variable(&mut self, identifier: &Path, ty: TypeKind, is_global: bool, is_shadowing: bool, is_mutable: bool) -> VariableIndex {
        let variable = Variable { name: identifier.clone(), ty, is_shadowing, is_mutable };
        let variable_index = self.variables.push(variable);

        if is_global {
            self.global_variables.push(variable_index);
        }

        variable_index
    }

    fn lookup_global_variable(&self, identifier: &Path) -> Option<VariableIndex> {
        self.global_variables.iter().rev()
            .map(|variable_index| (*variable_index, self.variables.get(*variable_index)))
            .find(|(_, variable)| variable.name == *identifier)
            .map(|(variable_index, _) | variable_index)
    }

    pub fn lookup_global_variable_by_path(&self, identifier: &Path) -> Option<VariableIndex> {
        self.lookup_global_variable(identifier)
    }

    pub fn lookup_variable_by_path(&self, identifier: &Path) -> Option<VariableIndex> {
        // Iterate in reverse to find the most recent declaration (for shadowing)
        self.variables.cloned_indices()
            .into_iter()
            .rev()
            .find(|idx| {
                let variable = self.variables.get(*idx);
                variable.name == *identifier
            })
    }

    pub fn create_function(&mut self, identifier: String, function_body: BlockExpression, parameters: Vec<VariableIndex>, return_type: TypeKind) -> Result<ItemIndex, ItemIndex> {
        if let Some(existing_fx_idx) = self.lookup_fx(&identifier) {
            return Err(existing_fx_idx);
        }

        let function = Function { name: identifier, parameters: parameters, body: function_body, return_type };
        return Ok(self.functions.push(function));
    }

    fn set_variable_type(&mut self, var_idx: VariableIndex, ty: TypeKind) {
        self.variables[var_idx].ty = ty;
    }

    pub fn get_variable_type(&self, var_idx: &VariableIndex) -> Option<TypeKind> {
        Some(self.variables.get(*var_idx).ty.clone())
    }

    pub fn lookup_fx(&self, identifier: &str) -> Option<ItemIndex> {
        self.functions.indexed_iter().find(|(_, function)| function.name == identifier).map(|(idx, _)| idx)
    }

    pub fn declare_struct(&mut self, item: Item<ItemKind>) -> Result<ItemIndex, ItemIndex> {
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

    pub fn get_struct(&self, struct_idx: ItemIndex) -> &Item<ItemKind> {
        self.structs.get(struct_idx)
    }
    
    /// Convert a resolved struct type back to StructIndex
    pub fn struct_index_from_resolved(&self, resolved_index: u32) -> ItemIndex {
        ItemIndex::new(resolved_index as usize)
    }

    

    pub fn declare_enum(&mut self, name: String, item: &Item<ItemKind>, variants: Vec<VariantInfo>) -> Result<ItemIndex, ItemIndex> {
        if let Some(existing_enum_idx) = self.lookup_enum(&name) {
            return Err(existing_enum_idx);
        }

        let enum_info = EnumInfo {
            id: item.id,
            name,
            variants,
        };

        Ok(self.enums.push(enum_info))
    }

    pub fn lookup_enum(&self, identifier: &str) -> Option<ItemIndex> {
        self.enums.indexed_iter()
            .find(|(_, enum_info)| enum_info.name == identifier)
            .map(|(idx, _)| idx)
    }

    pub fn get_enum(&self, idx: ItemIndex) -> &EnumInfo {
        self.enums.get(idx)
    }

    pub fn lookup_enum_variant(&self, enum_name: &str, variant_name: &str) -> Option<(ItemIndex, &VariantInfo)> {
        self.enums.indexed_iter()
            .find(|(_, enum_info)| enum_info.name == enum_name)
            .and_then(|(enum_idx, enum_info)| {
                enum_info.variants.iter()
                    .find(|variant| variant.name == variant_name)
                    .map(|variant| (enum_idx, variant))
            }
        )
    }

    /// Register a method for a type
    pub fn register_method(&mut self, type_name: &str, method_name: &str, fx_idx: ItemIndex) {
        self.methods
            .entry(type_name.to_string())
            .or_insert_with(HashMap::new)
            .insert(method_name.to_string(), fx_idx);
    }

    /// Look up a method by type name and method name
    pub fn lookup_method(&self, type_name: &str, method_name: &str) -> Option<ItemIndex> {
        self.methods
            .get(type_name)?
            .get(method_name)
            .copied()
    }

    pub fn lookup_type_from_method(&self, fx_idx: ItemIndex) -> Option<String> {
        for (type_name, methods) in &self.methods {
            for (_method_name, method_fx_idx) in methods {
                if *method_fx_idx == fx_idx {
                    return Some(type_name.clone());
                }
            }
        }

        None
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

    fn declare_variable(&mut self, identifier: &Path, ty: TypeKind, is_mutable: bool) -> VariableIndex {
        let is_inside_global_scope = self.is_inside_local_scope();
        let index = self._declare_variable(identifier, ty, !is_inside_global_scope, is_mutable);

        if is_inside_global_scope {
            self.current_local_scope_mut().add_local_var(index);
        }

        return index;
    }

    fn _declare_variable(&mut self, identifier: &Path, ty: TypeKind, is_global: bool, is_mutable: bool) -> VariableIndex {
        let is_shadowing = match self.current_local_scope() {
            None => false,
            Some(scope) => scope.locals.iter().any(|local| {
                let local = self.global_scope.variables.get(*local);
                local.name == *identifier
            }),
        };

        self.global_scope.declare_variable(identifier, ty, is_global, is_shadowing, is_mutable)
    }

    fn lookup_variable(&mut self, identifier: &Path) -> Option<VariableIndex> { // top-down lookup
        for scope in self.local_scopes.iter_mut().rev() {
            if let Some((index, _variable)) = scope.locals.iter() // loop local var idxs
                .map(|idx| (*idx, self.global_scope.variables.get(*idx))) // lookup idx in global_scope
                .find(|(_idx, variable)| variable.name == *identifier) { // use name to lookup var

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

    fn declare_local_struct(&mut self, item: Item<ItemKind>) -> Result<ItemIndex, ItemIndex> {
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
    expected_array_type: Option<TypeKind>, // Track expected array type for better error reporting
    visited_local_items: std::collections::HashSet<ItemIndex>,
    current_impl_type: Option<String>, // Track the type being implemented for Self resolution
    current_function: Option<String>, // Track the current function for nested function resolution
}

fn expect_type(diagnostics: &DiagnosticsReportCell, expected: TypeKind, actual: &TypeKind, span: &TextSpan) -> TypeKind {
    // Allow generic types and unresolved types to pass through without checking
    if matches!(expected, TypeKind::Generic(_) | TypeKind::Unresolved) || 
       matches!(actual, TypeKind::Generic(_) | TypeKind::Unresolved) {
        return expected;
    }
    
    // Implicit conversion from Int to Usize
    let is_compatible = actual.is_assignable_to(&expected) || 
                       (matches!(expected, TypeKind::Usize) && matches!(actual, TypeKind::Int));
    
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
            current_impl_type: None,
            current_function: None,
        }
    }

    fn expect_type(&self, expected: TypeKind, actual: &TypeKind, span: &TextSpan) -> TypeKind {
        expect_type(&self.diagnostics, expected, actual, span)
    }

    fn expect_index_type(&self, expected: TypeKind, actual: &TypeKind, span: &TextSpan, is_neg_idx: bool) {
        // Implicit conversion from Int to Usize for array indexing
        let is_compatible = actual.is_assignable_to(&expected) || 
                           (matches!(expected, TypeKind::Usize) && matches!(actual, TypeKind::Int));
        
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
        // Pass 0: Register all structs and enums in global scope
        for id in ast.items.cloned_indices() {
            let item = ast.query_item(id).clone();
            if item.is_local {
                continue;
            }
            
            match &item.kind {
                ItemKind::Struct(_, _, _) => {
                    match self.scopes.global_scope.declare_struct(item.clone()) {
                        Ok(_) => {},
                        Err(_existing_idx) => {
                            // Duplicate will be handled during visit_struct_item
                        }
                    }
                }
                ItemKind::Enum(name, _, definition) => {
                    let variants = definition.variants.iter().enumerate().map(|(idx, v)| {
                        VariantInfo {
                            discriminant: idx,
                            name: v.identifier.span.literal.clone(),
                            data: v.data.clone(),
                        }
                    }).collect();
                    
                    let _ = self.scopes.global_scope.declare_enum(
                        name.span.literal.clone(),
                        &item,
                        variants
                    );
                }
                _ => {}
            }
        }
        
        // First pass: resolve all function signatures (return types and parameter types)
        for id in ast.items.cloned_indices() {
            let item = ast.query_item(id).clone();
            if item.is_local {
                continue;
            }
            
            match &item.kind {
                ItemKind::Function(fx_decl) => {
                    let fx_idx = fx_decl.index;
                    
                    let return_type = if fx_decl.return_type.is_some() {
                        self.resolve_ast_type(&fx_decl.return_type.as_ref().unwrap().ty)
                    } else {
                        TypeKind::Void
                    };
                    
                    let mut param_updates = Vec::new();
                    let function = self.scopes.global_scope.functions.get(fx_idx);
                    for (param_idx, generic_param) in fx_decl.generics.params.iter().enumerate() {
                        if param_idx < function.parameters.len() {
                            let param_var_idx = function.parameters[param_idx];
                            
                            let resolved_type = match &generic_param.kind {
                                GenericParamKind::Type { ty, .. } => {
                                    self.resolve_ast_type(&ty)
                                }
                                GenericParamKind::Const { ty, .. } => {
                                    self.resolve_ast_type(&ty)
                                }
                            };
                            
                            param_updates.push((param_var_idx, resolved_type));
                        }
                    }
                    
                    let function = self.scopes.global_scope.functions.get_mut(fx_idx);
                    function.return_type = return_type;
                    
                    for (param_var_idx, resolved_type) in param_updates {
                        let param_var = self.scopes.global_scope.variables.get_mut(param_var_idx);
                        param_var.ty = resolved_type;
                    }
                }
                _ => {
                    // Other items will be processed in the second pass
                }
            }
        }
        
        // Second pass: visit all items
        for id in ast.items.cloned_indices() {
            let item = ast.query_item(id);
            if item.is_local {
                continue;
            }
            self.visit_item(ast, id);
        }
    }

    pub fn resolve_binary_expression(&self, ast: &Ast, left: &Expression, right: &Expression, operator: &BinaryOpKind) -> TypeKind {
        let left_ty = &left.ty;
        let right_ty = &right.ty;
        
        let result_type = match operator {
            BinaryOpKind::Equals | BinaryOpKind::NotEquals | 
            BinaryOpKind::LessThan | BinaryOpKind::GreaterThan | 
            BinaryOpKind::LessThanOrEqual | BinaryOpKind::GreaterThanOrEqual => {
                self.expect_type(left_ty.clone(), right_ty, &right.span(&ast));
                TypeKind::Bool
            },
            BinaryOpKind::LogicalAnd | BinaryOpKind::LogicalOr => {
                self.expect_type(TypeKind::Bool, left_ty, &left.span(&ast));
                self.expect_type(TypeKind::Bool, right_ty, &right.span(&ast));
                TypeKind::Bool
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
                self.expect_type(TypeKind::Int, left_ty, &left.span(&ast));
                self.expect_type(TypeKind::Int, right_ty, &right.span(&ast));
                TypeKind::Int
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

    pub fn resolve_compound_binary_expression(&self, ast: &Ast, left: &Expression, right: &Expression, operator: &AssignmentOpKind) -> TypeKind {
        // First, validate that the left-hand side is a valid l-value (variable)
        // If it's not, we'll let the type checker catch it when we return void
        // This will generate errors like "binary operation '+=' cannot be applied to type 'int' and 'void'"
        match &left.kind {
            ExpressionKind::Path(_) => {
                // Valid l-value, proceed with normal type checking
                let type_matrix: (TypeKind, TypeKind) = match operator {
                    AssignmentOpKind::PlusAs | AssignmentOpKind::MinusAs | 
                    AssignmentOpKind::MultiplyAs | AssignmentOpKind::DivideAs => (TypeKind::Int, TypeKind::Int),
                    AssignmentOpKind::ModuloAs | AssignmentOpKind::BitwiseAndAs | 
                    AssignmentOpKind::BitwiseOrAs | AssignmentOpKind::BitwiseXorAs | 
                    AssignmentOpKind::ShiftLeftAs | AssignmentOpKind::ShiftRightAs => (TypeKind::Int, TypeKind::Int),
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
                    AssignmentOpKind::ShiftLeftAs | AssignmentOpKind::ShiftRightAs => TypeKind::Int,
                };
                
                self.expect_type(expected_right_type, &right.ty, &right.span(&ast));
            }
        }

        TypeKind::Void
    }

    pub fn resolve_unary_expression(&self, ast: &Ast, operand: &Expression, operator: &UnaryOpKind) -> TypeKind {
        let type_matrix: (TypeKind, TypeKind) = match operator {
            UnaryOpKind::Negation => (TypeKind::Int, TypeKind::Int),
            UnaryOpKind::BitwiseNot => (TypeKind::Int, TypeKind::Int),
        };

        self.expect_type(type_matrix.0, &operand.ty, &operand.span(&ast));

        type_matrix.1
    }

    /// Resolve type from annotation with scope awareness
    pub fn resolve_type_from_annotation(&self, type_annotation: &StaticTypeAnnotation) -> TypeKind {
        match &type_annotation.type_kind {
            AstType::Array { element_type, length, .. } => {
                let resolved_element_type = self.resolve_ast_type(element_type);
                let length_str = &length.span.literal;
                match length_str.parse::<usize>() {
                    Ok(len) => TypeKind::Array(Box::new(resolved_element_type), len),
                    Err(_) => {
                        // TODO: Proper reporting of wrong array len
                        self.diagnostics.borrow_mut().report_undeclared_type(length);
                        TypeKind::Error
                    }
                }
            },
            AstType::Slice { element_type, .. } => {
                let _resolved_element_type = self.resolve_ast_type(element_type);
                // TODO: Implement slices
                TypeKind::Error
            },
            AstType::Simple { type_name } => {
                self.resolve_type_from_string(type_name)
            }
            AstType::Tuple { element_types, .. } => {
                let mut resolved_types = Vec::new();
                for elem_type in element_types {
                    let resolved_type = self.resolve_ast_type(elem_type);
                    resolved_types.push(resolved_type);
                }
                TypeKind::tuple(resolved_types)
            }
            AstType::Path(_, path) => {
                let ty_name = path.segments.last().unwrap().identifier.span.literal.clone();
                TypeKind::Path(None, ty_name)
            }
            _ => bug_report!("Unsupported type annotation kind {:?}", type_annotation.type_kind),
        }
    }

    /// Resolve type kind with scope awareness
    pub fn resolve_ast_type(&self, type_kind: &AstType) -> TypeKind {
        self.resolve_ast_type_with_generics(type_kind, &[])
    }

    /// Resolve type kind with generic parameter context
    fn resolve_ast_type_with_generics(&self, type_kind: &AstType, generic_params: &[GenericParam]) -> TypeKind {
        match type_kind {
            AstType::Array { element_type, length, .. } => {
                let resolved_element_type = self.resolve_ast_type_with_generics(element_type, generic_params);
                let length_str = &length.span.literal;
                match length_str.parse::<usize>() {
                    Ok(len) => TypeKind::Array(Box::new(resolved_element_type), len),
                    Err(_) => {
                        // TODO: Proper reporting of wrong array len
                        self.diagnostics.borrow_mut().report_undeclared_type(length);
                        TypeKind::Error
                    }
                }
            },
            AstType::Slice { element_type, .. } => {
                let _resolved_element_type = self.resolve_ast_type_with_generics(element_type, generic_params);
                // TODO: Implement slices
                TypeKind::Error
            },
            AstType::Simple { type_name } => {
                self.resolve_type_from_string_with_generics(type_name, generic_params)
            }
            AstType::Tuple { element_types, .. } => {
                let mut resolved_types = Vec::new();
                for elem_type in element_types {
                    let resolved_type = self.resolve_ast_type_with_generics(elem_type, generic_params);
                    resolved_types.push(resolved_type);
                }
                TypeKind::tuple(resolved_types)
            }
            AstType::Path(_, path) => {
                let ty_name = path.segments.last().unwrap().identifier.span.literal.clone();
                TypeKind::Path(None, ty_name)
            }
            AstType::ImplTrait(_, _) => {
                TypeKind::ImplTrait {
                    impl_type_name:"Placeholder".to_string(), // TODO: Implement proper impl trait resolution
                }
            }
        }
    }

    /// Resolve type from string with scope awareness for struct types
    pub fn resolve_type_from_string(&self, type_name: &Token) -> TypeKind {
        self.resolve_type_from_string_with_generics(type_name, &[])
    }

    /// Resolve type from string with generic parameter context
    fn resolve_type_from_string_with_generics(&self, type_name: &Token, generic_params: &[GenericParam]) -> TypeKind {
        let builtin_type = TypeKind::from_token(type_name);
        if !matches!(builtin_type, TypeKind::Unresolved) {
            return builtin_type;
        }

        // Handle Self type in impl blocks
        if type_name.span.literal == "Self" {
            if let Some(ref impl_type) = self.current_impl_type {
                // Recursively resolve the actual type
                let mut self_type_token = type_name.clone();
                self_type_token.span.literal = impl_type.clone();
                return self.resolve_type_from_string_with_generics(&self_type_token, generic_params);
            } else {
                self.diagnostics.borrow_mut().report_error(
                    "Self type used outside of impl block".to_string(),
                    "Self type can only be used inside impl blocks".to_string(),
                    type_name.span.clone()
                );
                return TypeKind::Error;
            }
        }

        if generic_params.iter().any(|param| param.identifier.span.literal == type_name.span.literal) {
            // This is a generic type parameter
            return TypeKind::Generic(type_name.span.literal.clone());
        }
        
        if let Some(struct_idx) = self.scopes.lookup_struct_with_local(&type_name.span.literal) {
            let struct_item = self.scopes.global_scope.get_struct(struct_idx);
            if let ItemKind::Struct(identifier, struct_generics, variant_data) = &struct_item.kind {
                match variant_data {
                    VariantData::Struct { fields } => {
                        let mut field_types = Vec::new();
                        for field in fields {
                            if let Some(field_name) = &field.identifier {
                                let field_type = self.resolve_ast_type_with_generics(&field.ty, &struct_generics.params);
                                field_types.push((field_name.span.literal.clone(), field_type));
                            }
                        }

                        return TypeKind::struct_resolved(identifier.span.literal.clone(), field_types);
                    }
                    VariantData::Tuple(elements) => {
                        let mut fields = Vec::new();
                        for element in elements {
                            let elem_type = self.resolve_ast_type_with_generics(&element.ty, &struct_generics.params);
                            fields.push(FieldType {
                                ty: Box::new(elem_type),
                                name: None,
                            });
                        }

                        return TypeKind::Object(ObjectType {
                            fields,
                            kind: ObjectKind::Struct(identifier.span.literal.clone()),
                        });
                    }
                    VariantData::Unit => {
                        return TypeKind::Unit;
                    }
                }
            }
        }
        
        // Check if it's an enum type
        if let Some(_enum_idx) = self.scopes.global_scope.lookup_enum(&type_name.span.literal) {
            return TypeKind::Enum {
                enum_name: type_name.span.literal.clone(),
                variant_name: None,
            };
        }
        
        self.diagnostics.borrow_mut().report_undeclared_type(type_name);
        TypeKind::Error
    }

    fn path_from_pattern_identifier(&self, pattern: &Pattern) -> Vec<Path> {
        match &pattern.kind {
            PatternKind::Identifier(_, token) => {
                vec![Path {
                    span: token.span.clone(),
                    segments: vec![PathSegment {
                        identifier: token.clone(),
                        arguments: None,
                    }],
                    tokens: vec![token.clone()],
                }]
            }
            PatternKind::Tuple(elements) => {
                let mut paths = Vec::new();
                for element in elements {
                    let mut element_paths = self.path_from_pattern_identifier(element);
                    paths.append(&mut element_paths);
                }
                paths
            }
            PatternKind::Struct(_, _, fields) => {
                let mut paths = Vec::new();
                for field in fields {
                    let mut field_paths = self.path_from_pattern_identifier(&field.pattern);
                    paths.append(&mut field_paths);
                }
                paths
            }
            PatternKind::TupleStruct(_, _, patterns) => {
                let mut paths = Vec::new();
                for pattern in patterns {
                    let mut pattern_paths = self.path_from_pattern_identifier(pattern);
                    paths.append(&mut pattern_paths);
                }
                paths
            }
            PatternKind::Wildcard => {
                vec![]
            }
            PatternKind::Rest => {
                vec![]
            }
            _ => todo!("Unsupported pattern kind {:?} for path extraction", pattern.kind),
        }
    }

    fn match_pattern_with_type(&self, pattern: &Pattern, ty: &TypeKind) -> Vec<(Path, TypeKind, bool)> {
        match (&pattern.kind, ty) {
            // Simple identifier pattern
            (PatternKind::Identifier(binding_mode, token), ty) => {
                let path = Path {
                    span: token.span.clone(),
                    segments: vec![PathSegment {
                        identifier: token.clone(),
                        arguments: None,
                    }],
                    tokens: vec![token.clone()],
                };

                let is_mutable = matches!(binding_mode.0, Mutability::Mutable);
                vec![(path, ty.clone(), is_mutable)]
            }
            // Tuple pattern
            (PatternKind::Tuple(elements), TypeKind::Object(obj_type)) if matches!(
                obj_type.kind,
                ObjectKind::Tuple,
            ) => {
                let has_rest = elements.iter().any(|e| matches!(e.kind, PatternKind::Rest));
                let non_rest_count = elements.iter()
                    .filter(|e| !matches!(e.kind, PatternKind::Rest))
                    .count();
                
                if !has_rest && elements.len() != obj_type.fields.len() {
                    let element_spans = TextSpan::combine(
                        elements.iter().map(|e| e.span.clone()).collect::<Vec<_>>()
                    );

                    self.diagnostics.borrow_mut().report_error(
                    format!("mismatched element count in tuple pattern"),
                        format!(
                            "Expected tuple with {} elements, found one with {} elements",
                            elements.len(), obj_type.fields.len()
                        ),
                        element_spans,
                    );

                    return vec![];
                }
                
                if has_rest && non_rest_count > obj_type.fields.len() {
                    let element_spans = TextSpan::combine(
                        elements.iter().map(|e| e.span.clone()).collect::<Vec<_>>()
                    );

                    self.diagnostics.borrow_mut().report_error(
                        format!("too many elements in tuple pattern"),
                        format!(
                            "Tuple has {} elements, but pattern specifies {} elements (plus rest pattern)",
                            obj_type.fields.len(), non_rest_count
                        ),
                        element_spans,
                    );

                    return vec![];
                }

                let mut bindings = Vec::new();
                let mut field_idx = 0;
                let mut pattern_idx = 0;
                
                while pattern_idx < elements.len() && field_idx < obj_type.fields.len() {
                    let element_pattern = &elements[pattern_idx];
                    
                    if matches!(element_pattern.kind, PatternKind::Rest) {
                        pattern_idx += 1;

                        // Calculate how many fields the rest pattern should absorb
                        let remaining_patterns = elements.len() - pattern_idx;
                        let remaining_fields = obj_type.fields.len() - field_idx;
                        if remaining_fields >= remaining_patterns {
                            field_idx += remaining_fields - remaining_patterns;
                        }
                        continue;
                    }
                    
                    let field = &obj_type.fields[field_idx];
                    let mut element_bindings = self.match_pattern_with_type(
                        element_pattern,
                        &field.ty
                    );

                    bindings.append(&mut element_bindings);
                    
                    field_idx += 1;
                    pattern_idx += 1;
                }

                bindings
            }
            // Struct pattern with resolved type
            (PatternKind::Struct(_, _, fields), TypeKind::Object(obj_type)) if matches!(
                obj_type.kind,
                ObjectKind::Struct(_),
            ) => {
                let has_rest = fields.iter().any(|f| f.identifier.kind == TokenKind::DoublePeriod);
                let non_rest_field_count = fields.iter()
                    .filter(|f| f.identifier.kind != TokenKind::DoublePeriod)
                    .count();
                
                if !has_rest && non_rest_field_count != obj_type.fields.len() {
                    let field_spans = TextSpan::combine(
                        fields.iter().map(|f| f.pattern.span.clone()).collect::<Vec<_>>()
                    );

                    self.diagnostics.borrow_mut().report_error(
                    format!("mismatched field count in struct pattern"),
                        format!(
                            "Expected struct with {} fields, found pattern with {} fields",
                            obj_type.fields.len(), non_rest_field_count
                        ),
                        field_spans,
                    );

                    return vec![];
                }
                
                if has_rest && non_rest_field_count > obj_type.fields.len() {
                    let field_spans = TextSpan::combine(
                        fields.iter().map(|f| f.pattern.span.clone()).collect::<Vec<_>>()
                    );

                    self.diagnostics.borrow_mut().report_error(
                        format!("too many fields in struct pattern"),
                        format!(
                            "Struct has {} fields, but pattern specifies {} fields (plus rest pattern)",
                            obj_type.fields.len(), non_rest_field_count
                        ),
                        field_spans,
                    );

                    return vec![];
                }

                let mut bindings = Vec::new();
                for pattern_field in fields {
                    if pattern_field.identifier.kind == TokenKind::DoublePeriod {
                        continue;
                    }
                    
                    let field_name = &pattern_field.identifier.span.literal;
                    
                    if let Some(struct_field) = obj_type.fields.iter().find(|f| {
                        f.name.as_ref() == Some(field_name)
                    }) {
                        let mut field_bindings = self.match_pattern_with_type(
                            &pattern_field.pattern,
                            &struct_field.ty
                        );
                        bindings.append(&mut field_bindings);
                    } else {
                        self.diagnostics.borrow_mut().report_error(
                            format!("unknown field in pattern"),
                            format!(
                                "Struct does not have a field named '{}'",
                                field_name
                            ),
                            pattern_field.identifier.span.clone(),
                        );
                    }
                }

                bindings
            }
            // Struct pattern with error or unresolved type
            (PatternKind::Struct(_, _, fields), TypeKind::Error | TypeKind::Unresolved) => {
                let mut bindings = Vec::new();
                for field in fields {
                    let mut field_bindings = self.match_pattern_with_type(
                        &field.pattern,
                        ty
                    );
                    bindings.append(&mut field_bindings);
                }
                bindings
            }
            // Struct pattern with enums
            (PatternKind::Struct(_, path, fields), TypeKind::Enum { enum_name, variant_name }) => {
                if let Some(variant_name) = variant_name {
                    if path.segments.last().unwrap().identifier.span.literal != *variant_name {
                        self.diagnostics.borrow_mut().report_error(
                            format!("mismatched variant name in struct pattern"),
                            format!(
                                "Expected variant '{}', found '{}'",
                                variant_name,
                                path.segments.last().unwrap().identifier.span.literal
                            ),
                            path.span.clone(),
                        );

                        return vec![];
                    }
                }

                let mut bindings = Vec::new();
                let enum_idx = self.scopes.global_scope.lookup_enum(&enum_name);
                if enum_idx.is_none() {
                    self.diagnostics.borrow_mut().report_undeclared_type(&path.segments.last().unwrap().identifier);
                    return vec![];
                }

                let enum_item = self.scopes.global_scope.get_enum(enum_idx.unwrap());
                let variant_info = enum_item.variants.iter().find(|var| var.name == path.segments.last().unwrap().identifier.span.literal);

                if variant_info.is_none() {
                    self.diagnostics.borrow_mut().mismatched_variant_name(
                        enum_name,
                        &path.segments.last().unwrap().identifier.span.literal,
                        path.span.clone(),
                    );

                    return vec![];
                }

                let variant_info = variant_info.unwrap();

                // Extract field types from the variant data
                match &variant_info.data {
                    VariantData::Struct { fields: variant_fields } => {
                        if fields.len() != variant_fields.len() {
                            for field in fields {
                                if matches!(field.pattern.kind, PatternKind::Rest) {
                                    // Allow rest pattern to absorb extra fields
                                    return vec![];
                                }
                            }

                            let field_spans = TextSpan::combine(
                                fields.iter().map(|f| f.pattern.span.clone()).collect::<Vec<_>>()
                            );

                            self.diagnostics.borrow_mut().report_error(
                                format!("mismatched field count in struct pattern"),
                                format!(
                                    "Expected variant with {} fields, found pattern with {} fields",
                                    variant_fields.len(), fields.len()
                                ),
                                field_spans,
                            );

                            return vec![];
                        }

                        // Match pattern fields with variant fields by name
                        for pattern_field in fields {
                            let field_name = &pattern_field.identifier.span.literal;
                            if let Some(variant_field) = variant_fields.iter().find(|vf| {
                                vf.identifier.as_ref().map(|id| &id.span.literal) == Some(field_name)
                            }) {
                                let field_type = self.resolve_ast_type(&variant_field.ty);
                                let mut field_bindings = self.match_pattern_with_type(
                                    &pattern_field.pattern,
                                    &field_type
                                );
                                bindings.append(&mut field_bindings);
                            } else {
                                self.diagnostics.borrow_mut().report_error(
                                    format!("unknown field in pattern"),
                                    format!(
                                        "Variant '{}' does not have a field named '{}'",
                                        variant_info.name, field_name
                                    ),
                                    pattern_field.identifier.span.clone(),
                                );
                            }
                        }
                    }
                    _ => {
                        self.diagnostics.borrow_mut().report_error(
                            format!("invalid pattern for variant"),
                            format!(
                                "Variant '{}' is not a struct variant",
                                variant_info.name
                            ),
                            path.span.clone(),
                        );
                        return vec![];
                    }
                }

                bindings
            }
            // Tuple struct pattern with resolved type
            (PatternKind::TupleStruct(_, _, fields), TypeKind::Object(obj_type)) if matches!(
                obj_type.kind,
                ObjectKind::Struct(_),
            ) => {
                if fields.len() != obj_type.fields.len() {
                    for field in fields {
                        if matches!(field.kind, PatternKind::Rest) {
                            // Allow rest pattern to absorb extra fields
                            return vec![];
                        }
                    }

                    let field_spans = TextSpan::combine(
                        fields.iter().map(|f| f.span.clone()).collect::<Vec<_>>()
                    );

                    self.diagnostics.borrow_mut().report_error(
                    format!("mismatched field count in struct pattern"),
                        format!(
                            "Expected struct with {} fields, found one with {} fields",
                            obj_type.fields.len(), fields.len()
                        ),
                        field_spans,
                    );

                    return vec![];
                }

                let mut bindings = Vec::new();
                for (element_pattern, field) in fields.iter().zip(&obj_type.fields) {
                    let mut element_bindings = self.match_pattern_with_type(
                        element_pattern,
                        &field.ty
                    );

                    bindings.append(&mut element_bindings);
                }

                bindings
            }
            // Tuple struct pattern with enums
            (PatternKind::TupleStruct(_, path, fields), TypeKind::Enum { enum_name, variant_name }) => {
                if let Some(variant_name) = variant_name {
                    if path.segments.last().unwrap().identifier.span.literal != *variant_name {
                        self.diagnostics.borrow_mut().report_error(
                            format!("mismatched variant name in tuple struct pattern"),
                            format!(
                                "Expected variant '{}', found '{}'",
                                variant_name,
                                path.segments.last().unwrap().identifier.span.literal
                            ),
                            path.span.clone(),
                        );

                        return vec![];
                    }
                }

                let mut bindings = Vec::new();
                let enum_idx = self.scopes.global_scope.lookup_enum(&enum_name);
                if enum_idx.is_none() {
                    self.diagnostics.borrow_mut().report_undeclared_type(&path.segments.last().unwrap().identifier);
                    return vec![];
                }

                let enum_item = self.scopes.global_scope.get_enum(enum_idx.unwrap());
                let variant_info = enum_item.variants.iter().find(|var| var.name == path.segments.last().unwrap().identifier.span.literal);

                if variant_info.is_none() {
                    self.diagnostics.borrow_mut().mismatched_variant_name(
                        enum_name,
                        &path.segments.last().unwrap().identifier.span.literal,
                        path.span.clone(),
                    );

                    return vec![];
                }

                let variant_info = variant_info.unwrap();

                match &variant_info.data {
                    VariantData::Tuple(elements) => {
                        if fields.len() != elements.len() {
                            for field in fields {
                                if matches!(field.kind, PatternKind::Rest) {
                                    // Allow rest pattern to absorb extra fields
                                    return vec![];
                                }
                            }

                            let field_spans = TextSpan::combine(
                                fields.iter().map(|f| f.span.clone()).collect::<Vec<_>>()
                            );

                            self.diagnostics.borrow_mut().report_error(
                                format!("mismatched field count in tuple struct pattern"),
                                format!(
                                    "Expected variant with {} fields, found pattern with {} fields",
                                    elements.len(), fields.len()
                                ),
                                field_spans,
                            );

                            return vec![];
                        }

                        for (field_pattern, element) in fields.iter().zip(elements.iter()) {
                            let element_type = self.resolve_ast_type(&element.ty);
                            let mut field_bindings = self.match_pattern_with_type(
                                field_pattern,
                                &element_type
                            );
                            bindings.append(&mut field_bindings);
                        }
                    }
                    _ => {
                        self.diagnostics.borrow_mut().report_error(
                            format!("invalid pattern for variant"),
                            format!(
                                "Variant '{}' is not a tuple variant",
                                variant_info.name
                            ),
                            path.span.clone(),
                        );
                        return vec![];
                    }
                }

                bindings
            }
            // Wildcard pattern
            (PatternKind::Wildcard, _) => {
                vec![]
            }
            // Rest pattern
            (PatternKind::Rest, _) => {
                vec![]
            }
            _ => todo!(
                "Unsupported pattern kind {:?} for type matching with type {:?}",
                pattern.kind,
                ty
            ),
        }
    }
}

impl ASTVisitor for Resolver {
    fn visit_let_statement(&mut self, ast: &mut Ast, let_statement: &LetStatement, statement: &Statement) {
        let _ = self.path_from_pattern_identifier(&let_statement.pattern);

        // Set expected array type if we have an array type annotation
        let expected_type = match &let_statement.type_annotation {
            Some(type_annotation) => {
                let ty = self.resolve_type_from_annotation(type_annotation);
                if matches!(ty, TypeKind::Array(_, _)) {
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
                
                match (&expected_ty, &initialiser_expression.ty) {
                    (TypeKind::Enum { enum_name: expected_enum, variant_name: None }, 
                     TypeKind::Enum { enum_name: init_enum, variant_name: Some(_) }) 
                        if expected_enum == init_enum => {
                        initialiser_expression.ty.clone()
                    }
                    _ => expected_ty
                }
            }
            None => initialiser_expression.ty.clone(),
        };

        let bindings = self.match_pattern_with_type(&let_statement.pattern, &ty);
        if bindings.is_empty() {
            return;
        }

        for (identifier_path, binding_ty, is_mutable) in bindings {
            let variable = self.scopes.declare_variable(&identifier_path, binding_ty, is_mutable);
            ast.set_variable_for_statement(&statement.id, variable);
        }
    }

    fn visit_const_statement(&mut self, ast: &mut Ast, const_statement: &ConstStatement, statement: &Statement) {
        let identifier = Path {
            span: const_statement.identifier.span.clone(),
            segments: vec![PathSegment {
                identifier: const_statement.identifier.clone(),
                arguments: None,
            }],
            tokens: vec![const_statement.identifier.clone()],
        };
        let identifier_string = &identifier.tokens.last().unwrap().span.literal;

        if identifier_string.chars().any(|c| c.is_lowercase()) {
            self.diagnostics.borrow_mut().warn_non_upper_case(&identifier_string, &const_statement.identifier.span);
        }
        
        let ty = self.resolve_type_from_annotation(&const_statement.type_annotation);
        if matches!(ty, TypeKind::Array(_, _)) {
            self.expected_array_type = Some(ty.clone());
        }
        
        self.visit_expression(ast, const_statement.expr);
        let initialiser_expression = &ast.query_expression(const_statement.expr);

        self.expected_array_type = None;

        let ty = self.expect_type(ty.clone(), &initialiser_expression.ty, &initialiser_expression.span(&ast));

        let variable = self.scopes.declare_variable(&identifier, ty, false);
        ast.set_variable_for_statement(&statement.id, variable);
    }

    fn visit_number_expression(&mut self, ast: &mut Ast, _number: &NumberExpression, expr: &Expression) {
        ast.set_type(expr.id, TypeKind::Int);
    }

    fn visit_float_expression(&mut self, ast: &mut Ast, _float: &FloatExpression, expr: &Expression) {
        ast.set_type(expr.id, TypeKind::Float);
    }

    fn visit_usize_expression(&mut self, ast: &mut Ast, _number: &UsizeExpression, expr: &Expression) {
        ast.set_type(expr.id, TypeKind::Usize);
    }

    fn visit_string_expression(&mut self, ast: &mut Ast, _string: &StringExpression, expr: &Expression) {
        ast.set_type(expr.id, TypeKind::String);
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
            ExpressionKind::Path(path_expr) => {
                // Valid assignment target - perform desugaring
                // Transform `a += b` into `a = (a + b)`
                let ty = self.resolve_compound_binary_expression(ast, &left, &right, &compound_expression.operator);
                
                let var_identifier = path_expr.path.tokens.last().unwrap().clone();
                let var_idx = match self.scopes.lookup_variable(&path_expr.path) {
                    Some(idx) => idx,
                    None => {
                        // Should not happen
                        self.diagnostics.borrow_mut().report_undeclared_item(
                            &path_expr.path.span.literal,
                            &path_expr.path.span
                        );
                        ast.set_type(expr.id, TypeKind::Error);
                        return;
                    }
                };
                
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
                let assignment_expr = AssignExpression {
                    lhs: left_expr_id,
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
                ast.set_type(expr.id, TypeKind::Void);
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
                _ => TypeKind::Void,
            }
        }).unwrap_or(TypeKind::Void);
        ast.set_type(expr.id, ty);
    }

    fn visit_boolean_expression(&mut self, ast: &mut Ast, _boolean: &BoolExpression, expr: &Expression) {
        ast.set_type(expr.id, TypeKind::Bool);
    }

    fn visit_if_expression(&mut self, ast: &mut Ast, if_statement: &IfExpression, expr: &Expression) {
        self.scopes.enter_scope();
        self.visit_expression(ast, if_statement.condition);

        // conditional expression type check
        let conditional_expression = ast.query_expression(if_statement.condition);
        self.expect_type(TypeKind::Bool, &conditional_expression.ty, &conditional_expression.span(&ast));

        self.visit_block_expression(ast, &if_statement.then_branch, expr);
        let mut ty = TypeKind::Void;
        self.scopes.exit_scope();

        if let Some(else_branch) = &if_statement.else_branch {
            self.scopes.enter_scope();

            self.visit_expression(ast, *else_branch);
            let else_expr = ast.query_expression(*else_branch);

            let then_expression_type = if_statement.then_branch.type_or_void(ast);
            let else_expression_type = match &else_expr.kind {
                ExpressionKind::Block(block_expr) => block_expr.type_or_void(ast),
                _ => else_expr.ty.clone(),
            };

            
            // Only perform type unification if both branches return non-void types
            if !matches!(then_expression_type, TypeKind::Void) && !matches!(else_expression_type, TypeKind::Void) {
                let else_span = else_expr.span(ast);
                ty = self.expect_type(then_expression_type, &else_expression_type, &else_span);
            } else {
                ty = TypeKind::Void;
            }

            self.scopes.exit_scope();
        }

        ast.set_type(expr.id, ty);
    }
    
    fn visit_fx_decl(&mut self, ast: &mut Ast, fx_decl: &FxDeclaration, _item_id: ItemIndex) {
        let fx_idx = fx_decl.index;

        self.scopes.enter_fx_scope(fx_idx);

        // Save and set current function context for nested function resolution
        let prev_function = self.current_function.take();
        let function = self.scopes.global_scope.functions.get(fx_idx);
        self.current_function = Some(function.name.clone());

        // Handle self parameter if present
        let self_var_idx_opt = if let Some(self_param) = &fx_decl.self_param {
            if let Some(ref impl_type_name) = self.current_impl_type {
                let mut type_token = self_param.token.clone();
                type_token.span.literal = impl_type_name.clone();
                
                let self_type = self.resolve_type_from_string(&type_token);
                
                // Register 'self' as a variable
                let self_path = Path {
                    span: self_param.token.span.clone(),
                    segments: vec![PathSegment {
                        identifier: self_param.token.clone(),
                        arguments: None,
                    }],
                    tokens: vec![self_param.token.clone()],
                };
                
                let self_var_idx = self.scopes.global_scope.declare_variable(
                    &self_path,
                    self_type,
                    false, // not shadowing
                    false, // TODO: handle mut self
                    false, // not mutable
                );
                
                // Add self as the first parameter
                let function = self.scopes.global_scope.functions.get_mut(fx_idx);
                function.parameters.insert(0, self_var_idx);
                
                Some(self_var_idx)
            } else {
                None
            }
        } else {
            None
        };

        let function = self.scopes.global_scope.functions.get(fx_idx);
        let param_indices: Vec<VariableIndex> = function.parameters.clone();
        
        // Add self param to the local scope
        if let Some(self_var_idx) = self_var_idx_opt {
            self.scopes.current_local_scope_mut().locals.push(self_var_idx);
        }
        
        let param_offset = if self_var_idx_opt.is_some() { 1 } else { 0 };
        
        for (param_idx, generic_param) in fx_decl.generics.params.iter().enumerate() {
            let actual_param_idx = param_idx + param_offset;
            if actual_param_idx < param_indices.len() {
                let param_var_idx = param_indices[actual_param_idx];
                
                let resolved_type = match &generic_param.kind {
                    GenericParamKind::Type { ty, .. } => {
                        self.resolve_ast_type(ty)
                    }
                    GenericParamKind::Const { ty, .. } => {
                        self.resolve_ast_type(ty)
                    }
                };
                
                let param_var = self.scopes.global_scope.variables.get_mut(param_var_idx);
                param_var.ty = resolved_type;
                
                self.scopes.current_local_scope_mut().locals.push(param_var_idx);
            }
        }

        let return_type = if fx_decl.return_type.is_some() {
            self.resolve_ast_type(&fx_decl.return_type.as_ref().unwrap().ty)
        } else {
            TypeKind::Void
        };
        
        let function = self.scopes.global_scope.functions.get_mut(fx_idx);
        function.return_type = return_type;

        for statement_id in &fx_decl.body.statements {
            self.visit_statement(ast, *statement_id);
        }
        
        // Update the function body's type based on the last statement
        // If the last statement is a return expression, the body type is Void (explicit return)
        // If the last statement is a tail expression (no semicolon), use its type (implicit return)
        let body_ty = fx_decl.body.statements.last().map(|statement_id| {
            let statement = ast.query_statement(*statement_id);
            match statement.kind {
                StatementKind::Expression(expr_id) | StatementKind::SemiExpression(expr_id) => {
                    let expr = ast.query_expression(expr_id);
                    if matches!(expr.kind, ExpressionKind::Return(_)) {
                        TypeKind::Void
                    } else if matches!(statement.kind, StatementKind::SemiExpression(_)) {
                        TypeKind::Void
                    } else {
                        expr.ty.clone()
                    }
                }
                _ => TypeKind::Void,
            }
        }).unwrap_or(TypeKind::Void);
        
        let function = self.scopes.global_scope.functions.get(fx_idx);
        let expected_return_type = function.return_type.clone();

        // Only check implicit returns (when body_ty is not Void)
        // If body_ty is Void, the function either:
        // 1. Ends with an explicit return statement (which is already type-checked), or
        // 2. Has no tail expression (which is correct for void functions)
        if !matches!(body_ty, TypeKind::Void) {
            self.expect_type(expected_return_type, &body_ty, &fx_decl.identifier.span);
        } else if !matches!(expected_return_type, TypeKind::Void) {
            let always_returns = fx_decl.body.always_returns(ast);
            
            if !always_returns {
                self.expect_type(expected_return_type, &TypeKind::Void, &fx_decl.body.span);
            }
        }

        self.scopes.exit_fx_scope();
        
        // Restore previous function context
        self.current_function = prev_function;
    }

    fn visit_return_expression(&mut self, ast: &mut Ast, return_expression: &ReturnExpression, expr: &Expression) {
        let return_keyword = return_expression.return_keyword.clone();
        // todo: do not clone this
        match self.scopes.surrounding_function().cloned() {
            None => {
                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                diagnostics_binding.report_return_outside_function(&return_expression.return_keyword);
            }
            Some(function) => {
                if let Some(return_expression_value) = &return_expression.return_value {
                    self.visit_expression(ast, *return_expression_value);
                    let return_value = ast.query_expression(*return_expression_value);
                    self.expect_type(function.return_type.clone(), &return_value.ty, &return_value.span(&ast));
                } else {
                    self.expect_type(function.return_type.clone(), &TypeKind::Void, &return_keyword.span);
                }
            }
        }
        
        ast.set_type(expr.id, TypeKind::Void);
    }

    fn visit_call_expression(&mut self, ast: &mut Ast, call_expression: &CallExpression, expr: &Expression) {
        let path_len = call_expression.callee.segments.len();
        let raw_callee_name = &call_expression.callee.segments.last().unwrap().identifier.span.literal;
        
        // Resolve Self to the actual type name if we're in an impl block
        let callee_name: String = if raw_callee_name == "Self" {
            if let Some(ref impl_type) = self.current_impl_type {
                let resolved_name = impl_type.clone();
                
                // Resolve Self to actual type name
                let expr_mut = ast.query_expression_mut(expr.id);
                if let ExpressionKind::Call(ref mut call_expr_mut) = expr_mut.kind {
                    // Update the last segment's identifier to use the resolved name
                    let last_idx = call_expr_mut.callee.segments.len() - 1;
                    call_expr_mut.callee.segments[last_idx].identifier.span.literal = resolved_name.clone();
                }
                
                resolved_name
            } else {
                self.diagnostics.borrow_mut().report_self_outside_impl(
                    &call_expression.callee.span.clone()
                );
                raw_callee_name.clone()
            }
        } else {
            raw_callee_name.clone()
        };
        
        // Check if this is a qualified path (Type::method)
        let function = if path_len >= 2 {
            let type_name = &call_expression.callee.segments[path_len - 2].identifier.span.literal;
            self.scopes.global_scope.lookup_method(type_name, &callee_name)
        } else {
            if let Some(ref current_fx) = self.current_function {
                let scoped_name = format!("{}::{}", current_fx, callee_name);
                if let Some(fx_idx) = self.scopes.global_scope.lookup_fx(&scoped_name) {
                    Some(fx_idx)
                } else {
                    self.scopes.global_scope.lookup_fx(&callee_name)
                }
            } else {
                self.scopes.global_scope.lookup_fx(&callee_name)
            }
        };

        let ty = match function {
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
            None => {
                let path_len = call_expression.callee.segments.len();
                let enum_name = if path_len >= 2 {
                    Some(&call_expression.callee.segments[path_len - 2].identifier.span.literal)
                } else {
                    None
                };

                // Tuple struct or undeclared function
                if let Some(struct_name) = self.scopes.lookup_struct_with_local(&callee_name) {
                    let struct_item = self.scopes.global_scope.get_struct(struct_name).clone();
                    if let ItemKind::Struct(_identifier, generics, variant_data) = &struct_item.kind {
                        let mut fields = Vec::new();

                        match variant_data {
                            VariantData::Tuple(elements) => {
                                if elements.len() != call_expression.arguments.len() {
                                    let mut diagnostics_binding = self.diagnostics.borrow_mut();
                                    diagnostics_binding.report_invalid_arg_count(
                                        &call_expression.callee.span,
                                        elements.len(),
                                        call_expression.arguments.len(),
                                    );
                                }

                                for argument in &call_expression.arguments {
                                    self.visit_expression(ast, *argument);
                                }

                                // Generic param type inference
                                let mut generic_substitutions = HashMap::new();
                                
                                if !generics.is_empty() {
                                    for (argument, element) in call_expression.arguments.iter().zip(elements.iter()) {
                                        let argument_expression = ast.query_expression(*argument);
                                        
                                        if let AstType::Simple { type_name } = &*element.ty {
                                            if generics.params.iter().any(
                                                |param| param.identifier.span.literal == type_name.span.literal
                                            ) {
                                                generic_substitutions.insert(
                                                    type_name.span.literal.clone(), argument_expression.ty.clone()
                                                );
                                            }
                                        }
                                    }
                                }

                                // Type substitution and checking
                                for (argument, element) in call_expression.arguments.iter().zip(elements.iter()) {
                                    let argument_expression = ast.query_expression(*argument);

                                    let element_type = if let AstType::Simple { type_name } = &*element.ty {
                                        if let Some(inferred_type) = generic_substitutions.get(&type_name.span.literal) {
                                            inferred_type.clone()
                                        } else {
                                            self.resolve_ast_type(&element.ty)
                                        }
                                    } else {
                                        self.resolve_ast_type(&element.ty)
                                    };

                                    self.expect_type(element_type.clone(), &argument_expression.ty, &argument_expression.span(&ast));

                                    fields.push(
                                        FieldType {
                                            ty: Box::new(argument_expression.ty.clone()),
                                            name: None,
                                        }
                                    )
                                }

                                TypeKind::Object(
                                    ObjectType {
                                        fields,
                                        kind: ObjectKind::Struct(callee_name.clone()),
                                    }
                                )
                            }
                            _ => {
                                let mut diagnostics_binding = self.diagnostics.borrow_mut();
                                diagnostics_binding.report_undeclared_function(&call_expression.callee.segments.last().unwrap().identifier);
                                TypeKind::Error
                            }
                        }
                    } else {
                        let mut diagnostics_binding = self.diagnostics.borrow_mut();
                        diagnostics_binding.report_undeclared_function(&call_expression.callee.segments.last().unwrap().identifier);
                        TypeKind::Error
                    }
                } else if let Some((enum_idx, variant_info)) = self.scopes.global_scope.lookup_enum_variant(
                    enum_name.map_or("???", |name| name), 
                    &call_expression.callee.segments.last().unwrap().identifier.span.literal,
                ) {
                    let variant_data = variant_info.data.clone();
                    let variant_name = variant_info.name.clone();
                    let enum_def_name = self.scopes.global_scope.get_enum(enum_idx).name.clone();
                    let mut fields = Vec::new();

                    if let VariantData::Tuple(elements) = variant_data {
                        if elements.len() != call_expression.arguments.len() {
                            let mut diagnostics_binding = self.diagnostics.borrow_mut();
                            diagnostics_binding.report_invalid_arg_count(
                                &call_expression.callee.span,
                                elements.len(),
                                call_expression.arguments.len(),
                            );
                        }

                        for (argument, element) in call_expression.arguments.iter().zip(elements.iter()) {
                            self.visit_expression(ast, *argument);
                            let argument_expression = ast.query_expression(*argument);

                            let element_type = self.resolve_ast_type(&element.ty);
                            self.expect_type(element_type.clone(), &argument_expression.ty, &argument_expression.span(&ast));

                            fields.push(
                                FieldType {
                                    ty: Box::new(element_type),
                                    name: None,
                                }
                            )
                        }

                        TypeKind::Enum {
                            enum_name: enum_def_name,
                            variant_name: Some(variant_name),
                        }
                    } else {
                        let mut diagnostics_binding = self.diagnostics.borrow_mut();
                        diagnostics_binding.report_undeclared_function(&call_expression.callee.segments.last().unwrap().identifier);
                        TypeKind::Error
                    }
                } else {
                    let mut diagnostics_binding = self.diagnostics.borrow_mut();
                    diagnostics_binding.report_undeclared_function(&call_expression.callee.segments.last().unwrap().identifier);
                    TypeKind::Error
                }
            }
        };

        ast.set_type(expr.id, ty);
    }

    fn visit_method_call_expression(&mut self, ast: &mut Ast, method_call: &MethodCallExpression, expr: &Expression) {
        self.visit_expression(ast, method_call.receiver);
        
        for arg in &method_call.arguments {
            self.visit_expression(ast, *arg);
        }
        
        let receiver_expr = ast.query_expression(method_call.receiver);
        let receiver_type = receiver_expr.ty.clone();
        
        let type_name = match &receiver_type {
            TypeKind::Object(obj_type) => {
                match &obj_type.kind {
                    ObjectKind::Struct(struct_name) => struct_name.clone(),
                    ObjectKind::Tuple => {
                        // The type should have been resolved from variable assignment
                        // Try to get it from the format method name
                        format!("{}", receiver_type).split("::").next().unwrap_or("").to_string()
                    }
                }
            }
            TypeKind::Enum { enum_name, .. } => enum_name.clone(),
            _ => {
                self.diagnostics.borrow_mut().report_inappropriate_method_call(
                    &receiver_expr.span.literal,
                    &method_call.method_name.span,
                );
                ast.set_type(expr.id, TypeKind::Void);
                return;
            }
        };
        
        if type_name.is_empty() || matches!(type_name.as_str(), "int" | "float" | "bool" | "string" | "void" | "unresolved") {
            self.diagnostics.borrow_mut().report_inappropriate_method_call(
                &receiver_expr.span.literal,
                &method_call.method_name.span,
            );
            ast.set_type(expr.id, TypeKind::Void);
            return;
        }

        // Method lookup
        let method_name = &method_call.method_name.span.literal;
        if let Some(fx_idx) = self.scopes.global_scope.lookup_method(&type_name, method_name) {
            let function = self.scopes.global_scope.functions.get(fx_idx);
            
            // Type check: self parameter should match receiver type
            // (First parameter should always be self)
            
            // Check argument count (excluding self parameter)
            let expected_arg_count = function.parameters.len().saturating_sub(1);
            if method_call.arguments.len() != expected_arg_count {
                self.diagnostics.borrow_mut().report_invalid_arg_count(
                    &method_call.method_name.span,
                    expected_arg_count,
                    method_call.arguments.len()
                );
            }

            // Type check arguments (skip first parameter which is self)
            for (i, arg) in method_call.arguments.iter().enumerate() {
                let param_idx = i + 1; // Skip self parameter
                if param_idx < function.parameters.len() {
                    let param_var_idx = function.parameters[param_idx];
                    let param_var = self.scopes.global_scope.variables.get(param_var_idx);
                    let arg_expr = ast.query_expression(*arg);
                    let _expected_ty = expect_type(
                        &self.diagnostics,
                        param_var.ty.clone(),
                        &arg_expr.ty,
                        &arg_expr.span(ast)
                    );
                }
            }

            let method_call_mut = match &mut ast.query_expression_mut(expr.id).kind {
                ExpressionKind::MethodCall(mc) => mc,
                _ => unreachable!(),
            };
            method_call_mut.resolved_fx = fx_idx;

            ast.set_type(expr.id, function.return_type.clone());
        } else {
            self.diagnostics.borrow_mut().report_unknown_method(
                &method_call.method_name.span.literal,
                &type_name,
                &method_call.method_name.span
            );
            ast.set_type(expr.id, TypeKind::Void);
        }
    }

    fn visit_assignment_expression(&mut self, ast: &mut Ast, assignment_expression: &AssignExpression, expr: &Expression) {
        self.visit_expression(ast, assignment_expression.expression);
        self.visit_expression(ast, assignment_expression.lhs);
        
        let lhs_expr = ast.query_expression(assignment_expression.lhs);
        let rhs_expr = ast.query_expression(assignment_expression.expression);
        
        self.expect_type(lhs_expr.ty.clone(), &rhs_expr.ty, &rhs_expr.span(ast));
        
        ast.set_type(expr.id, rhs_expr.ty.clone());
    }

    fn visit_while_expression(&mut self, ast: &mut Ast, while_statement: &WhileExpression, expr: &Expression) {
        self.visit_expression(ast, while_statement.condition);
        let condition = ast.query_expression(while_statement.condition);
        self.expect_type(TypeKind::Bool, &condition.ty, &condition.span(&ast));

        self.loop_depth += 1;
        self.visit_block_expression(ast, &while_statement.body, expr);
        self.loop_depth -= 1;
    }

    fn visit_break_expression(&mut self, ast: &mut Ast, break_expression: &BreakExpression, expr: &Expression) {
        if self.loop_depth == 0 {
            let mut diagnostics_binding = self.diagnostics.borrow_mut();
            diagnostics_binding.report_loop_keyword_outside_loop(&break_expression.break_keyword);
        }
        ast.set_type(expr.id, TypeKind::Void);
    }

    fn visit_continue_expression(&mut self, ast: &mut Ast, continue_expression: &ContinueExpression, expr: &Expression) {
        if self.loop_depth == 0 {
            let mut diagnostics_binding = self.diagnostics.borrow_mut();
            diagnostics_binding.report_loop_keyword_outside_loop(&continue_expression.continue_keyword);
        }
        ast.set_type(expr.id, TypeKind::Void);
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
        
        let actual_array_type = TypeKind::Array(Box::new(inferred_element_type.clone()), array_expression.elements.len());

        ast.set_type(expr.id, actual_array_type.clone());

        let should_report_element_mismatches = if let Some(expected) = &self.expected_array_type {
            match expected {
                TypeKind::Array(expected_element_type, expected_length) => {
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

        self.expect_index_type(TypeKind::Usize, &index_ty, &index_span, is_neg_idx);

        match &current_type {
            TypeKind::Array(element_type, array_size) => {
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
                current_type = TypeKind::Error;
            }
        }
        
        ast.set_type(expr.id, current_type);
    }

    fn visit_tuple_expression(&mut self, ast: &mut Ast, tuple_expression: &TupleExpression, expr: &Expression) {
        for element in &tuple_expression.elements {
            self.visit_expression(ast, *element);
        }

        let element_types: Vec<TypeKind> = tuple_expression.elements.iter()
            .map(|element_id| {
                let element = ast.query_expression(*element_id);
                element.ty.clone()
            })
            .collect();

        let tuple_type = TypeKind::tuple(element_types.clone());
        ast.set_type(expr.id, tuple_type);
    }

    fn visit_field_expression(&mut self, ast: &mut Ast, field_expression: &FieldExpression, expr: &Expression) {
        self.visit_expression(ast, field_expression.object);
        
        let target_obj = ast.query_expression(field_expression.object);
        let mut current_type = target_obj.ty.clone();
        let target_type_str = format!("{}", current_type);
        let target_span = target_obj.span(ast);
        let should_visit_field = match &current_type {
            TypeKind::Object(object_type) if matches!(object_type.kind, ObjectKind::Struct(_)) => false,
            TypeKind::Enum { .. } => false,
            _ => true,
        };
        
        if should_visit_field {
            self.visit_expression(ast, field_expression.field.idx_no);
        }

        let field_expr = ast.query_expression(field_expression.field.idx_no);
        let field_span = field_expr.span(ast);
        let field_expr_kind = field_expr.kind.clone();

        match &current_type {
            TypeKind::Object(object_type) if matches!(object_type.kind, ObjectKind::Tuple) => {
                // Tuple field access
                let index_ty = field_expr.ty.clone();
                let index_literal = field_span.literal.clone();

                self.expect_index_type(TypeKind::Usize, &index_ty, &field_span, false);

                let tuple_size = object_type.fields.len();

                // Compile-time bounds checking for constant indices
                if let Ok(idx) = index_literal.parse::<usize>() {
                    if idx >= tuple_size {
                        self.diagnostics.borrow_mut().report_tuple_unknown_field(
                            &field_span,
                            target_type_str,
                        );
                        current_type = TypeKind::Error;
                    } else {
                        current_type = (*object_type.fields[idx].ty).clone();
                    }
                };
            }
            TypeKind::Object(object_type) if matches!(object_type.kind, ObjectKind::Struct(_)) => {
                let is_numeric_access = match &field_expr_kind {
                    ExpressionKind::Number(_) | ExpressionKind::Usize(_) => true,
                    _ => false,
                };
                
                if is_numeric_access {
                    let index_literal = field_span.literal.clone();
                    let tuple_size = object_type.fields.len();

                    // Compile-time bounds checking for constant indices
                    if let Ok(idx) = index_literal.parse::<usize>() {
                        if idx >= tuple_size {
                            self.diagnostics.borrow_mut().report_tuple_unknown_field(
                                &field_span,
                                target_type_str,
                            );
                            current_type = TypeKind::Error;
                        } else {
                            current_type = (*object_type.fields[idx].ty).clone();
                        }
                    } else {
                        self.diagnostics.borrow_mut().report_invalid_field_kind(
                            format!("Invalid numeric index: {}", index_literal),
                            &field_span
                        );
                        current_type = TypeKind::Error;
                    }
                } else {
                    let field_name = match &field_expr_kind {
                        ExpressionKind::Path(path_expr) => {
                            path_expr.path.tokens.last().unwrap().span.literal.clone()
                        }
                        _ => {
                            self.diagnostics.borrow_mut().report_invalid_field_kind(
                                format!("{:?}", field_expr_kind),
                                &field_span
                            );
                            field_span.literal.clone()
                        }
                    };
                    
                    if let Some(field_info) = object_type.fields.iter().find(|f| {
                        if let Some(ref name) = f.name {
                            *name == field_name
                        } else {
                            false
                        }
                    }) {
                        current_type = field_info.ty.as_ref().clone();
                    } else {
                        self.diagnostics.borrow_mut().report_unknown_field_in_object(
                            field_span.literal.clone(),
                            target_type_str,
                            &field_span,
                        );

                        current_type = TypeKind::Error;
                    }
                }
            }
            TypeKind::Enum { enum_name, variant_name: Some(variant_name) } => {
                let field_name = match &field_expr_kind {
                    ExpressionKind::Path(path_expr) => {
                        path_expr.path.tokens.last().unwrap().span.literal.clone()
                    }
                    _ => {
                        self.diagnostics.borrow_mut().report_invalid_field_kind(
                            format!("{:?}", field_expr_kind),
                            &field_span
                        );
                        field_span.literal.clone()
                    }
                };
                
                // Get field types
                if let Some(enum_idx) = self.scopes.global_scope.lookup_enum(enum_name) {
                    let enum_def = self.scopes.global_scope.get_enum(enum_idx);
                    if let Some(variant) = enum_def.variants.iter().find(|v| &v.name == variant_name) {
                        match &variant.data {
                            VariantData::Struct { fields } => {
                                if let Some(field_def) = fields.iter().find(|f| {
                                    f.identifier.as_ref().map(|id| &id.span.literal) == Some(&field_name)
                                }) {
                                    current_type = self.resolve_ast_type(&field_def.ty);
                                } else {
                                    self.diagnostics.borrow_mut().report_unknown_field_in_object(
                                        field_name,
                                        format!("{}::{}", enum_name, variant_name),
                                        &field_span,
                                    );
                                    current_type = TypeKind::Error;
                                }
                            }
                            _ => {
                                self.diagnostics.borrow_mut().report_no_fields_to_access(&current_type, &target_span, &field_span);
                                current_type = TypeKind::Error;
                            }
                        }
                    } else {
                        current_type = TypeKind::Error;
                    }
                } else {
                    current_type = TypeKind::Error;
                }
            }
            TypeKind::Enum { .. } => {
                // Enum without specific variant - can't access fields
                self.diagnostics.borrow_mut().report_no_fields_to_access(&current_type, &target_span, &field_span);
                current_type = TypeKind::Error;
            }
            _ => {
                self.diagnostics.borrow_mut().report_no_fields_to_access(&current_type, &target_span, &field_span);
                current_type = TypeKind::Error;
            }
        }
        
        ast.set_type(expr.id, current_type);
    }

    fn visit_constant_item(&mut self, ast: &mut Ast, constant_item: &ConstantItem, _item_id: ItemIndex) {
        let identifiers = self.path_from_pattern_identifier(&constant_item.identifier);

        for identifier in identifiers {
            let identifier_str = &identifier.tokens.last().unwrap().span.literal;
    
            if identifier_str.chars().any(|c| c.is_lowercase()) {
                self.diagnostics.borrow_mut().warn_non_upper_case(&identifier_str, &constant_item.identifier.span);
            }
    
            let mut ty = self.resolve_type_from_annotation(&constant_item.type_annotation);
            if matches!(ty, TypeKind::Array(_, _)) {
                self.expected_array_type = Some(ty.clone());
            }
    
            if constant_item.expr.is_some() {
                let const_item_expr = **constant_item.expr.as_ref().unwrap();
                self.visit_expression(ast, const_item_expr);
                let initialiser_expression = &ast.query_expression(const_item_expr);
    
                self.expected_array_type = None;
        
                ty = self.expect_type(ty.clone(), &initialiser_expression.ty, &initialiser_expression.span(&ast));
            }
    
            self.scopes.global_scope.declare_variable(&identifier, ty, true, false, false);
        }
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
            let struct_name = match &item.kind {
                ItemKind::Struct(name, _, _) => &name.span.literal,
                _ => return,  // Should never happen
            };
            
            if self.scopes.global_scope.lookup_struct(struct_name).is_some() {
                return;
            }
            
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
        let raw_struct_name = &struct_expression.path.segments.last().unwrap().identifier.span.literal;
        
        let struct_name: String = if raw_struct_name == "Self" {
            if let Some(ref impl_type) = self.current_impl_type {
                let resolved_name = impl_type.clone();
                
                let expr_mut = ast.query_expression_mut(expr.id);
                if let ExpressionKind::Struct(ref mut struct_expr_mut) = expr_mut.kind {
                    // Update the last segment's identifier to use the resolved name
                    let last_idx = struct_expr_mut.path.segments.len() - 1;
                    struct_expr_mut.path.segments[last_idx].identifier.span.literal = resolved_name.clone();
                }
                
                resolved_name
            } else {
                self.diagnostics.borrow_mut().report_self_outside_impl(
                    &struct_expression.path.span.clone()
                );
                raw_struct_name.clone()
            }
        } else {
            raw_struct_name.clone()
        };
        
        let path_len = struct_expression.path.segments.len();
        let mut field_types: Vec<(String, TypeKind)> = Vec::new();
        
        if let Some(ref_struct_idx) = self.scopes.lookup_struct_with_local(&struct_name) {
            let ref_struct = self.scopes.global_scope.get_struct(ref_struct_idx).clone();

            match &ref_struct.kind {
                ItemKind::Struct(identifier, generics, variant_data) => {
                    match variant_data {
                        VariantData::Struct { fields: struct_fields } => {
                            for expr_field in &struct_expression.fields {
                                self.visit_expression(ast, expr_field.expr.id);
                            }

                            // Generic param type inference
                            let mut generic_substitutions = HashMap::new();
                            
                            if !generics.is_empty() {
                                for struct_field in struct_fields {
                                    if let Some(field_name) = &struct_field.identifier {
                                        if let Some(expr_field) = struct_expression.fields.iter()
                                            .find(|f| f.identifier.span.literal == field_name.span.literal) {
                                            
                                            let field_expr_ty = &ast.query_expression(expr_field.expr.id).ty;
                                            
                                            if let AstType::Simple { type_name } = &*struct_field.ty {
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
                                        let expected_field_type = if let AstType::Simple { type_name } = &*struct_field.ty {
                                            if let Some(inferred_type) = generic_substitutions.get(&type_name.span.literal) {
                                                inferred_type.clone()
                                            } else {
                                                self.resolve_ast_type(&struct_field.ty)
                                            }
                                        } else {
                                            self.resolve_ast_type(&struct_field.ty)
                                        };
                                        
                                        self.expect_type(expected_field_type, field_expr_ty, &expr_field.expr.span(ast));
                                    } else {
                                        self.diagnostics.borrow_mut().report_unknown_field_in_object(
                                            field_name.span.literal.clone(),
                                            struct_name.to_string(),
                                            &struct_expression.path.span.clone()
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

                            let struct_type = TypeKind::struct_resolved(identifier.span.literal.to_string(), field_types);
                            ast.query_expression_mut(expr.id).ty = struct_type;
                        }
                        _ => unimplemented!("TODO")
                    }
                }
                _ => {
                    bug_report!("Internal compiler error: Expected struct item");
                }
            }
        } else if let Some(enum_identifier) = struct_expression.path.segments.get(path_len - 2) {
            let enum_idx = self.scopes.global_scope.lookup_enum(enum_identifier.identifier.span.literal.as_str());
            if let Some(enum_idx) = enum_idx {
                let enum_def = self.scopes.global_scope.get_enum(enum_idx).clone();
                let variant_opt = enum_def.variants.iter().find(|variant| {
                    variant.name == struct_name
                });

                if let Some(variant) = variant_opt {
                    match &variant.data {
                        VariantData::Struct { fields } => {
                            for expr_field in &struct_expression.fields {
                                self.visit_expression(ast, expr_field.expr.id);
                            }

                            // TODO: Generic param inference (future impl)

                            // Type check
                            for variant_field in fields {
                                if let Some(expr_field) = struct_expression.fields.iter()
                                    .find(|f| f.identifier.span.literal == variant_field.identifier.as_ref().unwrap().span.literal) {
                                    
                                    let field_expr_ty = &ast.query_expression(expr_field.expr.id).ty;
                                    field_types.push((variant_field.identifier.as_ref().unwrap().span.literal.clone(), field_expr_ty.clone()));

                                    let expected_field_type = self.resolve_ast_type(&variant_field.ty);
                                    
                                    self.expect_type(expected_field_type, field_expr_ty, &expr_field.expr.span(ast));
                                } else {
                                    self.diagnostics.borrow_mut().report_unknown_field_in_object(
                                        variant_field.identifier.as_ref().unwrap().span.literal.clone(),
                                        struct_name.to_string(),
                                        &struct_expression.path.span.clone()
                                    );
                                }
                            }

                            // Check for extra fields in the expression that don't exist in the struct
                            for expr_field in &struct_expression.fields {
                                let field_exists = fields.iter().any(|vf| {
                                    vf.identifier.as_ref().unwrap().span.literal == expr_field.identifier.span.literal
                                });
                                
                                if !field_exists {
                                    self.diagnostics.borrow_mut().report_unknown_field_in_object(
                                        expr_field.identifier.span.literal.clone(),
                                        struct_name.to_string(),
                                        &expr_field.identifier.span
                                    );
                                }
                            }

                            let enum_type = TypeKind::Enum {
                                enum_name: enum_def.name.clone(),
                                variant_name: Some(variant.name.clone()),
                            };
                            ast.query_expression_mut(expr.id).ty = enum_type;
                        }
                        _ => bug_report!("Internal compiler error: Expected struct variant data"),
                    }
                }
            }
        } else {
            self.diagnostics.borrow_mut().report_undefined_struct(struct_name.to_string(), &struct_expression.path.span);
        }
    }

    fn visit_enum_item(&mut self, ast: &mut Ast, _generics: &Generics, enum_definition: &EnumDefinition, item_id: ItemIndex) {
        let enum_item = ast.query_item(item_id);
        let enum_name = if let ItemKind::Enum(name, _, _) = &enum_item.kind {
            &name.span.literal
        } else {
            bug_report!("Internal compiler error: Expected enum item");
        };

        if self.scopes.global_scope.lookup_enum(enum_name).is_some() {
            if !enum_name.chars().next().unwrap().is_uppercase() || enum_name.contains('_') {
                self.diagnostics.borrow_mut().warn_non_upper_camel_case(enum_name, &enum_item.span);
            }
            return;
        }

        let variants: Vec<VariantInfo> = enum_definition.variants.iter()
            .enumerate()
            .map(|(discriminant, variant)| {
                VariantInfo {
                    discriminant,
                    name: variant.identifier.span.literal.clone(),
                    data: variant.data.clone(),
                }
            }
        ).collect();

        let result = self.scopes.global_scope.declare_enum(
            enum_name.clone(),
            enum_item,
            variants,
        );

        if let Err(_existing_idx) = result {
            self.diagnostics.borrow_mut().report_enum_already_declared(
                enum_name.clone(),
                &enum_item.span,
            );
        }

        if !enum_name.chars().next().unwrap().is_uppercase() || enum_name.contains('_') {
            self.diagnostics.borrow_mut().warn_non_upper_camel_case(enum_name, &enum_item.span);
        }
    }

    fn visit_path_expression(&mut self, ast: &mut Ast, path_expression: &PathExpression, expr: &Expression) {
        let path_len = path_expression.path.segments.len();
        let path = &path_expression.path;

        if path_len == 0 {
            self.diagnostics.borrow_mut().report_invalid_path(&path_expression.path.span);
            ast.set_type(expr.id, TypeKind::Error);
            return;
        }

        let identifier = path_expression.path.segments.last().unwrap().identifier.span.literal.clone();

        if path_len == 1 {
            match self.scopes.lookup_variable(path) {
                None => {
                    // Unit struct
                    if self.scopes.global_scope.lookup_struct(&identifier).is_some() {
                        let struct_type = TypeKind::Object(
                            ObjectType {
                                fields: Vec::new(),
                                kind: ObjectKind::Struct(identifier.clone())
                            }
                        );
                        ast.set_type(expr.id, struct_type);
                        return;
                    }
                    
                    self.diagnostics.borrow_mut().report_undeclared_item(
                        &identifier,
                        &path_expression.path.span
                    );
                    ast.set_type(expr.id, TypeKind::Error);
                    return;
                }
                Some(var_idx) => {
                    let variable = self.scopes.global_scope.variables.get(var_idx);
                    ast.set_type(expr.id, variable.ty.clone());
                    ast.set_resolved_variable(expr.id, var_idx);
                    return;
                }
            }
        } else {
            // Enum variant access
            let enum_name = &path_expression.path.segments[path_len - 2].identifier.span.literal;
            let enum_idx = self.scopes.global_scope.lookup_enum(enum_name.as_str());
            if let Some(enum_idx) = enum_idx {
                let enum_def = self.scopes.global_scope.get_enum(enum_idx).clone();
                let variant_opt = enum_def.variants.iter().find(|variant| {
                    variant.name == identifier.as_str()
                });

                if let Some(variant) = variant_opt {
                    let enum_type = TypeKind::Enum {
                        enum_name: enum_def.name.clone(),
                        variant_name: Some(variant.name.clone()),
                    };
                    ast.set_type(expr.id, enum_type);
                    return;
                } else {
                    // Variant not found in enum
                    self.diagnostics.borrow_mut().report_undeclared_item(
                        &identifier,
                        &path_expression.path.span
                    );
                    ast.set_type(expr.id, TypeKind::Error);
                    return;
                }
            } else {
                // Enum not found – undeclared item
                self.diagnostics.borrow_mut().report_undeclared_item(
                    enum_name,
                    &path_expression.path.segments[path_len - 2].identifier.span
                );
                ast.set_type(expr.id, TypeKind::Error);
                return;
            }
        }
    }

    fn visit_impl_item(&mut self, ast: &mut Ast, impl_item: &Impl, item_id: ItemIndex) {
        // Get the type name from `self`
        let type_name = match &*impl_item.self_type {
            AstType::Simple { type_name } => {
                type_name.span.literal.clone()
            }
            AstType::Path(_, path) => {
                path.segments.last().unwrap().identifier.span.literal.clone()
            }
            _ => {
                // Complex types like arrays, tuples not supported yet
                return;
            }
        };
        
        // Add impl to global scope - store at item_id to maintain alignment with AST items
        // Push placeholders until there is enough space to set impls[item_id]
        while self.scopes.global_scope.impls.indices().last().map_or(0, |idx| idx.as_index() + 1) <= item_id.as_index() {
            // Create a placeholder impl
            let placeholder = Impl {
                generics: Generics { params: Vec::new(), span: TextSpan::new(0, 0, String::new()) },
                self_type: Box::new(AstType::Simple { 
                    type_name: Token::new(
                        TokenKind::Identifier, 
                        TextSpan::new(0, 0, String::new())
                    )
                }),
                items: Vec::new(),
            };
            self.scopes.global_scope.impls.push(placeholder);
        }

        // Overwrite the placeholder with the actual impl
        self.scopes.global_scope.impls[item_id] = impl_item.clone();

        // Set current impl type for Self resolution
        let prev_impl_type = self.current_impl_type.take();
        self.current_impl_type = Some(type_name.clone());

        // Register each method in this impl block and create function entries
        let mut method_mappings = std::collections::HashMap::new();
        
        for item in &impl_item.items {
            if let AssociatedItemKind::Function(fx_decl) = &item.kind {
                let method_name = fx_decl.identifier.span.literal.clone();
                
                // Method as path: TypeName::method_name
                let path = format!("{}::{}", type_name, method_name);
                let return_type = fx_decl.return_type.as_ref().map(|rt| {
                    self.resolve_ast_type(&rt.ty)
                }).unwrap_or(TypeKind::Void);
                
                let fx_idx_result = self.scopes.global_scope.create_function(
                    path,
                    fx_decl.body.clone(),
                    fx_decl.generics.get_param_indices(),
                    return_type,
                );
                
                let fx_idx = match fx_idx_result {
                    Ok(created_fx_idx) => created_fx_idx,
                    Err(existing_fx_idx) => existing_fx_idx,
                };
                
                self.scopes.global_scope.register_method(&type_name, &method_name, fx_idx);
                
                method_mappings.insert(item.id, fx_idx);
            }
        }

        // Method body resolution
        for item in &impl_item.items {
            match &item.kind {
                AssociatedItemKind::Function(fx_decl) => {
                    let fx_idx = method_mappings.get(&item.id).copied().unwrap_or(item.id);
                    let mut fx_decl_copy = fx_decl.clone();
                    fx_decl_copy.index = fx_idx;

                    self.visit_fx_decl(ast, &fx_decl_copy, fx_idx);
                }
                AssociatedItemKind::Const(_const_item) => {
                    // TODO: Handle associated constants in impl blocks
                }
            }
        }

        // Restore previous impl type
        self.current_impl_type = prev_impl_type;
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
    fn create_scoped_struct_item(&self, mut item: Item<ItemKind>) -> Item<ItemKind> {
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
            for statement in &function.body.statements {
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