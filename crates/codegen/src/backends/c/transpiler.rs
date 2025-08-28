use std::collections::HashMap;

use snowflake_front::{
    ast::{Ast, BinaryExpression, BinaryOp, BinaryOpKind, BlockExpression, CallExpression, Expression, ExpressionId, ExpressionKind, FxDeclaration, IfExpression, Item, ItemKind, StatementId, StatementKind, UnaryExpression, UnaryOp, UnaryOpKind},
    compilation_unit::{GlobalScope, VariableIndex}
};
use snowflake_common::typings::Type;

use crate::backends::c::ast::{CAssignExpr, CAst, CBinExpr, CBinOp, CBlockStatement, CBool, CCallExpr, CExpr, CFloat, CFxDecl, CFxImpl, CIfStatement, CItem, CNumber, CParams, CReturn, CStatement, CType, CUnaryExpr, CUnaryOp, CUsize, CVarDecl, CVarExpr, CWhileStatement};


pub struct CTranspiler<'a> {
    pub global_scope: &'a GlobalScope,
    pub temp_var_counter: usize,
    pub shadowing_vars: HashMap<String, Vec<VariableIndex>>,
}

impl <'a> CTranspiler<'a> {
    pub fn new(global_scope: &'a GlobalScope) -> Self {
        Self { global_scope, temp_var_counter: 0, shadowing_vars: HashMap::new() }
    }

    pub fn transpile(mut self, ast: &Ast) -> CAst {
        let mut items = vec![
            CItem::Macro("true".to_string(), "1".to_string()),
            CItem::Macro("false".to_string(), "0".to_string()),
        ];

        items.extend(
            ast.items.iter().filter(|item| matches!(item.kind, ItemKind::Function(_)))
                .map(|item| match &item.kind {
                    ItemKind::Statement(_) => unreachable!(),
                    ItemKind::Function(function) => self.transpile_fx_decl(ast, function),
                    ItemKind::Const(_) => unreachable!(),
                }).collect::<Vec<_>>()
        );

        items.extend(
            ast.items.iter()
                .map(|item| self.transpile_items(ast, item))
                .collect::<Vec<_>>()
        );

        CAst::new(items)
    }

    fn transpile_statement(&mut self, ast: &Ast, stmt_id: StatementId) -> Vec<CStatement> {
        let mut statements = vec![];
        let statement = ast.query_statement(stmt_id);
        let c_statement = match &statement.kind {
            StatementKind::Expression(expr) => {
                let (expr_statements, expr) = self.transpile_expr(ast, *expr);
                if let Some(expr_statements) = expr_statements {
                    statements.extend(expr_statements);
                }
                CStatement::Expr(expr)
            }
            StatementKind::Let(let_statement) => {
                let var = self.global_scope.variables.get(let_statement.variable_index);
                let var_name = self.get_variable_name(let_statement.variable_index);
                let (init_statements, init) = self.transpile_expr(ast, let_statement.initialiser);
                
                if let Some(init_statements) = init_statements {
                    statements.extend(init_statements);
                }

                CStatement::VarDecl(CVarDecl {
                    name: var_name,
                    ty: CType::try_from(&var.ty).expect("Unsupported type"),
                    init: Some(init)
                })
            }
            StatementKind::Const(const_statement) => {
                let var = self.global_scope.variables.get(const_statement.variable_index);
                let var_name = self.get_variable_name(const_statement.variable_index);
                let (init_statements, init) = self.transpile_expr(ast, const_statement.expr);
                
                if let Some(init_statements) = init_statements {
                    statements.extend(init_statements);
                }

                // In C, const declarations can be handled like regular variable declarations
                // but marked with const qualifier
                CStatement::VarDecl(CVarDecl {
                    name: var_name,
                    ty: CType::try_from(&var.ty).expect("Unsupported type"),
                    init: Some(init)
                })
            }
            StatementKind::While(while_statement) => {
                let (condition_statements, condition) = self.transpile_expr(ast, while_statement.condition);
                let (body_statements, body) = unreachable!();
                let mut while_body_statements = Vec::new();

                if let Some(condition_statements) = condition_statements {
                    while_body_statements.extend(condition_statements.clone());
                }

                let mut then_statements = match body_statements {
                    None => vec![],
                    Some(body_statements) => body_statements,
                };
                then_statements.push(CStatement::Expr(body));
                while_body_statements.push(CStatement::If(CIfStatement {
                    condition,
                    then_block: CBlockStatement { statements: then_statements },
                    else_block: Some(CBlockStatement { statements: vec![CStatement::Break]}),
                }));

                CStatement::While(CWhileStatement {
                    condition: CExpr::Bool(CBool { value: true }),
                    body: CBlockStatement { statements: while_body_statements }
                })
            }
            StatementKind::Return(return_statement) => {
                let return_value = return_statement.return_value.map(|expr| self.transpile_expr(ast, expr));
                return match return_value {
                    None => vec![CStatement::Return(CReturn { expr: None })],
                    Some((return_value_statements, expr)) => {
                        if let Some(return_value_statements) = return_value_statements {
                            statements.extend(return_value_statements);
                        }
                        statements.push(CStatement::Return(CReturn { expr: Some(expr) }));
                        statements
                    }
                };
            }
        };

        statements.push(c_statement);
        return statements;
    }

    fn transpile_expr(&mut self, ast: &Ast, expr_id: ExpressionId) -> (Option<Vec<CStatement>>, CExpr) {
        let expr = ast.query_expression(expr_id);
        match &expr.kind {
            ExpressionKind::Number(number) => (
                None, 
                CExpr::Number(CNumber { value: number.number }),
            ),
            ExpressionKind::Float(float) => (
                None, 
                CExpr::Float(CFloat { value: float.number }),
            ),
            ExpressionKind::Usize(usize_expr) => (
                None,
                CExpr::Usize(CUsize { value: usize_expr.number }),
            ),
            ExpressionKind::String(string) => (
                None,
                CExpr::String(string.string.clone()),
            ),
            ExpressionKind::Boolean(bool_expr) => (
                None,
                CExpr::Bool(CBool { value: bool_expr.value }),
            ),
            ExpressionKind::Binary(bin_expr) => self.transpile_binary_expression(ast, &bin_expr),
            ExpressionKind::Unary(unary_expr) => self.transpile_unary_expression(ast, &unary_expr),
            ExpressionKind::Parenthesised(paren_expr) => {
                let (expr_statements, expr) = self.transpile_expr(ast, paren_expr.expression);
                (expr_statements, CExpr::Parenthesised(Box::new(expr)))
            }
            ExpressionKind::Variable(var_expr) => (
                None,
                CExpr::Variable(CVarExpr { name: self.get_variable_name(var_expr.variable_index) }),
            ),
            ExpressionKind::Assignment(assignment_expr) => {
                let (assign_expr_statements, assign_expr) = self.transpile_expr(ast, assignment_expr.expression);
                (
                    assign_expr_statements,
                    CExpr::Assign(CAssignExpr {
                        name: self.get_variable_name(assignment_expr.variable_index),
                        expr: Box::new(assign_expr)
                    }),
                )
            }
            ExpressionKind::If(if_expr) => self.transpile_if_expression(ast, &expr, if_expr),
            ExpressionKind::Block(block_expr) => self.transpile_block_expression(ast, &expr, block_expr),
            ExpressionKind::Call(call_expr) => self.transpile_call_expression(ast, call_expr),
            ExpressionKind::CompoundBinary(_) => unimplemented!("CompoundBinary expressions not yet supported in C transpiler"),
            ExpressionKind::Break(_) => unimplemented!("Break expressions not yet supported in C transpiler"),
            ExpressionKind::Continue(_) => unimplemented!("Continue expressions not yet supported in C transpiler"),
            ExpressionKind::Array(_) => unimplemented!("Array expressions not yet supported in C transpiler"),
            ExpressionKind::IndexExpression(_) => unimplemented!("Index expressions not yet supported in C transpiler"),
            ExpressionKind::Tuple(_) => unimplemented!("Tuple expressions not yet supported in C transpiler"),
            ExpressionKind::TupleIndexExpression(_) => unimplemented!("TupleIndex expressions not yet supported in C transpiler"),
            ExpressionKind::Error(_) => panic!("Error expression"),
        }
    }

    fn transpile_binary_expression(&mut self, ast: &Ast, bin_expr: &&BinaryExpression) -> (Option<Vec<CStatement>>, CExpr) {
        let (left_statements, left) = self.transpile_expr(ast, bin_expr.left);
        let (right_statements, right) = self.transpile_expr(ast, bin_expr.right);
        let operator = CBinOp::try_from(&bin_expr.operator).expect("Unsupported binary operator");
        let mut statements =  Vec::new();

        if let Some(left_statements) = left_statements {
            statements.extend(left_statements);
        }

        if let Some(right_statements) = right_statements {
            statements.extend(right_statements);
        }

        (
            Some(statements),
            CExpr::Binary(CBinExpr {
                operator,
                left: Box::new(left),
                right: Box::new(right),
            })
        )
    }

    fn transpile_unary_expression(&mut self, ast: &Ast, unary_expr: &&UnaryExpression) -> (Option<Vec<CStatement>>, CExpr) {
        let (unary_statements, expr) = self.transpile_expr(ast, unary_expr.operand);
        let operator = CUnaryOp::try_from(&unary_expr.operator).expect("Unsupported unary operator");

        (
            unary_statements,
            CExpr::Unary(CUnaryExpr {
                operator,
                expr: Box::new(expr)
            })
        )
    }

    fn transpile_if_expression(&mut self, _ast: &Ast, _expr: &&Expression, _if_expr: &IfExpression) -> (Option<Vec<CStatement>>, CExpr) {
        todo!()
    }

    fn transpile_block_expression(&mut self, ast: &Ast, expr: &&Expression, block_expr: &BlockExpression) -> (Option<Vec<CStatement>>, CExpr) {
        let mut statements = Vec::new();
        let temp_returning_expr = !matches!(&expr.ty, Type::Void);
        let (temp_var, temp_var_name) = if temp_returning_expr {
            let temp_var_decl = self.next_temp_var_decl(&expr.ty);
            let temp_var_name = temp_var_decl.name.clone();
            statements.push(CStatement::VarDecl(temp_var_decl));
            let temp_var = CExpr::Variable(CVarExpr { name: temp_var_name.clone() });

            (Some(temp_var), Some(temp_var_name))
        } else {
            (None, None)
        };

        let returning_expr = block_expr.returning_expression(ast).map(|expr| self.transpile_expr(ast, expr));
        for statement in block_expr.statements.iter().take(match returning_expr {
            None => block_expr.statements.len(),
            Some(_) => block_expr.statements.len() - 1,
        }) {
            let temp_statements = self.transpile_statement(ast, *statement);
            statements.extend(temp_statements);
        }

        if let Some((expr_statements, expr)) = returning_expr {
            if let Some(expr_statements) = expr_statements {
                statements.extend(expr_statements);
            }

            if temp_returning_expr {
                statements.push(CStatement::Expr(CExpr::Assign(CAssignExpr {
                    name: temp_var_name.unwrap(),
                    expr: Box::new(expr)
                })));
            }
        }

        (
            Some(statements),
            temp_var.unwrap_or(CExpr::Bool(CBool { value: false })),
        )
    }

    fn transpile_call_expression(&mut self, ast: &Ast, call_expr: &CallExpression) -> (Option<Vec<CStatement>>, CExpr) {
        let fx = self.global_scope.functions.get(call_expr.fx_idx);
        let mut statements = Vec::new();
        let arguments = call_expr.arguments.iter().map(|arg| {
            let (arg_statements, arg_expr) = self.transpile_expr(ast, *arg);
            if let Some(arg_statements) = arg_statements {
                statements.extend(arg_statements);
            }
            arg_expr
        }).collect();

        (
            Some(statements),
            CExpr::Call(CCallExpr { name: fx.name.clone(), args: arguments })
        )
    }

    fn transpile_items(&mut self, ast: &Ast, item: &Item) -> CItem {
        match &item.kind {
            ItemKind::Statement(_) => panic!("Statement is not supported in global scope"),
            ItemKind::Function(function) => self.transpile_function(ast, function),
            ItemKind::Const(_) => unreachable!(),
        }
    }

    fn transpile_fx_decl(&mut self, _ast: &Ast, function: &FxDeclaration) -> CItem {
        let function = self.global_scope.functions.get(function.index);

        CItem::FxDecl(CFxDecl { 
            identifier: function.name.clone(),
            parameters: function.parameters.iter().map(|param_idx| {
                let param = self.global_scope.variables.get(*param_idx);
                CParams {
                    name: self.get_variable_name(*param_idx),
                    ty: CType::try_from(&param.ty).expect("Unsupported parameter type"),
                }
            }).collect(),
            return_type: CType::try_from(&function.return_type).expect("Unsupported return type"),
        })
    }

    fn transpile_function(&mut self, ast: &Ast, function: &FxDeclaration) -> CItem {
        let fx_decl = match self.transpile_fx_decl(ast, function) {
            CItem::FxDecl(fx_decl) => fx_decl,
            _ => unreachable!(),
        };

        let body = function.body.iter().map(|statement| self.transpile_statement(ast, *statement))
            .flatten().collect::<Vec<_>>();

        CItem::FxImpl(CFxImpl { identifier: fx_decl.identifier, parameters: fx_decl.parameters, body, return_type: fx_decl.return_type })
    }

    fn transpile_type(ty: &Type) -> String {
        return match ty {
            Type::Int => "int".to_string(),
            Type::Float => "float".to_string(),
            Type::String => "char*".to_string(),
            Type::Bool => "int".to_string(),
            Type::Void => "void".to_string(),
            Type::Usize => "size_t".to_string(),
            Type::Array(_, _) => panic!("Array types not supported in C codegen yet"),
            Type::Unresolved => panic!("Unresolved type"),
            Type::Tuple(_) => panic!("Tuple types not supported in C codegen yet"),
            Type::Error => panic!("Error type"),
        }
    }

    fn transpile_binary_operator(&self, operator: &BinaryOp) -> &'static str {
        return match &operator.kind {
            BinaryOpKind::Plus => "+",
            BinaryOpKind::Minus => "-",
            BinaryOpKind::Multiply => "*",
            BinaryOpKind::Divide => "/",
            BinaryOpKind::Modulo => "%",
            BinaryOpKind::Power => panic!("Power operator unsupported"),
            BinaryOpKind::Equals => "==",
            BinaryOpKind::NotEquals => "!=",
            BinaryOpKind::LessThan => "<",
            BinaryOpKind::LessThanOrEqual => "<=",
            BinaryOpKind::GreaterThan => ">",
            BinaryOpKind::GreaterThanOrEqual => ">=",
            BinaryOpKind::BitwiseAnd => "&",
            BinaryOpKind::BitwiseOr => "|",
            BinaryOpKind::BitwiseXor => "^",
            BinaryOpKind::ShiftLeft => "<<",
            BinaryOpKind::ShiftRight => ">>",
        }
    }

    fn transpile_unary_operator(&self, operator: &UnaryOp) -> &'static str {
        return match &operator.kind {
            UnaryOpKind::Negation => "-",
            UnaryOpKind::BitwiseNot => "~",
        };
    }

    fn is_valid_r_value(&mut self, ast: &Ast, expr_id: ExpressionId) -> bool {
        let expr = ast.query_expression(expr_id);

        return match &expr.kind {
            ExpressionKind::Number(_) => true,
            ExpressionKind::Float(_) => true,
            ExpressionKind::Usize(_) => true,
            ExpressionKind::String(_) => true,
            ExpressionKind::Boolean(_) => true,
            ExpressionKind::Unary(_) => self.is_valid_r_value(ast, expr.id),
            ExpressionKind::Variable(_) => true,
            ExpressionKind::Binary(bin_expr) => {
                let left = self.is_valid_r_value(ast, bin_expr.left);
                let right = self.is_valid_r_value(ast, bin_expr.right);
                left && right
            }
            ExpressionKind::Parenthesised(paren_expr) => self.is_valid_r_value(ast, paren_expr.expression),
            ExpressionKind::Assignment(assign_expr) => self.is_valid_r_value(ast, assign_expr.expression),
            ExpressionKind::Call(call_expr) => {
                for argument in call_expr.arguments.iter() {
                    if !self.is_valid_r_value(ast, *argument) {
                        return false;
                    }
                }
                true
            },
            ExpressionKind::If(_) => false,
            ExpressionKind::Block(_) => false,
            ExpressionKind::CompoundBinary(_) => false, // Compound binary expressions should be desugared before reaching here
            ExpressionKind::Break(_) => false,
            ExpressionKind::Continue(_) => false,
            ExpressionKind::Array(_) => false,
            ExpressionKind::IndexExpression(_) => false,
            ExpressionKind::Tuple(_) => false,
            ExpressionKind::TupleIndexExpression(_) => false,
            ExpressionKind::Error(_) => panic!("Error expression"),
        };
    }

    fn next_temp_var_decl(&mut self, ty: &Type) -> CVarDecl {
        let name = self.next_temp_var_name();
        return CVarDecl {
            name,
            ty: CType::try_from(ty).expect("Unresolved type"),
            init: None,
        };
    }

    fn next_temp_var_name(&mut self) -> String {
        let name = format!("_{}", self.temp_var_counter);
        self.temp_var_counter += 1;
        
        name
    }
}

impl CTranspiler<'_> {
    fn get_variable_name(&mut self, var_idx: VariableIndex) -> String {
        let var = self.global_scope.variables.get(var_idx);
        let shadowing_vars = self.shadowing_vars.get_mut(&var.name);
        let shadowing_vars = match shadowing_vars {
            None => {
                self.shadowing_vars.insert(var.name.clone(), vec![var_idx]);
                self.shadowing_vars.get_mut(&var.name).unwrap()
            }
            Some(shadowing_vars) => shadowing_vars,
        };

        let format = |index: usize| format!("{}_{}", var.name, index);
        for (index, var) in shadowing_vars.iter().rev().enumerate() {
            if var == &var_idx {
                return format(index);
            }
        }

        shadowing_vars.push(var_idx);
        return format(shadowing_vars.len() - 1);
    }
}