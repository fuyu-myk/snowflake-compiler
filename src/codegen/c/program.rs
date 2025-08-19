use std::{fs::File, io::Write, process::Command};
use anyhow::anyhow;

use crate::{codegen::c::{ast::{CAst, CBlockStatement, CExpr, CItem, CParams, CStatement}, CTranspiler}, compilation_unit::CompilationUnit};


impl From<CAst> for CProgram {
    fn from(value: CAst) -> Self {
        Self { ast: value }
    }
}

pub struct CProgram {
    pub ast: CAst,
}

impl CProgram {
    const C_COMPILER: &'static str = "clang";
    const OUTPUT_FILE: &'static str = "out";
    const C_INPUT_FILE: &'static str = "out.c";

    pub fn from_compilation_unit(compilation_unit: &CompilationUnit) -> Self {
        compilation_unit.into()
    }

    pub fn source_code(&self) -> String {
        let mut generator = CCodegen::new();
        for item in &self.ast.items {
            generator.transpile_item(item);
        }
        generator.code
    }

    pub fn compile(&self) -> anyhow::Result<File> {
        let mut file = File::create(Self::C_INPUT_FILE)?;
        let transpiled_code = self.source_code();

        file.write_all(transpiled_code.as_bytes())?;
        Command::new(Self::C_COMPILER)
            .arg(Self::C_INPUT_FILE)
            .arg("-o")
            .arg(Self::OUTPUT_FILE)
            .status()?;

        Ok(file)
    }

    pub fn run(&self) -> anyhow::Result<i32> {
        let _ = self.compile()?;
        let run_result = Command::new(format!("./{}", Self::OUTPUT_FILE)).status()?;

        Ok(run_result.code().ok_or(
            anyhow!("Program exited without returning a value")
        )?)
    }
}

impl Into<CProgram> for &CompilationUnit {
    fn into(self) -> CProgram {
        let ast = CTranspiler::new(&self.global_scope).transpile(&self.ast);
        ast.into()
    }
}

struct CCodegen {
    indent: usize,
    code: String,
}

impl CCodegen {
    fn new() -> Self {
        Self { indent: 0, code: String::new() }
    }

    fn write_whitespace(&mut self) {
        self.code.push(' ');
    }

    fn write(&mut self, text: &str) {
        self.code.push_str(text);
    }

    fn write_indent(&mut self) {
        for _ in 0..self.indent {
            self.write("    ");
        }
    }

    fn transpile_item(&mut self, item: &CItem) {
        match item {
            CItem::Macro(name, value) => {
                self.write(format!("#define {} {}\n", name, value).as_str());
            }
            CItem::FxDecl(function) => {
                self.write(format!("{} {}(", function.return_type, function.identifier).as_str());
                self.transpile_params(&function.parameters);
                self.write(");\n");
            }
            CItem::FxImpl(function) => {
                self.write(format!("{} {}(", function.return_type, function.identifier).as_str());
                self.transpile_params(&function.parameters);
                self.write(") {\n");
                self.indent += 1;

                for statement in &function.body {
                    self.transpile_statement(statement);
                }
                self.indent -= 1;
                self.write("}\n");
            }
            CItem::VarDecl(_) => {
                unimplemented!()
            }
        }
    }

    fn transpile_params(&mut self, params: &Vec<CParams>) {
        for (index, param) in params.iter().enumerate() {
            if index != 0 {
                self.write(", ");
            }
            self.write(format!("{} {}", param.ty, param.name).as_str());
        }
    }

    fn transpile_statement(&mut self, statement: &CStatement) {
        self.write_indent();

        match statement {
            CStatement::VarDecl(var_decl) => {
                self.write(format!("{} {}", var_decl.ty, var_decl.name).as_str());
                if let Some(init) = &var_decl.init {
                    self.write(" = ");
                    self.transpile_expr(init);
                }
                self.write(";\n");
            }
            CStatement::Expr(expr) => {
                self.transpile_expr(expr);
                self.write(";\n");
            }
            CStatement::If(if_statement) => {
                self.write("if (");
                self.transpile_expr(&if_statement.condition);
                self.write(")");

                self.transpile_block(&if_statement.then_block);

                if let Some(else_block) = &if_statement.else_block {
                    self.write_indent();
                    self.write("else");
                    self.transpile_block(else_block);
                }
            }
            CStatement::While(while_statement) => {
                self.write("while (");
                self.transpile_expr(&while_statement.condition);
                self.write(")");

                self.transpile_block(&while_statement.body);
            }
            CStatement::Block(block_statement) => {
                self.transpile_block(block_statement);
            }
            CStatement::Return(return_statement) => {
                self.write("return");
                if let Some(expr) = &return_statement.expr {
                    self.write_whitespace();
                    self.transpile_expr(expr);
                }
                self.write(";\n");
            }
            CStatement::Break => {
                self.write("break;\n");
            }
        };
    }

    fn transpile_expr(&mut self, expr: &CExpr) {
        match expr {
            CExpr::Number(number) => {
                self.write(format!("{}", number.value).as_str());
            }
            CExpr::Float(float) => {
                self.write(format!("{}", float.value).as_str());
            }
            CExpr::Usize(number) => {
                self.write(format!("{}", number.value).as_str());
            }
            CExpr::String(string) => {
                self.write(format!("\"{}\"", string).as_str());
            }
            CExpr::Bool(bool) => {
                self.write(format!("{}", bool.value).as_str());
            }
            CExpr::Variable(var) => {
                self.write(var.name.as_str());
            }
            CExpr::Assign(assign_expr) => {
                self.write(format!("{} = ", assign_expr.name).as_str());
                self.transpile_expr(&assign_expr.expr);
            }
            CExpr::Binary(binary_expr) => {
                self.transpile_expr(&binary_expr.left);
                self.write(format!(" {} ", binary_expr.operator).as_str());
                self.transpile_expr(&binary_expr.right);
            }
            CExpr::Unary(unary_expr) => {
                self.write(format!("{}", unary_expr.operator).as_str());
                self.transpile_expr(&unary_expr.expr);
            }
            CExpr::Call(call_expr) => {
                self.write(call_expr.name.as_str());
                self.write("(");

                let mut first = true;
                for arg in &call_expr.args {
                    if first {
                        first = false;
                    } else {
                        self.write(", ");
                    }
                    self.transpile_expr(arg);
                }
                self.write(")");
            }
            CExpr::Parenthesised(paren_expr) => {
                self.write("(");
                self.transpile_expr(paren_expr);
                self.write(")");
            }
        }
    }

    fn transpile_block(&mut self, block: &CBlockStatement) {
        self.write(" {\n");
        self.indent += 1;

        for statement in &block.statements {
            self.transpile_statement(statement);
        }
        self.indent -= 1;

        self.write_indent();
        self.write("}\n");
    }
}