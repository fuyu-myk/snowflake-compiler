use anyhow::Result;
use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    values::PointerValue,
    AddressSpace,
};


/// Runtime support for LLVM backend - handles panic, abort, and I/O functions
pub struct LLVMRuntime;

impl LLVMRuntime {
    /// Generate a panic with message that prints to stderr and calls abort()
    pub fn generate_panic_with_message<'ctx>(
        context: &'ctx Context,
        module: &Module<'ctx>,
        builder: &Builder<'ctx>,
        message: &str
    ) -> Result<()> {
        Self::declare_runtime_functions(context, module)?;
        
        let panic_msg = format!("PANIC: {}", message);
        let message_global = Self::create_string_literal(context, module, &panic_msg)?;
        
        let puts_fn = module.get_function("puts")
            .expect("puts function should be declared");
        
        builder.build_call(
            puts_fn,
            &[message_global.into()],
            "puts_call"
        )?;
        
        // Call abort()
        let abort_fn = module.get_function("abort")
            .expect("abort function should be declared");
        
        builder.build_call(abort_fn, &[], "abort_call")?;
        builder.build_unreachable()?;
        
        Ok(())
    }
    
    /// Declare required runtime functions (puts, abort, etc.)
    pub fn declare_runtime_functions<'ctx>(context: &'ctx Context, module: &Module<'ctx>) -> Result<()> {
        if module.get_function("abort").is_none() {
            let abort_type = context.void_type().fn_type(&[], false);
            module.add_function("abort", abort_type, None);
        }
        
        if module.get_function("puts").is_none() {
            let ptr_type = context.ptr_type(AddressSpace::default());
            let i32_type = context.i32_type();
            let puts_type = i32_type.fn_type(&[ptr_type.into()], false);
            module.add_function("puts", puts_type, None);
        }
        
        Ok(())
    }
    
    /// Create a string literal as a global constant
    pub fn create_string_literal<'ctx>(context: &'ctx Context, module: &Module<'ctx>, text: &str) -> Result<PointerValue<'ctx>> {
        let string_type = context.i8_type().array_type(text.len() as u32 + 1);
        let string_global = module.add_global(string_type, Some(AddressSpace::default()), "str");
        
        let mut chars: Vec<_> = text.bytes().map(|b| context.i8_type().const_int(b as u64, false)).collect();
        chars.push(context.i8_type().const_int(0, false));
        
        let string_const = context.i8_type().const_array(&chars);
        string_global.set_initializer(&string_const);
        string_global.set_constant(true);
        
        Ok(string_global.as_pointer_value())
    }
    
    /// Generate an unreachable error with message (for bounds checking, etc.)
    pub fn generate_unreachable_error<'ctx>(
        context: &'ctx Context,
        module: &Module<'ctx>,
        builder: &Builder<'ctx>,
        error_message: &str
    ) -> Result<()> {
        // Treat unreachable errors the same as panics
        Self::generate_panic_with_message(context, module, builder, &format!("UNREACHABLE: {}", error_message))
    }

    /// Declare common I/O functions that might be needed
    pub fn declare_io_functions<'ctx>(context: &'ctx Context, module: &Module<'ctx>) -> Result<()> {
        let ptr_type = context.ptr_type(AddressSpace::default());
        let i32_type = context.i32_type();

        if module.get_function("puts").is_none() {
            let puts_type = i32_type.fn_type(&[ptr_type.into()], false);
            module.add_function("puts", puts_type, None);
        }

        if module.get_function("printf").is_none() {
            let printf_type = i32_type.fn_type(&[ptr_type.into()], true); // variadic
            module.add_function("printf", printf_type, None);
        }

        Ok(())
    }
}