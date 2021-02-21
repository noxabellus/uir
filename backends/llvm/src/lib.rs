use std::collections::HashMap;

use llvm_sys::prelude::*;

use uir_core::{
	ty::*,
	ir::*
};

pub enum LLVMErr {
	InvalidFunctionKey(FunctionKey),
}

pub type LLVMResult<T = ()> = Result<T, LLVMErr>;

pub struct LLVMBackend<'c> {
	pub ctx: &'c Context,
	pub llctx: LLVMContextRef,
	pub types: HashMap<TyKey, LLVMTypeRef>,
	pub globals: HashMap<GlobalKey, LLVMValueRef>,
	pub functions: HashMap<FunctionKey, LLVMValueRef>,
}

impl<'c> LLVMBackend<'c> {
	pub fn emit_fn_body (&mut self, f: FunctionKey) -> LLVMResult<LLVMValueRef> {
		let _func = self.ctx.functions.get(f).ok_or(LLVMErr::InvalidFunctionKey(f))?;

		let llfunc = *self.functions.get(&f).ok_or(LLVMErr::InvalidFunctionKey(f))?;




		Ok(llfunc)
	}
}