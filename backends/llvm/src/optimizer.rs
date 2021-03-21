use llvm_sys::transforms::pass_manager_builder::*;

use crate::{
	wrapper::*,
	Emitter,
};


pub struct Optimizer {
	builder: LLVMPassManagerBuilderRef,
	module: LLVMModule,
	pass: Option<LLVMPassManagerRef>,
	opt_level: u32,
}

impl Optimizer {
	pub fn new (emitter: &Emitter) -> Self {
		let builder = unsafe { LLVMPassManagerBuilderCreate() };

		Self { builder, module: emitter.module.borrow(), pass: None, opt_level: 0 }
	}

	pub fn set_level (&mut self, opt_level: u32) {
		unsafe { LLVMPassManagerBuilderSetOptLevel(self.builder, opt_level) }
		if let Some(old_pass) = self.pass.take() {
			unsafe { LLVMDisposePassManager(old_pass) }
		}
	}

	pub fn get_level (&self) -> u32 {
		self.opt_level
	}

	pub fn with_level (emitter: &Emitter, opt_level: u32) -> Self {
		let mut s = Self::new(emitter);
		s.set_level(opt_level);
		s
	}

	pub fn function_pass (&mut self) -> Option<LLVMPassManagerRef> {
		if self.pass.is_some() {
			self.pass
		} else { unsafe {
			let pass = LLVMCreateFunctionPassManagerForModule(self.module.inner());

			if LLVMInitializeFunctionPassManager(pass) != LLVM_OK { return None }

			LLVMPassManagerBuilderPopulateFunctionPassManager(self.builder, pass);

			if LLVMFinalizeFunctionPassManager(pass) != LLVM_OK { return None }

			self.pass.replace(pass);

			Some(pass)
		} }
	}

	pub fn optimize (&mut self, function: LLVMValue) -> bool {
		assert!(function.is_function_node(), "Expected a function for optimizer");
		debug_assert!(function.get_global_parent() == self.module.inner());
		let function_pass = self.function_pass().expect("valid opt level");
		unsafe { LLVMRunFunctionPassManager(function_pass, function.into()) == LLVM_TRUE }
	}
}


impl Drop for Optimizer {
	fn drop (&mut self) { unsafe {
		if let Some(pass) = self.pass.take() { LLVMDisposePassManager(pass) }
		LLVMPassManagerBuilderDispose(self.builder);
	} }
}