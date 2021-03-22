use std::{ffi::CStr, mem::MaybeUninit};

use llvm_sys::{execution_engine::*, target::*};

use crate::{
	wrapper::*,
	Emitter,
};


pub struct Jit {
	pub module: LLVMModule,
	execution_engine: LLVMExecutionEngineRef,
}

impl Jit {
	pub fn for_module (mut module: LLVMModule) -> Self {
		unsafe {
			module.leak();

			assert!(LLVM_InitializeNativeTarget() == LLVM_OK, "Failed to init native target");
			assert!(LLVM_InitializeNativeAsmPrinter() == LLVM_OK, "Failed to init native asm printer");
			assert!(LLVM_InitializeNativeAsmParser() == LLVM_OK, "Failed to init native asm parser");

			LLVMLinkInMCJIT();


			let mut err_msg = MaybeUninit::<*mut i8>::uninit();
			let mut execution_engine = MaybeUninit::<LLVMExecutionEngineRef>::uninit();

			if LLVMCreateExecutionEngineForModule(execution_engine.as_mut_ptr(), module.inner(), err_msg.as_mut_ptr()) != LLVM_OK {
				let cstr = CStr::from_ptr(err_msg.assume_init()).to_str().unwrap();
				panic!("Failed to create execution engine: {}", cstr);
				// LLVMDisposeMessage(err_msg);
			}

			let execution_engine = execution_engine.assume_init();

			Self {
				module,
				execution_engine,
			}
		}
	}

	pub fn new (emitter: &mut Emitter) -> Self {
		assert!(emitter.abi.is_native(), "Cannot JIT non-native code");

		Self::for_module(emitter.ll.module.take())
	}

	pub fn map_global (&mut self, name: impl ToLLVMText, addr: *mut ()) {
		unsafe {
			let global = LLVMGetNamedGlobal(self.module.inner(), name.to_lltext());

			LLVMAddGlobalMapping(self.execution_engine, global, addr as _)
		}
	}

	pub fn get_global (&mut self, name: impl ToLLVMText) -> *mut () {
		unsafe { LLVMGetGlobalValueAddress(self.execution_engine, name.to_lltext()) as _ }
	}

	pub fn get_function (&mut self, name: impl ToLLVMText) -> *const () {
		unsafe { LLVMGetFunctionAddress(self.execution_engine, name.to_lltext()) as _ }
	}

	pub fn free_function (&mut self, name: impl ToLLVMText) {
		unsafe {
			let function = LLVMGetNamedFunction(self.module.inner(), name.to_lltext());

			LLVMFreeMachineCodeForFunction(self.execution_engine, function)
		}
	}

	// pub fn map_global (&mut self, global: LLVMValue, addr: *mut ()) {
	// 	unsafe {
	// 		LLVMAddGlobalMapping(self.execution_engine, global.into(), addr as _)
	// 	}
	// }

	// pub fn get_global (&mut self, global: LLVMValue) -> *mut () {
	// 	unsafe {
	// 		let name = LLVMGetValueName2(global.into(), std::ptr::null_mut());
	// 		LLVMGetGlobalValueAddress(self.execution_engine, name) as _
	// 	}
	// }

	// pub fn get_function (&mut self, function: LLVMValue) -> *const () {
	// 	unsafe {
	// 		let name = LLVMGetValueName2(function.into(), std::ptr::null_mut());
	// 		LLVMGetFunctionAddress(self.execution_engine, name) as _
	// 	}
	// }

	// pub fn free_function (&mut self, function: LLVMValue) {
	// 	unsafe {
	// 		LLVMFreeMachineCodeForFunction(self.execution_engine, function.into())
	// 	}
	// }
}


impl Drop for Jit {
	fn drop (&mut self) {
		unsafe {
			LLVMDisposeExecutionEngine(self.execution_engine);
		}
	}
}