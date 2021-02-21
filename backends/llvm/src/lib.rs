#![allow(non_upper_case_globals)]

use std::{cell::{Ref, RefCell, RefMut}, collections::HashMap};

use llvm_sys::core::*;
use llvm_sys::prelude::*;

use uir_core::{
	ty::*,
	ir::*
};

pub const LLVMFalse: LLVMBool = 0;
pub const LLVMTrue: LLVMBool = 1;



pub struct LLVMString {
	bytes: Vec<u8>,
}

impl From<String> for LLVMString {
	fn from (s: String) -> LLVMString {
		let mut bytes = s.into_bytes();

		for &byte in bytes.iter() {
			assert_ne!(byte, 0);
		}

		bytes.push(0);

		Self {
			bytes
		}
	}
}

impl From<&str> for LLVMString {
	fn from (s: &str) -> LLVMString {
		Self::from(s.to_owned())
	}
}

impl From<&String> for LLVMString {
	fn from (s: &String) -> LLVMString {
		Self::from(s.to_owned())
	}
}

impl LLVMString {
	pub fn into_bytes (self) -> Vec<u8> {
		self.bytes
	}

	pub fn as_ptr (&self) -> *const i8 {
		self.bytes.as_ptr() as *const i8
	}
}


pub struct LLVMMutableState {
	pub types: HashMap<TyKey, LLVMTypeRef>,
	pub globals: HashMap<GlobalKey, LLVMValueRef>,
	pub functions: HashMap<FunctionKey, LLVMValueRef>,
}

pub struct LLVMBackend<'c> {
	pub ctx: ContextCollapsePredictor<'c>,
	pub llctx: LLVMContextRef,
	pub llmod: LLVMModuleRef,
	pub state: RefCell<LLVMMutableState>,
}

impl<'c> LLVMBackend<'c> {
	pub fn type_map (&self) -> Ref<HashMap<TyKey, LLVMTypeRef>> {
		Ref::map(self.state.borrow(), |state| &state.types)
	}

	pub fn type_map_mut (&self) -> RefMut<HashMap<TyKey, LLVMTypeRef>> {
		RefMut::map(self.state.borrow_mut(), |state| &mut state.types)
	}

	pub fn global_map (&self) -> Ref<HashMap<GlobalKey, LLVMValueRef>> {
		Ref::map(self.state.borrow(), |state| &state.globals)
	}

	pub fn global_map_mut (&self) -> RefMut<HashMap<GlobalKey, LLVMValueRef>> {
		RefMut::map(self.state.borrow_mut(), |state| &mut state.globals)
	}

	pub fn function_map (&self) -> Ref<HashMap<FunctionKey, LLVMValueRef>> {
		Ref::map(self.state.borrow(), |state| &state.functions)
	}

	pub fn function_map_mut (&self) -> RefMut<HashMap<FunctionKey, LLVMValueRef>> {
		RefMut::map(self.state.borrow_mut(), |state| &mut state.functions)
	}



	pub fn prim_ty (&self, prim: PrimitiveTy) -> LLVMTypeRef { unsafe {
		use PrimitiveTy::*;

		match prim {
			Bool
			=> LLVMInt1TypeInContext(self.llctx),

			| SInt8 | SInt16 | SInt32 | SInt64 | SInt128
			| UInt8 | UInt16 | UInt32 | UInt64 | UInt128
			=> LLVMIntTypeInContext(self.llctx, (prim.size() * 8) as _),

			Real32
			=> LLVMFloatTypeInContext(self.llctx),

			Real64
			=> LLVMDoubleTypeInContext(self.llctx),
		}
	} }

	pub fn emit_ty (&self, ty_key: TyKey) -> LLVMTypeRef {
		if let Some(llty) = self.type_map().get(&ty_key) {
			return *llty
		}

		let ty = self.ctx.tys.get_value(ty_key).expect("valid ty key");

		let llty = unsafe {
			use TyData::*;

			match &ty.data {
				Void => LLVMVoidTypeInContext(self.llctx),

				Block => LLVMLabelTypeInContext(self.llctx),

				Primitive(prim) => self.prim_ty(*prim),

				Pointer { target_ty } => LLVMPointerType(self.emit_ty(*target_ty), 0),

				Array { length, element_ty } => LLVMArrayType(self.emit_ty(*element_ty), *length as _),

				Structure { field_tys } => {
					let mut elem_types = field_tys.iter().map(|&ty_key| self.emit_ty(ty_key)).collect::<Vec<_>>();

					if let Some(name) = ty.name.as_ref() {
						let llname = LLVMString::from(name);
						let s = LLVMStructCreateNamed(self.llctx, llname.as_ptr());
						LLVMStructSetBody(s, elem_types.as_mut_ptr(), elem_types.len() as _, LLVMFalse);
						s
					} else {
						LLVMStructTypeInContext(self.llctx, elem_types.as_mut_ptr(), elem_types.len() as _, LLVMFalse)
					}
				}

				Function { parameter_tys, result_ty } => {
					let mut param_types = parameter_tys.iter().map(|&ty_key| self.emit_ty(ty_key)).collect::<Vec<_>>();
					let result_type = if let Some(ty_key) = result_ty {
						self.emit_ty(*ty_key)
					} else {
						LLVMVoidTypeInContext(self.llctx)
					};

					LLVMFunctionType(result_type, param_types.as_mut_ptr(), param_types.len() as _, LLVMFalse)
				}
			}
		};

		self.type_map_mut().insert(ty_key, llty);

		llty
	}


	pub fn emit_constant (&self, constant: &Constant) -> LLVMValueRef { unsafe {
		use Constant::*;

		match constant {
			Null(ty_key) => LLVMConstNull(self.emit_ty(*ty_key)),

			Bool(val) => LLVMConstInt(self.prim_ty(PrimitiveTy::Bool), *val as _, LLVMFalse),

			SInt8(val) => LLVMConstInt(self.prim_ty(PrimitiveTy::SInt8), *val as _, LLVMTrue),
			SInt16(val) => LLVMConstInt(self.prim_ty(PrimitiveTy::SInt16), *val as _, LLVMTrue),
			SInt32(val) => LLVMConstInt(self.prim_ty(PrimitiveTy::SInt32), *val as _, LLVMTrue),
			SInt64(val) => LLVMConstInt(self.prim_ty(PrimitiveTy::SInt64), *val as _, LLVMTrue),

			SInt128(val) => {
				LLVMConstIntOfArbitraryPrecision(
					self.prim_ty(PrimitiveTy::SInt128),
					2,
					std::mem::transmute::<_, [u64; 2]>(*val).as_ptr()
				)
			}

			UInt8(val) => LLVMConstInt(self.prim_ty(PrimitiveTy::UInt8), *val as _, LLVMFalse),
			UInt16(val) => LLVMConstInt(self.prim_ty(PrimitiveTy::UInt16), *val as _, LLVMFalse),
			UInt32(val) => LLVMConstInt(self.prim_ty(PrimitiveTy::UInt32), *val as _, LLVMFalse),
			UInt64(val) => LLVMConstInt(self.prim_ty(PrimitiveTy::UInt64), *val as _, LLVMFalse),

			UInt128(val) =>  {
				LLVMConstIntOfArbitraryPrecision(
					self.prim_ty(PrimitiveTy::UInt128),
					2,
					std::mem::transmute::<_, [u64; 2]>(*val).as_ptr()
				)
			}

			Real32(val) => LLVMConstReal(self.prim_ty(PrimitiveTy::Real32), *val as _),
			Real64(val) => LLVMConstReal(self.prim_ty(PrimitiveTy::Real64), *val),

			Aggregate(_ty_key, _data) => {
				todo!()
			}
		}
	} }


	pub fn emit_global (&self, global_key: GlobalKey) -> LLVMValueRef {
		if let Some(llglobal) = self.global_map_mut().get(&global_key) {
			return *llglobal
		}

		let global = self.ctx.globals.get_value(global_key).expect("valid global key");

		let llty = self.emit_ty(global.ty);

		let llname = if let Some(name) = global.name.as_ref() {
			LLVMString::from(name)
		} else {
			LLVMString::from(format!("$g({})", self.ctx.globals.get_index(global_key).unwrap()))
		};

		let llglobal = unsafe { LLVMAddGlobal(self.llmod, llty, llname.as_ptr()) };

		if let Some(init_const) = global.init.as_ref() {
			let llinit = self.emit_constant(init_const);

			unsafe { LLVMSetInitializer(llglobal, llinit) }
		}

		llglobal
	}


	pub fn emit_function_decl (&self, function_key: FunctionKey) -> LLVMValueRef {
		if let Some(llfunction) = self.function_map_mut().get(&function_key) {
			return *llfunction
		}

		let function = self.ctx.functions.get_value(function_key).expect("valid function key");

		let llty = self.emit_ty(function.ty);

		let llname = if let Some(name) = function.name.as_ref() {
			LLVMString::from(name)
		} else {
			LLVMString::from(format!("$f({})", self.ctx.functions.get_index(function_key).unwrap()))
		};

		unsafe { LLVMAddFunction(self.llmod, llname.as_ptr(), llty) }
	}
}


// #[cfg(test)]
// mod llvm_tests {
// 	use super::*;
// }