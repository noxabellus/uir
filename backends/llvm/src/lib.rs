#![allow(non_upper_case_globals, dead_code)]

use std::{cell::{Ref, RefCell, RefMut}, collections::HashMap };


#[macro_use]
pub(crate) mod wrapper;
pub(crate) mod abi;

use abi::Abi;
use llvm_sys::core::*;
use llvm_sys::prelude::*;

use uir_core::{
	support::utils::ref_and_then,
	ty::*,
	ir::*
};

use wrapper::*;


#[derive(Default)]
pub struct LLVMMutableState {
	pub types: HashMap<TyKey, LLVMType>,
	pub globals: HashMap<GlobalKey, LLVMValue>,
	pub functions: HashMap<FunctionKey, LLVMValue>,
	pub target_signature_types: HashMap<TyKey, abi::Function>,
}

pub struct LLVMBackend<'c> {
	pub ctx: ContextCollapsePredictor<'c>,
	pub abi: &'c dyn Abi,
	pub llctx: LLVMContextRef,
	pub llmod: LLVMModuleRef,
	pub state: RefCell<LLVMMutableState>,
}

impl<'c> LLVMBackend<'c> {
	pub fn new (ctx: &'c Context) -> Option<Self> {
		let abi = abi::get_abi(ctx.target.as_ref())?;
		let ctx = ctx.predict_collapse();

		let llctx = unsafe { LLVMContextCreate() };

		// TODO: module names
		let llmod = unsafe { LLVMModuleCreateWithNameInContext(llvm_str!("UIR_MODULE"), llctx) };

		let state = RefCell::default();

		Some(Self {
			abi,
			ctx,
			llctx,
			llmod,
			state
		})
	}

	pub fn type_map (&self) -> Ref<HashMap<TyKey, LLVMType>> {
		Ref::map(self.state.borrow(), |state| &state.types)
	}

	pub fn type_map_mut (&self) -> RefMut<HashMap<TyKey, LLVMType>> {
		RefMut::map(self.state.borrow_mut(), |state| &mut state.types)
	}

	pub fn global_map (&self) -> Ref<HashMap<GlobalKey, LLVMValue>> {
		Ref::map(self.state.borrow(), |state| &state.globals)
	}

	pub fn global_map_mut (&self) -> RefMut<HashMap<GlobalKey, LLVMValue>> {
		RefMut::map(self.state.borrow_mut(), |state| &mut state.globals)
	}

	pub fn function_map (&self) -> Ref<HashMap<FunctionKey, LLVMValue>> {
		Ref::map(self.state.borrow(), |state| &state.functions)
	}

	pub fn function_map_mut (&self) -> RefMut<HashMap<FunctionKey, LLVMValue>> {
		RefMut::map(self.state.borrow_mut(), |state| &mut state.functions)
	}

	pub fn target_signature_type_map (&self) -> Ref<HashMap<TyKey, abi::Function>> {
		Ref::map(self.state.borrow(), |state| &state.target_signature_types)
	}

	pub fn target_signature_type_map_mut (&self) -> RefMut<HashMap<TyKey, abi::Function>> {
		RefMut::map(self.state.borrow_mut(), |state| &mut state.target_signature_types)
	}



	pub fn prim_ty (&self, prim: PrimitiveTy) -> LLVMType {
		use PrimitiveTy::*;

		match prim {
			Bool
			=> LLVMType::int1(self.llctx),

			| SInt8 | SInt16 | SInt32 | SInt64 | SInt128
			| UInt8 | UInt16 | UInt32 | UInt64 | UInt128
			=> LLVMType::int(self.llctx, (prim.size() * 8) as _),

			Real32
			=> LLVMType::float(self.llctx),

			Real64
			=> LLVMType::double(self.llctx),
		}
	}

	pub fn emit_ty (&self, ty_key: TyKey) -> LLVMType {
		if let Some(llty) = self.type_map().get(&ty_key) {
			return *llty
		}

		let ty = self.ctx.tys.get_value(ty_key).expect("valid ty key");

		let llty = {
			use TyData::*;

			match &ty.data {
				Void => LLVMType::void(self.llctx),

				Block => LLVMType::label(self.llctx),

				Primitive(prim) => self.prim_ty(*prim),

				Pointer { target_ty } => self.emit_ty(*target_ty).as_pointer(0),

				Array { length, element_ty } => self.emit_ty(*element_ty).as_array(*length as _),

				Structure { field_tys } => {
					let llname = if let Some(name) = ty.name.as_ref() {
						LLVMString::from(name)
					} else {
						LLVMString::from(format!("$s({})", self.ctx.tys.get_index(ty_key).unwrap()))
					};

					let llty = LLVMType::named_empty_structure(self.llctx, llname);

					self.type_map_mut().insert(ty_key, llty);

					let elem_types = field_tys.iter().map(|&ty_key| self.emit_ty(ty_key)).collect::<Vec<_>>();
					llty.structure_set_body(elem_types.as_slice(), false);

					llty
				}

				Function { .. } => {
					dbg!(self.abi_info(ty_key).unwrap()).ty
				}
			}
		};

		self.type_map_mut().insert(ty_key, llty);

		llty
	}

	pub fn abi_info(&self, ty_key: TyKey) -> Option<Ref<abi::Function>>
	{
		let ty = self.ctx.tys.get_value(ty_key)?;

		match &ty.data {
			TyData::Function { parameter_tys, result_ty } => {
				{
					let existing = ref_and_then(self.target_signature_type_map(), |map| map.get(&ty_key));
					if existing.is_some() { return existing }
				} {
					let param_types = parameter_tys.iter().map(|&ty_key| self.emit_ty(ty_key)).collect::<Vec<_>>();
					let result_type = result_ty.map(|ty_key| self.emit_ty(ty_key));
					let function_data = self.abi.get_info(self.llctx, param_types.as_slice(), result_type, false);

					self.target_signature_type_map_mut().insert(ty_key, function_data);
				}

				ref_and_then(self.target_signature_type_map(), |map| map.get(&ty_key))
			},

			_ => None
		}
	}


	pub fn emit_constant (&self, constant: &Constant) -> LLVMValue {
		use Constant::*;

		match constant {
			Null(ty_key) => LLVMValue::const_null(self.emit_ty(*ty_key)),

			Bool(val) => LLVMValue::const_int(self.prim_ty(PrimitiveTy::Bool), *val as _),

			SInt8(val) => LLVMValue::const_int(self.prim_ty(PrimitiveTy::SInt8), *val as _),
			SInt16(val) => LLVMValue::const_int(self.prim_ty(PrimitiveTy::SInt16), *val as _),
			SInt32(val) => LLVMValue::const_int(self.prim_ty(PrimitiveTy::SInt32), *val as _),
			SInt64(val) => LLVMValue::const_int(self.prim_ty(PrimitiveTy::SInt64), *val as _),

			SInt128(val) => {
				LLVMValue::const_int(
					self.prim_ty(PrimitiveTy::SInt128),
					*val as _
				)
			}

			UInt8(val) => LLVMValue::const_int(self.prim_ty(PrimitiveTy::UInt8), *val as _),
			UInt16(val) => LLVMValue::const_int(self.prim_ty(PrimitiveTy::UInt16), *val as _),
			UInt32(val) => LLVMValue::const_int(self.prim_ty(PrimitiveTy::UInt32), *val as _),
			UInt64(val) => LLVMValue::const_int(self.prim_ty(PrimitiveTy::UInt64), *val as _),

			UInt128(val) =>  {
				LLVMValue::const_int(
					self.prim_ty(PrimitiveTy::UInt128),
					*val
				)
			}

			Real32(val) => LLVMValue::const_real(self.prim_ty(PrimitiveTy::Real32), *val as _),
			Real64(val) => LLVMValue::const_real(self.prim_ty(PrimitiveTy::Real64), *val),

			Aggregate(_ty_key, _data) => {
				todo!()
			}
		}
	}


	pub fn emit_global (&self, global_key: GlobalKey) -> LLVMValue {
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

		let llglobal = LLVMValue::create_global(self.llmod, llty, llname);

		if let Some(init_const) = global.init.as_ref() {
			let llinit = self.emit_constant(init_const);

			llglobal.set_global_initializer(llinit)
		}

		llglobal
	}


	pub fn emit_function_decl (&self, function_key: FunctionKey) -> LLVMValue {
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

		LLVMValue::create_function(self.llmod, llty, llname)
	}
}


#[cfg(test)]
mod llvm_tests {
	use super::*;

	use uir_core::{ ir, builder, support::slotmap::AsKey};

	#[test]
	fn what_do () {
		let mut ctx = ir::Context::new();
		let mut builder = builder::Builder::new(&mut ctx);

		let s32_t = builder.sint32_ty().as_key();
		let s64_t = builder.sint64_ty().as_key();

		let u_a32_t = builder.structure_ty(vec! [
			s32_t, s32_t
		]).unwrap().set_name("u_a32_t").as_key();

		let u_a64_t = builder.structure_ty(vec! [
			s64_t, s64_t
		]).unwrap().set_name("u_a64_t").as_key();

		let u_b32_t = builder.structure_ty(vec! [
			s32_t, s32_t, s32_t, s32_t
		]).unwrap().set_name("u_b32_t").as_key();

		let u_b64_t = builder.structure_ty(vec! [
			s64_t, s64_t, s64_t, s64_t
		]).unwrap().set_name("u_b64_t").as_key();

		let f_a32_t = builder.function_ty(vec![ u_a32_t ], Some(u_a32_t)).unwrap().as_key();
		let f_a64_t = builder.function_ty(vec![ u_a64_t ], Some(u_a64_t)).unwrap().as_key();
		let f_b32_t = builder.function_ty(vec![ u_b32_t ], Some(u_b32_t)).unwrap().as_key();
		let f_b64_t = builder.function_ty(vec![ u_b64_t ], Some(u_b64_t)).unwrap().as_key();

		let backend = LLVMBackend::new(&ctx).unwrap();

		let ll_f_a32_t = backend.emit_ty(f_a32_t);
		let ll_f_a64_t = backend.emit_ty(f_a64_t);
		let ll_f_b32_t = backend.emit_ty(f_b32_t);
		let ll_f_b64_t = backend.emit_ty(f_b64_t);

		let f_a32_abi = backend.abi_info(f_a32_t).unwrap();
		let f_a64_abi = backend.abi_info(f_a64_t).unwrap();
		let f_b32_abi = backend.abi_info(f_b32_t).unwrap();
		let f_b64_abi = backend.abi_info(f_b64_t).unwrap();

		let f_a32 = LLVMValue::create_function(backend.llmod, ll_f_a32_t, "f_a32");
		let f_a64 = LLVMValue::create_function(backend.llmod, ll_f_a64_t, "f_a64");
		let f_b32 = LLVMValue::create_function(backend.llmod, ll_f_b32_t, "f_b32");
		let f_b64 = LLVMValue::create_function(backend.llmod, ll_f_b64_t, "f_b64");

		f_a32_abi.apply_attributes(backend.llctx, f_a32);
		f_a64_abi.apply_attributes(backend.llctx, f_a64);
		f_b32_abi.apply_attributes(backend.llctx, f_b32);
		f_b64_abi.apply_attributes(backend.llctx, f_b64);



		for &(llty, expect) in &[
			(f_a32, "declare i64 @f_a32(i64)"),
			(f_a64, "declare { i64, i64 } @f_a64(i64, i64)"),
			(f_b32, "declare { i64, i64 } @f_b32(i64, i64)"),
			(f_b64, "declare void @f_b64(%u_b64_t*, %u_b64_t*)"),

			// TODO: implement proper attributes when llvm doesnt suck
			// (f_b64, "declare void @f_b64(%u_b64_t* sret, %u_b64_t* byval(%u_b64_t) align 8)"),
		] {
			assert_eq!(dbg!(format!("{:?}", llty)), expect)
		}
	}
}