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
					self.abi_info(ty_key).unwrap().ty
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
	use std::fmt;


use llvm_sys::LLVMTypeKind::*;

    use super::*;

	use llvm_sys::bit_reader::LLVMParseBitcodeInContext2;
    use uir_core::{builder, ir, support::slotmap::AsKey};

	macro_rules! build_c_abi_str {
		(%MAIN% $name:ident ($( $field_name:ident : $field_ty:ident ),*)) => {
			concat!("int main () {\n",
				"\tint $counter = 0;\n",
				$( "\t",stringify!($field_ty)," ",stringify!($field_name)," = (",stringify!($field_ty),") ++$counter;\n", )*
				"\tfn_direct_",stringify!($name),"(",stringify!($($field_name),*),");\n",
				"\tfn_struct_",stringify!($name),"((",stringify!($name),") { ",stringify!($($field_name),*)," });\n",
				"\treturn 0;\n",
			"}\n")
		};
		(%BASE%) => {
r#"typedef void void_ty;
typedef char bool;
typedef float real32_ty;
typedef double real64_ty;
typedef char sint8_ty;
typedef short sint16_ty;
typedef int sint32_ty;
typedef long sint64_ty;
typedef unsigned char uint8_ty;
typedef unsigned short uint16_ty;
typedef unsigned int uint32_ty;
typedef unsigned long uint64_ty;
"#
		};
		( $name:ident ($( $field_name:ident : $field_ty:ident ),*) ) => {
			concat!(
				build_c_abi_str!(%BASE%),
				"typedef struct {\n",
					$( "\t",stringify!($field_ty)," ",stringify!($field_name),";\n", )*
				"} ", stringify!($name),";\n",
				"extern ",build_c_abi_str!(%GET_TY% $name ($($field_name)*))," fn_direct_",stringify!($name),"(",stringify!($($field_ty),*),");\n",
				"extern ",stringify!($name)," fn_struct_",stringify!($name), "(", stringify!($name), ");\n",
				build_c_abi_str!(%MAIN% $name ($( $field_name : $field_ty ),*))
			)
		};

		(%GET_TY% $struct_name:ident ()) => { "void" };
		(%GET_TY% $struct_name:ident ($single:ident)) => { stringify!($single) };
		(%GET_TY% $struct_name:ident ($first:ident $($more:ident)+)) => { stringify!($struct_name) };
	}

	macro_rules! build_abi_tests {
		( $(
			$name:ident ($( $field_name:ident : $field_ty:ident ),*)
		)* ) => { {
			$( {
				let mut ctx = ir::Context::new();
				let mut builder = builder::Builder::new(&mut ctx);

				let tys = &[ 	$( builder.$field_ty().as_key() ),* ];
				let struct_ty = builder.structure_ty(tys.to_vec()).unwrap().set_name(stringify!($name)).as_key();

				let direct_function_ty = {
					let ret_ty =
						match tys.len() {
							0 => None,
							1 => Some(tys[0]),
							_ => Some(struct_ty),
						};

					builder.function_ty(tys.to_vec(), ret_ty).unwrap().as_key()
				};

				let struct_function_ty = builder.function_ty(vec! [ struct_ty ], Some(struct_ty)).unwrap().as_key();

				let backend = LLVMBackend::new(&ctx).unwrap();

				let ll_direct_function_ty = backend.emit_ty(direct_function_ty);
				let ll_struct_function_ty = backend.emit_ty(struct_function_ty);

				let direct_function_abi = backend.abi_info(direct_function_ty).unwrap();
				let struct_function_abi = backend.abi_info(struct_function_ty).unwrap();

				let ll_direct_function = LLVMValue::create_function(backend.llmod, ll_direct_function_ty, concat!("fn_direct_", stringify!($name)));
				let ll_struct_function = LLVMValue::create_function(backend.llmod, ll_struct_function_ty, concat!("fn_struct_", stringify!($name)));

				direct_function_abi.apply_attributes(backend.llctx, ll_direct_function);
				struct_function_abi.apply_attributes(backend.llctx, ll_struct_function);

				let ll_mod = llvm_from_c(build_c_abi_str!($name ($( $field_name : $field_ty ),*)));

				let truth_ll_direct_function = LLVMValue::get_function(ll_mod, concat!("fn_direct_", stringify!($name)));
				let truth_ll_struct_function = LLVMValue::get_function(ll_mod, concat!("fn_struct_", stringify!($name)));

				println!("got: {:#?}\nexpected: {:#?}", ll_direct_function, truth_ll_direct_function);
				println!();
				println!("got: {:#?}\nexpected: {:#?}", ll_struct_function, truth_ll_struct_function);


				let truth_ll_direct_function_ty = LLVMType::of(truth_ll_direct_function);
				let truth_ll_struct_function_ty = LLVMType::of(truth_ll_struct_function);

				let truth_ctx = unsafe { LLVMGetModuleContext(ll_mod) };

				println!("got: {}\nexpected: {}", ll_direct_function_ty, truth_ll_direct_function_ty);
				println!();
				println!("got: {}\nexpected: {}", ll_struct_function_ty, truth_ll_struct_function_ty);

				assert!(llvm_ty_eq(truth_ctx, truth_ll_direct_function_ty, backend.llctx, ll_direct_function_ty));
				assert!(llvm_ty_eq(truth_ctx, truth_ll_struct_function_ty, backend.llctx, ll_struct_function_ty));
			} )*
		} };
	}

	impl fmt::Display for LLVMType {
		fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
			match self.kind() {
				LLVMVoidTypeKind => write!(f, "Void"),
				LLVMLabelTypeKind => write!(f, "Label"),
				LLVMMetadataTypeKind => write!(f, "Metadata"),
				LLVMHalfTypeKind => write!(f, "Half"),
				LLVMFloatTypeKind => write!(f, "Float"),
				LLVMDoubleTypeKind => write!(f, "Double"),
				LLVMTokenTypeKind => write!(f, "Token"),
				LLVMFP128TypeKind => write!(f, "FP128"),
				LLVMX86_FP80TypeKind => write!(f, "X86_FP80"),
				LLVMPPC_FP128TypeKind => write!(f, "PPC_FP128"),
				LLVMX86_MMXTypeKind => write!(f, "X86_MMX"),

				LLVMIntegerTypeKind
				=> {
					let s = self.get_int_type_width();
					write!(f, "i{}", s)
				}

				LLVMPointerTypeKind
				=> {
					let a = self.get_address_space();
					let e = self.get_element_type();
					write!(f, "*{} {}", a, e)
				}

				LLVMArrayTypeKind
				=> {
					let l = self.get_array_length();
					let e = self.get_element_type();
					write!(f, "[{}] {}", l, e)
				}

				LLVMVectorTypeKind
				=> {
					let l = self.get_vector_size();
					let a = self.get_element_type();
					write!(f, "<{}> {}", l, a)
				}

				LLVMStructTypeKind => {
					write!(f, "{{ ")?;

					let l = self.count_element_types();
					for i in 0..l {
						let e = self.get_type_at_index(i);
						write!(f, "{}", e)?;

						if i < l - 1 { write!(f, ", ")? }
					}

					write!(f, " }}")
				}

				LLVMFunctionTypeKind => {
					let r = self.get_return_type();
					write!(f, "{} (", r)?;

					let p = self.get_param_types();
					let mut i = p.iter().peekable();
					while let Some(p) = i.next() {
						write!(f, "{}", p)?;

						if i.peek().is_some() { write!(f, ", ")? }
					}

					write!(f, ")")
				}
			}
		}
	}

	fn llvm_ty_eq (a_ctx: LLVMContextRef, a: LLVMType, b_ctx: LLVMContextRef, b: LLVMType) -> bool {
		let compare_fn_ty =
			|a_ctx, a: LLVMType, b_ctx, b: LLVMType| {
				let a_len = a.count_param_types();
				let b_len = b.count_param_types();
				if a_len != b_len { return false }

				let ret_a = a.get_return_type();
				let ret_b = b.get_return_type();

				if !llvm_ty_eq(a_ctx, ret_a, b_ctx, ret_b) { return false }

				let a_param_types = a.get_param_types();
				let b_param_types = b.get_param_types();
				for (&a, &b) in a_param_types.iter().zip(b_param_types.iter()) {
					if !llvm_ty_eq(a_ctx, a, b_ctx, b) { return false }
				}

				true
			};

		match (a.kind(), b.kind()) {
			| (LLVMVoidTypeKind, LLVMVoidTypeKind)
			| (LLVMLabelTypeKind, LLVMLabelTypeKind)
			| (LLVMMetadataTypeKind, LLVMMetadataTypeKind)
			| (LLVMHalfTypeKind, LLVMHalfTypeKind)
			| (LLVMFloatTypeKind, LLVMFloatTypeKind)
			| (LLVMDoubleTypeKind, LLVMDoubleTypeKind)
			| (LLVMTokenTypeKind, LLVMTokenTypeKind)
			| (LLVMFP128TypeKind, LLVMFP128TypeKind)
			| (LLVMX86_FP80TypeKind, LLVMX86_FP80TypeKind)
			| (LLVMPPC_FP128TypeKind, LLVMPPC_FP128TypeKind)
			| (LLVMX86_MMXTypeKind, LLVMX86_MMXTypeKind)
			=> { true }

			(LLVMIntegerTypeKind, LLVMIntegerTypeKind)
			=> {
				let a = a.get_int_type_width();
				let b = b.get_int_type_width();
				a == b
			}

			(LLVMPointerTypeKind, LLVMPointerTypeKind)
			=> {
				let ae = a.get_element_type();
				let be = b.get_element_type();
				if !llvm_ty_eq(a_ctx, ae, b_ctx, be) { return false }

				let aa = a.get_address_space();
				let ba = b.get_address_space();
				aa == ba
			}

			(LLVMArrayTypeKind, LLVMArrayTypeKind)
			=> {
				let a_len = a.get_array_length();
				let b_len = b.get_array_length();
				if a_len != b_len { return false }

				let a = a.get_element_type();
				let b = b.get_element_type();
				llvm_ty_eq(a_ctx, a, b_ctx, b)
			}

			(LLVMVectorTypeKind, LLVMVectorTypeKind)
			=> {
				let a_len = a.get_vector_size();
				let b_len = b.get_vector_size();
				if a_len != b_len { return false }

				let a = a.get_element_type();
				let b = b.get_element_type();
				llvm_ty_eq(a_ctx, a, b_ctx, b)
			}

			(LLVMStructTypeKind, LLVMStructTypeKind) => {
				let a_len = a.count_element_types();
				let b_len = a.count_element_types();
				if a_len != b_len { return false }

				for i in 0..a_len {
					let a = a.get_type_at_index(i);
					let b = b.get_type_at_index(i);

					if !llvm_ty_eq(a_ctx, a, b_ctx, b) { return false }
				}

				true
			}

			(LLVMPointerTypeKind, LLVMFunctionTypeKind) => {
				let a = a.get_element_type();
				if a.is_function_kind() {
					compare_fn_ty(a_ctx, a, b_ctx, b)
				} else {
					false
				}
			}


			(LLVMFunctionTypeKind, LLVMPointerTypeKind) => {
				let b = b.get_element_type();
				if b.is_function_kind() {
					compare_fn_ty(a_ctx, a, b_ctx, b)
				} else {
					false
				}
			}

			(LLVMFunctionTypeKind, LLVMFunctionTypeKind) => {
				compare_fn_ty(a_ctx, a, b_ctx, b)
			}

			_ => { false }
		}
	}


	fn llvm_from_c (c_code: &str) -> LLVMModuleRef {
		// echo "int main () { return 1; }" | clang -xc -c -emit-llvm -o- - | llvm-dis
		use std::process::{ Command, Stdio };
		use std::io::Write;
		use std::mem::MaybeUninit;
		let mut clang =
			Command::new("clang")
				.arg("-xc")
				.arg("-c")
				.arg("-emit-llvm")
				.arg("-o-")
				.arg("-")
				.stdin(Stdio::piped())
				.stdout(Stdio::piped())
				.spawn()
				.unwrap();

		clang.stdin.as_mut().unwrap().write_all(c_code.as_bytes()).unwrap();

		let clang_output = clang.wait_with_output().unwrap().stdout;

		unsafe {
			let context = LLVMContextCreate();
			let mut module = MaybeUninit::uninit();

			let buff = LLVMCreateMemoryBufferWithMemoryRange(clang_output.as_ptr() as *const _, clang_output.len() as _, llvm_str!("harness bitcode"), LLVMFalse);
			assert!(LLVMParseBitcodeInContext2(context, buff, module.as_mut_ptr()) == LLVMOk, "Cannot load bitcode harness module");
			LLVMDisposeMemoryBuffer(buff);

			module.assume_init()
		}
	}

	#[test]
	fn build_abi_tests () {
		build_abi_tests! {
			i32_2(x: sint32_ty, y: sint32_ty)
			i64_2(x: sint64_ty, y: sint64_ty)
			i32_4(x: sint32_ty, y: sint32_ty, z: sint32_ty, w: sint32_ty)
			i64_4(x: sint64_ty, y: sint64_ty, z: sint64_ty, w: sint64_ty)
			i32_i16(x: sint32_ty, y: sint16_ty)
			i16_i32(x: sint16_ty, y: sint32_ty)
			i16_4(x: sint16_ty, y: sint16_ty, z: sint16_ty, w: sint16_ty)
			i16_8(x0: sint16_ty, y0: sint16_ty, z0: sint16_ty, w0: sint16_ty, x1: sint16_ty, y1: sint16_ty, z1: sint16_ty, w1: sint16_ty)
			f32_2(x: real32_ty, y: real32_ty)
			f32_4(x: real32_ty, y: real32_ty, z: real32_ty, w: real32_ty)
			f64_2(x: real64_ty, y: real64_ty)
			f64_4(x: real64_ty, y: real64_ty, z: real32_ty, w: real32_ty)
		}
	}
}