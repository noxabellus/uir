use std::fmt;

use llvm_sys::analysis::{LLVMVerifierFailureAction, LLVMVerifyFunction};
pub use llvm_sys::{LLVMTypeKind, LLVMTypeKind::*, LLVMValueKind, LLVMValueKind::*, core::*, prelude::*};
pub use llvm_sys::{LLVMIntPredicate, LLVMIntPredicate::*,};
pub use llvm_sys::{LLVMRealPredicate, LLVMRealPredicate::*,};
use uir_core::ty::PrimitiveTy;

pub const LLVM_OK: LLVMBool = 0;
pub const LLVM_FALSE: LLVMBool = 0;
pub const LLVM_TRUE: LLVMBool = 1;


unsafe fn strlen (p: *const i8) -> usize {
	let mut len = 0;
	while *p.add(len) != 0 { len += 1; }
	len
}

pub struct LLVMString {
	bytes: Vec<u8>,
}

impl Default for LLVMString {
	fn default () -> Self { Self::from("") }
}

impl From<String> for LLVMString {
	fn from(s: String) -> LLVMString {
		let mut bytes = s.into_bytes();

		for &byte in bytes.iter() {
			assert_ne!(byte, 0);
		}

		bytes.push(0);

		Self { bytes }
	}
}

impl From<*const i8> for LLVMString {
	#[allow(clippy::not_unsafe_ptr_arg_deref)]
	fn from(s: *const i8) -> LLVMString {
		unsafe {
			let len = strlen(s);
			let bytes = std::slice::from_raw_parts(s as _, len);

			std::str::from_utf8_unchecked(bytes).into()
		}
	}
}

impl From<&str> for LLVMString {
	fn from(s: &str) -> LLVMString {
		Self::from(s.to_owned())
	}
}

impl From<&String> for LLVMString {
	fn from(s: &String) -> LLVMString {
		Self::from(s.to_owned())
	}
}

impl LLVMString {
	pub fn into_bytes(self) -> Vec<u8> {
		self.bytes
	}

	pub fn as_ptr(&self) -> *const i8 {
		self.bytes.as_ptr() as *const i8
	}
}


#[repr(transparent)]
pub struct LLVMStr(str);

impl LLVMStr {
	#[allow(clippy::should_implement_trait)]
	pub fn from_str (s: &str) -> &Self { s.into() }
	pub fn as_str (&self) -> &str { self.into() }

	pub fn from_ptr<'a> (p: *const i8) -> &'a Self { p.into() }
	pub fn as_ptr (&self) -> *const i8 { self.into() }
}

impl<'a> From<*const i8> for &'a LLVMStr {
	fn from (x: *const i8) -> &'a LLVMStr {
		unsafe {
			let strlen = |p: *const i8| -> usize { let mut len = 0; while *p.add(len) != 0 { len += 1; } len };

			let slice = std::slice::from_raw_parts(x as _, strlen(x));
			let str = std::str::from_utf8(slice).unwrap();

			&*(str as *const _ as *const _)
		}
	}
}


impl<'a> From<&'a [i8]> for &'a LLVMStr {
	fn from (x: &'a [i8]) -> &'a LLVMStr {
		unsafe { &*(x as *const _ as *const [u8]) }.into()
	}
}

impl<'a> From<&'a [u8]> for &'a LLVMStr {
	fn from (x: &'a [u8]) -> &'a LLVMStr {
		unsafe {
			std::ffi::CStr::from_bytes_with_nul(x).unwrap();

			&*(x as *const _ as *const _)
		}
	}
}

impl<'a> From<&'a LLVMString> for &'a LLVMStr {
	fn from (x: &'a LLVMString) -> &'a LLVMStr {
		x.bytes.as_slice().into()
	}
}

impl<'a> From<&'a str> for &'a LLVMStr {
	fn from (x: &'a str) -> &'a LLVMStr {
		x.as_bytes().into()
	}
}



impl<'a> From<&'a LLVMStr> for &'a str {
	fn from (x: &'a LLVMStr) -> &'a str {
		unsafe { &*(x as *const _ as *const _) }
	}
}

impl<'a> From<&'a LLVMStr> for &'a [i8] {
	fn from (x: &'a LLVMStr) -> &'a [i8] {
		unsafe { &*(x as *const _ as *const _) }
	}
}

impl<'a> From<&'a LLVMStr> for &'a [u8] {
	fn from (x: &'a LLVMStr) -> &'a [u8] {
		unsafe { &*(x as *const _ as *const _) }
	}
}



impl<'a> From<&'a LLVMStr> for *const i8 {
	fn from (x: &'a LLVMStr) -> *const i8 {
		unsafe { &*(x as *const _ as *const _) }
	}
}

impl<'a> From<&'a LLVMStr> for *const u8 {
	fn from (x: &'a LLVMStr) -> *const u8 {
		unsafe { &*(x as *const _ as *const _) }
	}
}


pub trait ToLLVMText {
	fn to_lltext (&self) -> *const i8;
}

impl<'a> ToLLVMText for LLVMString {
	fn to_lltext (&self) -> *const i8 {
		self.as_ptr()
	}
}

impl<'a> ToLLVMText for LLVMStr {
	fn to_lltext (&self) -> *const i8 {
		self.as_ptr()
	}
}

impl<'a> ToLLVMText for str {
	fn to_lltext (&self) -> *const i8 {
		<&LLVMStr>::from(self).to_lltext()
	}
}

impl<'a> ToLLVMText for [u8] {
	fn to_lltext (&self) -> *const i8 {
		<&LLVMStr>::from(self).to_lltext()
	}
}

impl<'a> ToLLVMText for [i8] {
	fn to_lltext (&self) -> *const i8 {
		<&LLVMStr>::from(self).to_lltext()
	}
}


impl<'a> ToLLVMText for &LLVMString {
	fn to_lltext (&self) -> *const i8 {
		self.as_ptr()
	}
}

impl<'a> ToLLVMText for &'a LLVMStr {
	fn to_lltext (&self) -> *const i8 {
		(*self).to_lltext()
	}
}

impl<'a> ToLLVMText for &'a str {
	fn to_lltext (&self) -> *const i8 {
		(*self).to_lltext()
	}
}

impl<'a> ToLLVMText for &'a [u8] {
	fn to_lltext (&self) -> *const i8 {
		(*self).to_lltext()
	}
}

impl<'a> ToLLVMText for &'a [i8] {
	fn to_lltext (&self) -> *const i8 {
		(*self).to_lltext()
	}
}



pub struct Unnamed;
impl Unnamed {
	fn to_lltext (&self) -> *const i8 {
		b"\0" as *const _ as *const _
	}
}



macro_rules! llvm_str {
	($str:expr) => {{
		$crate::wrapper::LLVMStr::from_str(concat!($str, "\0"))
	}};
}

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LLVMType(LLVMTypeRef);
impl Default for LLVMType { fn default () -> Self { Self(std::ptr::null_mut()) } }

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LLVMValue(LLVMValueRef);
impl Default for LLVMValue { fn default () -> Self { Self(std::ptr::null_mut()) } }


#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LLVMBlock(LLVMBasicBlockRef);
impl Default for LLVMBlock { fn default () -> Self { Self(std::ptr::null_mut()) } }

impl From<LLVMTypeRef> for LLVMType {
	fn from(r: LLVMTypeRef) -> LLVMType {
		Self(r)
	}
}
impl From<LLVMType> for LLVMTypeRef {
	fn from(r: LLVMType) -> LLVMTypeRef {
		r.0
	}
}

impl From<LLVMValueRef> for LLVMValue {
	fn from(r: LLVMValueRef) -> LLVMValue {
		Self(r)
	}
}
impl From<LLVMValue> for LLVMValueRef {
	fn from(r: LLVMValue) -> LLVMValueRef {
		r.0
	}
}

impl From<LLVMBasicBlockRef> for LLVMBlock {
	fn from(r: LLVMBasicBlockRef) -> LLVMBlock {
		Self(r)
	}
}
impl From<LLVMBlock> for LLVMBasicBlockRef {
	fn from(r: LLVMBlock) -> LLVMBasicBlockRef {
		r.0
	}
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

impl fmt::Debug for LLVMType {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let alloc = unsafe { LLVMPrintTypeToString(self.0) };
		let s = unsafe { std::ffi::CStr::from_ptr(alloc).to_str().unwrap_or("[Err printing llvm type to string]") };

		write!(f, "{}", s.trim())?;

		unsafe { LLVMDisposeMessage(alloc) }

		Ok(())
	}
}

impl fmt::Debug for LLVMValue {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let alloc = unsafe { LLVMPrintValueToString(self.0) };
		let s = unsafe { std::ffi::CStr::from_ptr(alloc).to_str().unwrap_or("[Err printing llvm value to string]") };

		write!(f, "{}", s.trim())?;

		unsafe { LLVMDisposeMessage(alloc) }

		Ok(())
	}
}


impl LLVMBlock {
	pub fn as_value (self) -> LLVMValue {
		unsafe { LLVMBasicBlockAsValue(self.into()).into() }
	}
}

impl LLVMType {
	pub fn get_context (self) -> LLVMContextRef {
		unsafe { LLVMGetTypeContext(self.into()) }
	}

	pub fn equivalent (self, other: LLVMType) -> bool {
		let (a, b) = (self, other);

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
				if !ae.equivalent(be) { return false }

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
				a.equivalent(b)
			}

			(LLVMVectorTypeKind, LLVMVectorTypeKind)
			=> {
				let a_len = a.get_vector_size();
				let b_len = b.get_vector_size();
				if a_len != b_len { return false }

				let a = a.get_element_type();
				let b = b.get_element_type();
				a.equivalent(b)
			}

			(LLVMStructTypeKind, LLVMStructTypeKind) => {
				let a_len = a.count_element_types();
				let b_len = a.count_element_types();
				if a_len != b_len { return false }

				for i in 0..a_len {
					let a = a.get_type_at_index(i);
					let b = b.get_type_at_index(i);

					if !a.equivalent(b) { return false }
				}

				true
			}

			(LLVMPointerTypeKind, LLVMFunctionTypeKind) => {
				let a = a.get_element_type();
				if a.is_function_kind() {
					a.equivalent(b)
				} else {
					false
				}
			}


			(LLVMFunctionTypeKind, LLVMPointerTypeKind) => {
				let b = b.get_element_type();
				if b.is_function_kind() {
					a.equivalent(b)
				} else {
					false
				}
			}

			(LLVMFunctionTypeKind, LLVMFunctionTypeKind) => {
				let a_len = a.count_param_types();
				let b_len = b.count_param_types();
				if a_len != b_len { return false }

				let ret_a = a.get_return_type();
				let ret_b = b.get_return_type();

				if !ret_a.equivalent(ret_b) { return false }

				let a_param_types = a.get_param_types();
				let b_param_types = b.get_param_types();
				for (&a, &b) in a_param_types.iter().zip(b_param_types.iter()) {
					if !a.equivalent(b) { return false }
				}

				true
			}

			_ => { false }
		}
	}

	pub fn of (value: LLVMValue) -> LLVMType {
		unsafe { LLVMTypeOf(value.into()).into() }
	}

	pub fn is_register (self) -> bool {
		matches!(self.kind(),
				LLVMIntegerTypeKind // TODO: does this need to check for integers of size > word size? if so, it should be in ABI
			| LLVMFloatTypeKind
			| LLVMDoubleTypeKind
			| LLVMPointerTypeKind
		)
	}

	pub fn kind (self) -> LLVMTypeKind {
		unsafe { LLVMGetTypeKind(self.into()) }
	}

	pub fn is_kind (self, kind: LLVMTypeKind) -> bool {
		self.kind() == kind
	}

	pub fn is_void_kind (self) -> bool { self.is_kind(LLVMVoidTypeKind) }
	pub fn is_half_kind (self) -> bool { self.is_kind(LLVMHalfTypeKind) }
	pub fn is_float_kind (self) -> bool { self.is_kind(LLVMFloatTypeKind) }
	pub fn is_double_kind (self) -> bool { self.is_kind(LLVMDoubleTypeKind) }
	pub fn is_x86_fp80_kind (self) -> bool { self.is_kind(LLVMX86_FP80TypeKind) }
	pub fn is_fp128_kind (self) -> bool { self.is_kind(LLVMFP128TypeKind) }
	pub fn is_ppc_fp128_kind (self) -> bool { self.is_kind(LLVMPPC_FP128TypeKind) }
	pub fn is_label_kind (self) -> bool { self.is_kind(LLVMLabelTypeKind) }
	pub fn is_integer_kind (self) -> bool { self.is_kind(LLVMIntegerTypeKind) }
	pub fn is_function_kind (self) -> bool { self.is_kind(LLVMFunctionTypeKind) }
	pub fn is_struct_kind (self) -> bool { self.is_kind(LLVMStructTypeKind) }
	pub fn is_array_kind (self) -> bool { self.is_kind(LLVMArrayTypeKind) }
	pub fn is_pointer_kind (self) -> bool { self.is_kind(LLVMPointerTypeKind) }
	pub fn is_vector_kind (self) -> bool { self.is_kind(LLVMVectorTypeKind) }
	pub fn is_metadata_kind (self) -> bool { self.is_kind(LLVMMetadataTypeKind) }
	pub fn is_x86_mmx_kind (self) -> bool { self.is_kind(LLVMX86_MMXTypeKind) }
	pub fn is_token_kind (self) -> bool { self.is_kind(LLVMTokenTypeKind) }


	pub fn get_address_space (self) -> u32 {
		assert_eq!(self.kind(), LLVMPointerTypeKind);

		unsafe { LLVMGetPointerAddressSpace(self.into()) }
	}


	pub fn count_param_types (self) -> u32 {
		assert_eq!(self.kind(), LLVMFunctionTypeKind);

		unsafe { LLVMCountParamTypes(self.into()) }
	}

	pub fn get_param_types (self) -> Vec<LLVMType> {
		let len = self.count_param_types();

		let mut types = Vec::with_capacity(len as usize);
		unsafe {
			LLVMGetParamTypes(self.into(), types.as_mut_ptr());
			types.set_len(len as usize);
		}

		types.into_iter().map(LLVMType).collect()
	}

	pub fn get_return_type (self) -> LLVMType {
		unsafe { LLVMGetReturnType(self.into()).into() }
	}


	pub fn get_int_type_width (self) -> u32 {
		assert_eq!(self.kind(), LLVMIntegerTypeKind);

		unsafe { LLVMGetIntTypeWidth(self.into()) }
	}


	pub fn get_int_type_width_bytes (self) -> u32 {
		(self.get_int_type_width() + 7) / 8
	}


	pub fn count_element_types (self) -> u32 {
		assert_eq!(self.kind(), LLVMStructTypeKind);

		unsafe { LLVMCountStructElementTypes(self.0) }
	}


	pub fn get_array_length (self) -> u32 {
		assert_eq!(self.kind(), LLVMArrayTypeKind);

		unsafe { LLVMGetArrayLength(self.0) }
	}


	pub fn get_vector_size (self) -> u32 {
		assert_eq!(self.kind(), LLVMVectorTypeKind);

		unsafe { LLVMGetVectorSize(self.0) }
	}

	pub fn get_type_at_index (self, index: u32) -> LLVMType {
		unsafe { LLVMStructGetTypeAtIndex(self.0, index).into() }
	}

	pub fn is_packed_struct (self) -> bool {
		if self.kind() == LLVMStructTypeKind {
			unsafe { LLVMIsPackedStruct(self.into()) != LLVM_FALSE }
		} else {
			false
		}
	}


	pub fn get_element_type (self) -> LLVMType {
		assert!(matches!(self.kind(), LLVMArrayTypeKind | LLVMVectorTypeKind | LLVMPointerTypeKind));

		unsafe { LLVMGetElementType(self.0).into() }
	}

	pub fn as_pointer (self, address_space: u32) -> LLVMType {
		Self::pointer(self, address_space)
	}

	pub fn as_array (self, length: u32) -> LLVMType {
		Self::array(self, length)
	}

	pub fn primitive(ctx: LLVMContextRef, prim: PrimitiveTy) -> LLVMType {
		match prim {
			PrimitiveTy::Bool => Self::int1(ctx),

			PrimitiveTy::UInt8   | PrimitiveTy::SInt8   => Self::int8(ctx),
			PrimitiveTy::UInt16  | PrimitiveTy::SInt16  => Self::int16(ctx),
			PrimitiveTy::UInt32  | PrimitiveTy::SInt32  => Self::int32(ctx),
			PrimitiveTy::UInt64  | PrimitiveTy::SInt64  => Self::int64(ctx),
			PrimitiveTy::UInt128 | PrimitiveTy::SInt128 => Self::int128(ctx),

			PrimitiveTy::Real32 => Self::float(ctx),
			PrimitiveTy::Real64 => Self::double(ctx),
		}
	}

	pub fn int (ctx: LLVMContextRef, bits: u32) -> LLVMType {
		unsafe { LLVMIntTypeInContext(ctx, bits).into() }
	}

	pub fn int1 (ctx: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt1TypeInContext(ctx).into() }
	}

	pub fn int8 (ctx: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt8TypeInContext(ctx).into() }
	}

	pub fn int16 (ctx: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt16TypeInContext(ctx).into() }
	}

	pub fn int32 (ctx: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt32TypeInContext(ctx).into() }
	}

	pub fn int64 (ctx: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt64TypeInContext(ctx).into() }
	}

	pub fn int128 (ctx: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt128TypeInContext(ctx).into() }
	}

	pub fn float (ctx: LLVMContextRef) -> LLVMType {
		unsafe { LLVMFloatTypeInContext(ctx).into() }
	}

	pub fn double (ctx: LLVMContextRef) -> LLVMType {
		unsafe { LLVMDoubleTypeInContext(ctx).into() }
	}

	pub fn void (ctx: LLVMContextRef) -> LLVMType {
		unsafe { LLVMVoidTypeInContext(ctx).into() }
	}

	pub fn label (ctx: LLVMContextRef) -> LLVMType {
		unsafe { LLVMLabelTypeInContext(ctx).into() }
	}

	pub fn pointer (target_ty: LLVMType, address_space: u32) -> LLVMType {
		unsafe { LLVMPointerType(target_ty.into(), address_space).into() }
	}

	pub fn function (param_tys: &[LLVMType], ret_ty: LLVMType, is_var_args: bool) -> LLVMType {
		unsafe { LLVMFunctionType(ret_ty.into(), param_tys.as_ptr() as *const _ as *mut _, param_tys.len() as _, is_var_args as _).into() }
	}

	pub fn array (element_ty: LLVMType, length: u32) -> LLVMType {
		unsafe { LLVMArrayType(element_ty.into(), length).into() }
	}

	pub fn vector (element_ty: LLVMType, length: u32) -> LLVMType {
		unsafe { LLVMVectorType(element_ty.into(), length).into() }
	}

	pub fn named_empty_structure<T: ToLLVMText> (ctx: LLVMContextRef, name: T) -> LLVMType {
		unsafe { LLVMStructCreateNamed(ctx, name.to_lltext()).into() }
	}

	pub fn anonymous_empty_structure (ctx: LLVMContextRef) -> LLVMType {
		unsafe { LLVMStructTypeInContext(ctx, std::ptr::null_mut(), 0, LLVM_FALSE).into() }
	}

	pub fn structure_set_body (self, field_tys: &[LLVMType], packed: bool) {
		unsafe { LLVMStructSetBody(self.into(), field_tys.as_ptr() as *mut _, field_tys.len() as _, packed as _) }
	}

	pub fn named_structure<T: ToLLVMText> (ctx: LLVMContextRef, name: T, field_tys: &[LLVMType], packed: bool) -> LLVMType {
		let llt = LLVMType::named_empty_structure(ctx, name);
		llt.structure_set_body(field_tys, packed);
		llt
	}

	pub fn anonymous_structure (ctx: LLVMContextRef, field_tys: &[LLVMType], packed: bool) -> LLVMType {
		unsafe { LLVMStructTypeInContext(ctx, field_tys.as_ptr() as *const _ as *mut _, field_tys.len() as _, packed as _).into() }
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LLVMNodeKind {
	LLVMArgumentNodeKind,
	LLVMBasicBlockNodeKind,
	LLVMInlineAsmNodeKind,
	LLVMUserNodeKind,
	LLVMConstantNodeKind,
	LLVMBlockAddressNodeKind,
	LLVMConstantAggregateZeroNodeKind,
	LLVMConstantArrayNodeKind,
	LLVMConstantDataSequentialNodeKind,
	LLVMConstantDataArrayNodeKind,
	LLVMConstantDataVectorNodeKind,
	LLVMConstantExprNodeKind,
	LLVMConstantFPNodeKind,
	LLVMConstantIntNodeKind,
	LLVMConstantPointerNullNodeKind,
	LLVMConstantStructNodeKind,
	LLVMConstantTokenNoneNodeKind,
	LLVMConstantVectorNodeKind,
	LLVMGlobalValueNodeKind,
	LLVMGlobalAliasNodeKind,
	LLVMGlobalIFuncNodeKind,
	LLVMGlobalObjectNodeKind,
	LLVMFunctionNodeKind,
	LLVMGlobalVariableNodeKind,
	LLVMUndefValueNodeKind,
	LLVMInstructionNodeKind,
	LLVMUnaryOperatorNodeKind,
	LLVMBinaryOperatorNodeKind,
	LLVMCallInstNodeKind,
	LLVMIntrinsicInstNodeKind,
	LLVMDbgInfoIntrinsicNodeKind,
	LLVMDbgVariableIntrinsicNodeKind,
	LLVMDbgDeclareInstNodeKind,
	LLVMDbgLabelInstNodeKind,
	LLVMMemIntrinsicNodeKind,
	LLVMMemCpyInstNodeKind,
	LLVMMemMoveInstNodeKind,
	LLVMMemSetInstNodeKind,
	LLVMCmpInstNodeKind,
	LLVMFCmpInstNodeKind,
	LLVMICmpInstNodeKind,
	LLVMExtractElementInstNodeKind,
	LLVMGetElementPtrInstNodeKind,
	LLVMInsertElementInstNodeKind,
	LLVMInsertValueInstNodeKind,
	LLVMLandingPadInstNodeKind,
	LLVMPHINodeNodeKind,
	LLVMSelectInstNodeKind,
	LLVMShuffleVectorInstNodeKind,
	LLVMStoreInstNodeKind,
	LLVMBranchInstNodeKind,
	LLVMIndirectBrInstNodeKind,
	LLVMInvokeInstNodeKind,
	LLVMReturnInstNodeKind,
	LLVMSwitchInstNodeKind,
	LLVMUnreachableInstNodeKind,
	LLVMResumeInstNodeKind,
	LLVMCleanupReturnInstNodeKind,
	LLVMCatchReturnInstNodeKind,
	LLVMCatchSwitchInstNodeKind,
	LLVMCallBrInstNodeKind,
	LLVMFuncletPadInstNodeKind,
	LLVMCatchPadInstNodeKind,
	LLVMCleanupPadInstNodeKind,
	LLVMUnaryInstructionNodeKind,
	LLVMAllocaInstNodeKind,
	LLVMCastInstNodeKind,
	LLVMAddrSpaceCastInstNodeKind,
	LLVMBitCastInstNodeKind,
	LLVMFPExtInstNodeKind,
	LLVMFPToSIInstNodeKind,
	LLVMFPToUIInstNodeKind,
	LLVMFPTruncInstNodeKind,
	LLVMIntToPtrInstNodeKind,
	LLVMPtrToIntInstNodeKind,
	LLVMSExtInstNodeKind,
	LLVMSIToFPInstNodeKind,
	LLVMTruncInstNodeKind,
	LLVMUIToFPInstNodeKind,
	LLVMZExtInstNodeKind,
	LLVMExtractValueInstNodeKind,
	LLVMLoadInstNodeKind,
	LLVMVAArgInstNodeKind,
	LLVMFreezeInstNodeKind,
	LLVMAtomicCmpXchgInstNodeKind,
	LLVMAtomicRMWInstNodeKind,
	LLVMFenceInstNodeKind,
}

impl LLVMNodeKind {
	pub fn test_node (self, value: LLVMValue) -> bool {
		LLVMValue(unsafe { (match self {
			LLVMArgumentNodeKind => LLVMIsAArgument,
			LLVMBasicBlockNodeKind => LLVMIsABasicBlock,
			LLVMInlineAsmNodeKind => LLVMIsAInlineAsm,
			LLVMUserNodeKind => LLVMIsAUser,
			LLVMConstantNodeKind => LLVMIsAConstant,
			LLVMBlockAddressNodeKind => LLVMIsABlockAddress,
			LLVMConstantAggregateZeroNodeKind => LLVMIsAConstantAggregateZero,
			LLVMConstantArrayNodeKind => LLVMIsAConstantArray,
			LLVMConstantDataSequentialNodeKind => LLVMIsAConstantDataSequential,
			LLVMConstantDataArrayNodeKind => LLVMIsAConstantDataArray,
			LLVMConstantDataVectorNodeKind => LLVMIsAConstantDataVector,
			LLVMConstantExprNodeKind => LLVMIsAConstantExpr,
			LLVMConstantFPNodeKind => LLVMIsAConstantFP,
			LLVMConstantIntNodeKind => LLVMIsAConstantInt,
			LLVMConstantPointerNullNodeKind => LLVMIsAConstantPointerNull,
			LLVMConstantStructNodeKind => LLVMIsAConstantStruct,
			LLVMConstantTokenNoneNodeKind => LLVMIsAConstantTokenNone,
			LLVMConstantVectorNodeKind => LLVMIsAConstantVector,
			LLVMGlobalValueNodeKind => LLVMIsAGlobalValue,
			LLVMGlobalAliasNodeKind => LLVMIsAGlobalAlias,
			LLVMGlobalIFuncNodeKind => LLVMIsAGlobalIFunc,
			LLVMGlobalObjectNodeKind => LLVMIsAGlobalObject,
			LLVMFunctionNodeKind => LLVMIsAFunction,
			LLVMGlobalVariableNodeKind => LLVMIsAGlobalVariable,
			LLVMUndefValueNodeKind => LLVMIsAUndefValue,
			LLVMInstructionNodeKind => LLVMIsAInstruction,
			LLVMUnaryOperatorNodeKind => LLVMIsAUnaryOperator,
			LLVMBinaryOperatorNodeKind => LLVMIsABinaryOperator,
			LLVMCallInstNodeKind => LLVMIsACallInst,
			LLVMIntrinsicInstNodeKind => LLVMIsAIntrinsicInst,
			LLVMDbgInfoIntrinsicNodeKind => LLVMIsADbgInfoIntrinsic,
			LLVMDbgVariableIntrinsicNodeKind => LLVMIsADbgVariableIntrinsic,
			LLVMDbgDeclareInstNodeKind => LLVMIsADbgDeclareInst,
			LLVMDbgLabelInstNodeKind => LLVMIsADbgLabelInst,
			LLVMMemIntrinsicNodeKind => LLVMIsAMemIntrinsic,
			LLVMMemCpyInstNodeKind => LLVMIsAMemCpyInst,
			LLVMMemMoveInstNodeKind => LLVMIsAMemMoveInst,
			LLVMMemSetInstNodeKind => LLVMIsAMemSetInst,
			LLVMCmpInstNodeKind => LLVMIsACmpInst,
			LLVMFCmpInstNodeKind => LLVMIsAFCmpInst,
			LLVMICmpInstNodeKind => LLVMIsAICmpInst,
			LLVMExtractElementInstNodeKind => LLVMIsAExtractElementInst,
			LLVMGetElementPtrInstNodeKind => LLVMIsAGetElementPtrInst,
			LLVMInsertElementInstNodeKind => LLVMIsAInsertElementInst,
			LLVMInsertValueInstNodeKind => LLVMIsAInsertValueInst,
			LLVMLandingPadInstNodeKind => LLVMIsALandingPadInst,
			LLVMPHINodeNodeKind => LLVMIsAPHINode,
			LLVMSelectInstNodeKind => LLVMIsASelectInst,
			LLVMShuffleVectorInstNodeKind => LLVMIsAShuffleVectorInst,
			LLVMStoreInstNodeKind => LLVMIsAStoreInst,
			LLVMBranchInstNodeKind => LLVMIsABranchInst,
			LLVMIndirectBrInstNodeKind => LLVMIsAIndirectBrInst,
			LLVMInvokeInstNodeKind => LLVMIsAInvokeInst,
			LLVMReturnInstNodeKind => LLVMIsAReturnInst,
			LLVMSwitchInstNodeKind => LLVMIsASwitchInst,
			LLVMUnreachableInstNodeKind => LLVMIsAUnreachableInst,
			LLVMResumeInstNodeKind => LLVMIsAResumeInst,
			LLVMCleanupReturnInstNodeKind => LLVMIsACleanupReturnInst,
			LLVMCatchReturnInstNodeKind => LLVMIsACatchReturnInst,
			LLVMCatchSwitchInstNodeKind => LLVMIsACatchSwitchInst,
			LLVMCallBrInstNodeKind => LLVMIsACallBrInst,
			LLVMFuncletPadInstNodeKind => LLVMIsAFuncletPadInst,
			LLVMCatchPadInstNodeKind => LLVMIsACatchPadInst,
			LLVMCleanupPadInstNodeKind => LLVMIsACleanupPadInst,
			LLVMUnaryInstructionNodeKind => LLVMIsAUnaryInstruction,
			LLVMAllocaInstNodeKind => LLVMIsAAllocaInst,
			LLVMCastInstNodeKind => LLVMIsACastInst,
			LLVMAddrSpaceCastInstNodeKind => LLVMIsAAddrSpaceCastInst,
			LLVMBitCastInstNodeKind => LLVMIsABitCastInst,
			LLVMFPExtInstNodeKind => LLVMIsAFPExtInst,
			LLVMFPToSIInstNodeKind => LLVMIsAFPToSIInst,
			LLVMFPToUIInstNodeKind => LLVMIsAFPToUIInst,
			LLVMFPTruncInstNodeKind => LLVMIsAFPTruncInst,
			LLVMIntToPtrInstNodeKind => LLVMIsAIntToPtrInst,
			LLVMPtrToIntInstNodeKind => LLVMIsAPtrToIntInst,
			LLVMSExtInstNodeKind => LLVMIsASExtInst,
			LLVMSIToFPInstNodeKind => LLVMIsASIToFPInst,
			LLVMTruncInstNodeKind => LLVMIsATruncInst,
			LLVMUIToFPInstNodeKind => LLVMIsAUIToFPInst,
			LLVMZExtInstNodeKind => LLVMIsAZExtInst,
			LLVMExtractValueInstNodeKind => LLVMIsAExtractValueInst,
			LLVMLoadInstNodeKind => LLVMIsALoadInst,
			LLVMVAArgInstNodeKind => LLVMIsAVAArgInst,
			LLVMFreezeInstNodeKind => LLVMIsAFreezeInst,
			LLVMAtomicCmpXchgInstNodeKind => LLVMIsAAtomicCmpXchgInst,
			LLVMAtomicRMWInstNodeKind => LLVMIsAAtomicRMWInst,
			LLVMFenceInstNodeKind => LLVMIsAFenceInst,
		})(value.into()) }) != LLVMValue::default()
	}
}

pub use LLVMNodeKind::*;


impl LLVMValue {
	pub fn set_name (self, name: impl ToLLVMText) {
		let name = name.to_lltext();

		unsafe { LLVMSetValueName2(self.into(), name, strlen(name))}
	}

	pub fn verify_function (self, action: LLVMVerifierFailureAction) -> bool {
		unsafe { LLVMVerifyFunction(self.into(), action) == LLVM_OK }
	}

	pub fn undef (ty: LLVMType) -> LLVMValue {
		unsafe { LLVMGetUndef(ty.into()).into() }
	}

	pub fn zero (ty: LLVMType) -> LLVMValue {
		unsafe { LLVMConstNull(ty.into()).into() }
	}

	pub fn null_ptr (ty: LLVMType) -> LLVMValue {
		unsafe { LLVMConstPointerNull(ty.into()).into() }
	}

	pub fn int (ty: LLVMType, value: u128) -> LLVMValue {
		unsafe { LLVMConstIntOfArbitraryPrecision(ty.into(), 2, &value as *const _ as *const _).into() }
	}

	pub fn real (ty: LLVMType, value: f64) -> LLVMValue {
		unsafe { LLVMConstReal(ty.into(), value).into() }
	}


	pub fn const_insert_value (self, value: LLVMValue, index: u32) -> LLVMValue {
		unsafe { LLVMConstInsertValue(self.into(), value.into(), [index].as_ptr() as _, 1).into() }
	}

	pub fn const_fill_agg (mut self, value: LLVMValue, len: u32) -> LLVMValue {
		for i in 0..len {
			self = self.const_insert_value(value, i);
		}

		self
	}

	pub fn get_global_parent (self) -> LLVMModuleRef {
		assert!(self.is_global_variable_node() || self.is_function_node());
		unsafe { LLVMGetGlobalParent(self.into()) }
	}

	// pub fn const_structure (ty: LLVMType) -> LLVMValue {
	// 	unsafe { LLVMConstNamedStruct(ty.into(), ).into() }
	// }

	pub fn create_global<T: ToLLVMText> (module: impl Into<LLVMModuleRef>, ty: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMAddGlobal(module.into(), ty.into(), name.to_lltext()).into() }
	}

	pub fn create_function<T: ToLLVMText> (module: impl Into<LLVMModuleRef>, ty: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMAddFunction(module.into(), name.to_lltext(), ty.into()).into() }
	}

	pub fn get_function<T: ToLLVMText> (module: impl Into<LLVMModuleRef>, name: T) -> LLVMValue {
		unsafe { LLVMGetNamedFunction(module.into(), name.to_lltext()).into() }
	}

	pub fn set_global_initializer (self, const_init: LLVMValue) {
		unsafe { LLVMSetInitializer(self.into(), const_init.into()) }
	}

	pub fn kind (self) -> LLVMValueKind {
		unsafe { LLVMGetValueKind(self.into()) }
	}

	pub fn is_kind (self, kind: LLVMValueKind) -> bool {
		self.kind() == kind
	}

	pub fn is_argument_kind (self) -> bool { self.is_kind(LLVMArgumentValueKind) }
	pub fn is_basic_block_kind (self) -> bool { self.is_kind(LLVMBasicBlockValueKind) }
	pub fn is_memory_use_kind (self) -> bool { self.is_kind(LLVMMemoryUseValueKind) }
	pub fn is_memory_def_kind (self) -> bool { self.is_kind(LLVMMemoryDefValueKind) }
	pub fn is_memory_phi_kind (self) -> bool { self.is_kind(LLVMMemoryPhiValueKind) }

	pub fn is_function_kind (self) -> bool { self.is_kind(LLVMFunctionValueKind) }
	pub fn is_global_alias_kind (self) -> bool { self.is_kind(LLVMGlobalAliasValueKind) }
	pub fn is_global_ifunc_kind (self) -> bool { self.is_kind(LLVMGlobalIFuncValueKind) }
	pub fn is_global_variable_kind (self) -> bool { self.is_kind(LLVMGlobalVariableValueKind) }
	pub fn is_block_address_kind (self) -> bool { self.is_kind(LLVMBlockAddressValueKind) }
	pub fn is_constant_expr_kind (self) -> bool { self.is_kind(LLVMConstantExprValueKind) }
	pub fn is_constant_array_kind (self) -> bool { self.is_kind(LLVMConstantArrayValueKind) }
	pub fn is_constant_struct_kind (self) -> bool { self.is_kind(LLVMConstantStructValueKind) }
	pub fn is_constant_vector_kind (self) -> bool { self.is_kind(LLVMConstantVectorValueKind) }
	pub fn is_undef_value_kind (self) -> bool { self.is_kind(LLVMUndefValueValueKind) }
	pub fn is_constant_aggregate_zero_kind (self) -> bool { self.is_kind(LLVMConstantAggregateZeroValueKind) }
	pub fn is_constant_data_array_kind (self) -> bool { self.is_kind(LLVMConstantDataArrayValueKind) }
	pub fn is_constant_data_vector_kind (self) -> bool { self.is_kind(LLVMConstantDataVectorValueKind) }
	pub fn is_constant_int_kind (self) -> bool { self.is_kind(LLVMConstantIntValueKind) }
	pub fn is_constant_fp_kind (self) -> bool { self.is_kind(LLVMConstantFPValueKind) }
	pub fn is_constant_pointer_null_kind (self) -> bool { self.is_kind(LLVMConstantPointerNullValueKind) }
	pub fn is_constant_token_none_kind (self) -> bool { self.is_kind(LLVMConstantTokenNoneValueKind) }

	pub fn is_metadata_as_value_kind (self) -> bool { self.is_kind(LLVMMetadataAsValueValueKind) }
	pub fn is_inline_asm_kind (self) -> bool { self.is_kind(LLVMInlineAsmValueKind) }

	pub fn is_instruction_kind (self) -> bool { self.is_kind(LLVMInstructionValueKind) }

	pub fn node_kind (self) -> Option<LLVMNodeKind> {
		Some(unsafe { match self.into() {
			x if LLVMValue(LLVMIsAArgument(x)) != LLVMValue::default() => LLVMArgumentNodeKind,
			x if LLVMValue(LLVMIsABasicBlock(x)) != LLVMValue::default() => LLVMBasicBlockNodeKind,
			x if LLVMValue(LLVMIsAInlineAsm(x)) != LLVMValue::default() => LLVMInlineAsmNodeKind,
			x if LLVMValue(LLVMIsAUser(x)) != LLVMValue::default() => LLVMUserNodeKind,
			x if LLVMValue(LLVMIsAConstant(x)) != LLVMValue::default() => LLVMConstantNodeKind,
			x if LLVMValue(LLVMIsABlockAddress(x)) != LLVMValue::default() => LLVMBlockAddressNodeKind,
			x if LLVMValue(LLVMIsAConstantAggregateZero(x)) != LLVMValue::default() => LLVMConstantAggregateZeroNodeKind,
			x if LLVMValue(LLVMIsAConstantArray(x)) != LLVMValue::default() => LLVMConstantArrayNodeKind,
			x if LLVMValue(LLVMIsAConstantDataSequential(x)) != LLVMValue::default() => LLVMConstantDataSequentialNodeKind,
			x if LLVMValue(LLVMIsAConstantDataArray(x)) != LLVMValue::default() => LLVMConstantDataArrayNodeKind,
			x if LLVMValue(LLVMIsAConstantDataVector(x)) != LLVMValue::default() => LLVMConstantDataVectorNodeKind,
			x if LLVMValue(LLVMIsAConstantExpr(x)) != LLVMValue::default() => LLVMConstantExprNodeKind,
			x if LLVMValue(LLVMIsAConstantFP(x)) != LLVMValue::default() => LLVMConstantFPNodeKind,
			x if LLVMValue(LLVMIsAConstantInt(x)) != LLVMValue::default() => LLVMConstantIntNodeKind,
			x if LLVMValue(LLVMIsAConstantPointerNull(x)) != LLVMValue::default() => LLVMConstantPointerNullNodeKind,
			x if LLVMValue(LLVMIsAConstantStruct(x)) != LLVMValue::default() => LLVMConstantStructNodeKind,
			x if LLVMValue(LLVMIsAConstantTokenNone(x)) != LLVMValue::default() => LLVMConstantTokenNoneNodeKind,
			x if LLVMValue(LLVMIsAConstantVector(x)) != LLVMValue::default() => LLVMConstantVectorNodeKind,
			x if LLVMValue(LLVMIsAGlobalValue(x)) != LLVMValue::default() => LLVMGlobalValueNodeKind,
			x if LLVMValue(LLVMIsAGlobalAlias(x)) != LLVMValue::default() => LLVMGlobalAliasNodeKind,
			x if LLVMValue(LLVMIsAGlobalIFunc(x)) != LLVMValue::default() => LLVMGlobalIFuncNodeKind,
			x if LLVMValue(LLVMIsAGlobalObject(x)) != LLVMValue::default() => LLVMGlobalObjectNodeKind,
			x if LLVMValue(LLVMIsAFunction(x)) != LLVMValue::default() => LLVMFunctionNodeKind,
			x if LLVMValue(LLVMIsAGlobalVariable(x)) != LLVMValue::default() => LLVMGlobalVariableNodeKind,
			x if LLVMValue(LLVMIsAUndefValue(x)) != LLVMValue::default() => LLVMUndefValueNodeKind,
			x if LLVMValue(LLVMIsAInstruction(x)) != LLVMValue::default() => LLVMInstructionNodeKind,
			x if LLVMValue(LLVMIsAUnaryOperator(x)) != LLVMValue::default() => LLVMUnaryOperatorNodeKind,
			x if LLVMValue(LLVMIsABinaryOperator(x)) != LLVMValue::default() => LLVMBinaryOperatorNodeKind,
			x if LLVMValue(LLVMIsACallInst(x)) != LLVMValue::default() => LLVMCallInstNodeKind,
			x if LLVMValue(LLVMIsAIntrinsicInst(x)) != LLVMValue::default() => LLVMIntrinsicInstNodeKind,
			x if LLVMValue(LLVMIsADbgInfoIntrinsic(x)) != LLVMValue::default() => LLVMDbgInfoIntrinsicNodeKind,
			x if LLVMValue(LLVMIsADbgVariableIntrinsic(x)) != LLVMValue::default() => LLVMDbgVariableIntrinsicNodeKind,
			x if LLVMValue(LLVMIsADbgDeclareInst(x)) != LLVMValue::default() => LLVMDbgDeclareInstNodeKind,
			x if LLVMValue(LLVMIsADbgLabelInst(x)) != LLVMValue::default() => LLVMDbgLabelInstNodeKind,
			x if LLVMValue(LLVMIsAMemIntrinsic(x)) != LLVMValue::default() => LLVMMemIntrinsicNodeKind,
			x if LLVMValue(LLVMIsAMemCpyInst(x)) != LLVMValue::default() => LLVMMemCpyInstNodeKind,
			x if LLVMValue(LLVMIsAMemMoveInst(x)) != LLVMValue::default() => LLVMMemMoveInstNodeKind,
			x if LLVMValue(LLVMIsAMemSetInst(x)) != LLVMValue::default() => LLVMMemSetInstNodeKind,
			x if LLVMValue(LLVMIsACmpInst(x)) != LLVMValue::default() => LLVMCmpInstNodeKind,
			x if LLVMValue(LLVMIsAFCmpInst(x)) != LLVMValue::default() => LLVMFCmpInstNodeKind,
			x if LLVMValue(LLVMIsAICmpInst(x)) != LLVMValue::default() => LLVMICmpInstNodeKind,
			x if LLVMValue(LLVMIsAExtractElementInst(x)) != LLVMValue::default() => LLVMExtractElementInstNodeKind,
			x if LLVMValue(LLVMIsAGetElementPtrInst(x)) != LLVMValue::default() => LLVMGetElementPtrInstNodeKind,
			x if LLVMValue(LLVMIsAInsertElementInst(x)) != LLVMValue::default() => LLVMInsertElementInstNodeKind,
			x if LLVMValue(LLVMIsAInsertValueInst(x)) != LLVMValue::default() => LLVMInsertValueInstNodeKind,
			x if LLVMValue(LLVMIsALandingPadInst(x)) != LLVMValue::default() => LLVMLandingPadInstNodeKind,
			x if LLVMValue(LLVMIsAPHINode(x)) != LLVMValue::default() => LLVMPHINodeNodeKind,
			x if LLVMValue(LLVMIsASelectInst(x)) != LLVMValue::default() => LLVMSelectInstNodeKind,
			x if LLVMValue(LLVMIsAShuffleVectorInst(x)) != LLVMValue::default() => LLVMShuffleVectorInstNodeKind,
			x if LLVMValue(LLVMIsAStoreInst(x)) != LLVMValue::default() => LLVMStoreInstNodeKind,
			x if LLVMValue(LLVMIsABranchInst(x)) != LLVMValue::default() => LLVMBranchInstNodeKind,
			x if LLVMValue(LLVMIsAIndirectBrInst(x)) != LLVMValue::default() => LLVMIndirectBrInstNodeKind,
			x if LLVMValue(LLVMIsAInvokeInst(x)) != LLVMValue::default() => LLVMInvokeInstNodeKind,
			x if LLVMValue(LLVMIsAReturnInst(x)) != LLVMValue::default() => LLVMReturnInstNodeKind,
			x if LLVMValue(LLVMIsASwitchInst(x)) != LLVMValue::default() => LLVMSwitchInstNodeKind,
			x if LLVMValue(LLVMIsAUnreachableInst(x)) != LLVMValue::default() => LLVMUnreachableInstNodeKind,
			x if LLVMValue(LLVMIsAResumeInst(x)) != LLVMValue::default() => LLVMResumeInstNodeKind,
			x if LLVMValue(LLVMIsACleanupReturnInst(x)) != LLVMValue::default() => LLVMCleanupReturnInstNodeKind,
			x if LLVMValue(LLVMIsACatchReturnInst(x)) != LLVMValue::default() => LLVMCatchReturnInstNodeKind,
			x if LLVMValue(LLVMIsACatchSwitchInst(x)) != LLVMValue::default() => LLVMCatchSwitchInstNodeKind,
			x if LLVMValue(LLVMIsACallBrInst(x)) != LLVMValue::default() => LLVMCallBrInstNodeKind,
			x if LLVMValue(LLVMIsAFuncletPadInst(x)) != LLVMValue::default() => LLVMFuncletPadInstNodeKind,
			x if LLVMValue(LLVMIsACatchPadInst(x)) != LLVMValue::default() => LLVMCatchPadInstNodeKind,
			x if LLVMValue(LLVMIsACleanupPadInst(x)) != LLVMValue::default() => LLVMCleanupPadInstNodeKind,
			x if LLVMValue(LLVMIsAUnaryInstruction(x)) != LLVMValue::default() => LLVMUnaryInstructionNodeKind,
			x if LLVMValue(LLVMIsAAllocaInst(x)) != LLVMValue::default() => LLVMAllocaInstNodeKind,
			x if LLVMValue(LLVMIsACastInst(x)) != LLVMValue::default() => LLVMCastInstNodeKind,
			x if LLVMValue(LLVMIsAAddrSpaceCastInst(x)) != LLVMValue::default() => LLVMAddrSpaceCastInstNodeKind,
			x if LLVMValue(LLVMIsABitCastInst(x)) != LLVMValue::default() => LLVMBitCastInstNodeKind,
			x if LLVMValue(LLVMIsAFPExtInst(x)) != LLVMValue::default() => LLVMFPExtInstNodeKind,
			x if LLVMValue(LLVMIsAFPToSIInst(x)) != LLVMValue::default() => LLVMFPToSIInstNodeKind,
			x if LLVMValue(LLVMIsAFPToUIInst(x)) != LLVMValue::default() => LLVMFPToUIInstNodeKind,
			x if LLVMValue(LLVMIsAFPTruncInst(x)) != LLVMValue::default() => LLVMFPTruncInstNodeKind,
			x if LLVMValue(LLVMIsAIntToPtrInst(x)) != LLVMValue::default() => LLVMIntToPtrInstNodeKind,
			x if LLVMValue(LLVMIsAPtrToIntInst(x)) != LLVMValue::default() => LLVMPtrToIntInstNodeKind,
			x if LLVMValue(LLVMIsASExtInst(x)) != LLVMValue::default() => LLVMSExtInstNodeKind,
			x if LLVMValue(LLVMIsASIToFPInst(x)) != LLVMValue::default() => LLVMSIToFPInstNodeKind,
			x if LLVMValue(LLVMIsATruncInst(x)) != LLVMValue::default() => LLVMTruncInstNodeKind,
			x if LLVMValue(LLVMIsAUIToFPInst(x)) != LLVMValue::default() => LLVMUIToFPInstNodeKind,
			x if LLVMValue(LLVMIsAZExtInst(x)) != LLVMValue::default() => LLVMZExtInstNodeKind,
			x if LLVMValue(LLVMIsAExtractValueInst(x)) != LLVMValue::default() => LLVMExtractValueInstNodeKind,
			x if LLVMValue(LLVMIsALoadInst(x)) != LLVMValue::default() => LLVMLoadInstNodeKind,
			x if LLVMValue(LLVMIsAVAArgInst(x)) != LLVMValue::default() => LLVMVAArgInstNodeKind,
			x if LLVMValue(LLVMIsAFreezeInst(x)) != LLVMValue::default() => LLVMFreezeInstNodeKind,
			x if LLVMValue(LLVMIsAAtomicCmpXchgInst(x)) != LLVMValue::default() => LLVMAtomicCmpXchgInstNodeKind,
			x if LLVMValue(LLVMIsAAtomicRMWInst(x)) != LLVMValue::default() => LLVMAtomicRMWInstNodeKind,
			x if LLVMValue(LLVMIsAFenceInst(x)) != LLVMValue::default() => LLVMFenceInstNodeKind,
			_ => return None,
		} })
	}

	pub fn is_node_kind (self, kind: LLVMNodeKind) -> bool {
		kind.test_node(self)
	}

	pub fn is_argument_node (self) -> bool { LLVMValue(unsafe { LLVMIsAArgument(self.into()) }) != LLVMValue::default() }
	pub fn is_basic_block_node (self) -> bool { LLVMValue(unsafe { LLVMIsABasicBlock(self.into()) }) != LLVMValue::default() }
	pub fn is_inline_asm_node (self) -> bool { LLVMValue(unsafe { LLVMIsAInlineAsm(self.into()) }) != LLVMValue::default() }
	pub fn is_user_node (self) -> bool { LLVMValue(unsafe { LLVMIsAUser(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstant(self.into()) }) != LLVMValue::default() }
	pub fn is_block_address_node (self) -> bool { LLVMValue(unsafe { LLVMIsABlockAddress(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_aggregate_zero_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantAggregateZero(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_array_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantArray(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_data_sequential_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantDataSequential(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_data_array_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantDataArray(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_data_vector_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantDataVector(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_expr_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantExpr(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_fp_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantFP(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_int_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantInt(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_pointer_null_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantPointerNull(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_struct_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantStruct(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_token_none_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantTokenNone(self.into()) }) != LLVMValue::default() }
	pub fn is_constant_vector_node (self) -> bool { LLVMValue(unsafe { LLVMIsAConstantVector(self.into()) }) != LLVMValue::default() }
	pub fn is_global_value_node (self) -> bool { LLVMValue(unsafe { LLVMIsAGlobalValue(self.into()) }) != LLVMValue::default() }
	pub fn is_global_alias_node (self) -> bool { LLVMValue(unsafe { LLVMIsAGlobalAlias(self.into()) }) != LLVMValue::default() }
	pub fn is_global_ifunc_node (self) -> bool { LLVMValue(unsafe { LLVMIsAGlobalIFunc(self.into()) }) != LLVMValue::default() }
	pub fn is_global_object_node (self) -> bool { LLVMValue(unsafe { LLVMIsAGlobalObject(self.into()) }) != LLVMValue::default() }
	pub fn is_function_node (self) -> bool { LLVMValue(unsafe { LLVMIsAFunction(self.into()) }) != LLVMValue::default() }
	pub fn is_global_variable_node (self) -> bool { LLVMValue(unsafe { LLVMIsAGlobalVariable(self.into()) }) != LLVMValue::default() }
	pub fn is_undef_value_node (self) -> bool { LLVMValue(unsafe { LLVMIsAUndefValue(self.into()) }) != LLVMValue::default() }
	pub fn is_instruction_node (self) -> bool { LLVMValue(unsafe { LLVMIsAInstruction(self.into()) }) != LLVMValue::default() }
	pub fn is_unary_operator_node (self) -> bool { LLVMValue(unsafe { LLVMIsAUnaryOperator(self.into()) }) != LLVMValue::default() }
	pub fn is_binary_operator_node (self) -> bool { LLVMValue(unsafe { LLVMIsABinaryOperator(self.into()) }) != LLVMValue::default() }
	pub fn is_call_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsACallInst(self.into()) }) != LLVMValue::default() }
	pub fn is_intrinsic_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAIntrinsicInst(self.into()) }) != LLVMValue::default() }
	pub fn is_dbg_info_intrinsic_node (self) -> bool { LLVMValue(unsafe { LLVMIsADbgInfoIntrinsic(self.into()) }) != LLVMValue::default() }
	pub fn is_dbg_variable_intrinsic_node (self) -> bool { LLVMValue(unsafe { LLVMIsADbgVariableIntrinsic(self.into()) }) != LLVMValue::default() }
	pub fn is_dbg_declare_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsADbgDeclareInst(self.into()) }) != LLVMValue::default() }
	pub fn is_dbg_label_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsADbgLabelInst(self.into()) }) != LLVMValue::default() }
	pub fn is_mem_intrinsic_node (self) -> bool { LLVMValue(unsafe { LLVMIsAMemIntrinsic(self.into()) }) != LLVMValue::default() }
	pub fn is_mem_cpy_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAMemCpyInst(self.into()) }) != LLVMValue::default() }
	pub fn is_mem_move_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAMemMoveInst(self.into()) }) != LLVMValue::default() }
	pub fn is_mem_set_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAMemSetInst(self.into()) }) != LLVMValue::default() }
	pub fn is_cmp_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsACmpInst(self.into()) }) != LLVMValue::default() }
	pub fn is_fcmp_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAFCmpInst(self.into()) }) != LLVMValue::default() }
	pub fn is_icmp_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAICmpInst(self.into()) }) != LLVMValue::default() }
	pub fn is_extract_element_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAExtractElementInst(self.into()) }) != LLVMValue::default() }
	pub fn is_get_element_ptr_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAGetElementPtrInst(self.into()) }) != LLVMValue::default() }
	pub fn is_insert_element_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAInsertElementInst(self.into()) }) != LLVMValue::default() }
	pub fn is_insert_value_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAInsertValueInst(self.into()) }) != LLVMValue::default() }
	pub fn is_landing_pad_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsALandingPadInst(self.into()) }) != LLVMValue::default() }
	pub fn is_phi_node (self) -> bool { LLVMValue(unsafe { LLVMIsAPHINode(self.into()) }) != LLVMValue::default() }
	pub fn is_select_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsASelectInst(self.into()) }) != LLVMValue::default() }
	pub fn is_shuffle_vector_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAShuffleVectorInst(self.into()) }) != LLVMValue::default() }
	pub fn is_store_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAStoreInst(self.into()) }) != LLVMValue::default() }
	pub fn is_branch_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsABranchInst(self.into()) }) != LLVMValue::default() }
	pub fn is_indirect_br_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAIndirectBrInst(self.into()) }) != LLVMValue::default() }
	pub fn is_invoke_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAInvokeInst(self.into()) }) != LLVMValue::default() }
	pub fn is_return_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAReturnInst(self.into()) }) != LLVMValue::default() }
	pub fn is_switch_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsASwitchInst(self.into()) }) != LLVMValue::default() }
	pub fn is_unreachable_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAUnreachableInst(self.into()) }) != LLVMValue::default() }
	pub fn is_resume_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAResumeInst(self.into()) }) != LLVMValue::default() }
	pub fn is_cleanup_return_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsACleanupReturnInst(self.into()) }) != LLVMValue::default() }
	pub fn is_catch_return_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsACatchReturnInst(self.into()) }) != LLVMValue::default() }
	pub fn is_catch_switch_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsACatchSwitchInst(self.into()) }) != LLVMValue::default() }
	pub fn is_call_br_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsACallBrInst(self.into()) }) != LLVMValue::default() }
	pub fn is_funclet_pad_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAFuncletPadInst(self.into()) }) != LLVMValue::default() }
	pub fn is_catch_pad_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsACatchPadInst(self.into()) }) != LLVMValue::default() }
	pub fn is_cleanup_pad_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsACleanupPadInst(self.into()) }) != LLVMValue::default() }
	pub fn is_unary_instruction_node (self) -> bool { LLVMValue(unsafe { LLVMIsAUnaryInstruction(self.into()) }) != LLVMValue::default() }
	pub fn is_alloca_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAAllocaInst(self.into()) }) != LLVMValue::default() }
	pub fn is_cast_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsACastInst(self.into()) }) != LLVMValue::default() }
	pub fn is_addr_space_cast_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAAddrSpaceCastInst(self.into()) }) != LLVMValue::default() }
	pub fn is_bit_cast_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsABitCastInst(self.into()) }) != LLVMValue::default() }
	pub fn is_fpext_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAFPExtInst(self.into()) }) != LLVMValue::default() }
	pub fn is_fpto_siinst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAFPToSIInst(self.into()) }) != LLVMValue::default() }
	pub fn is_fpto_uiinst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAFPToUIInst(self.into()) }) != LLVMValue::default() }
	pub fn is_fptrunc_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAFPTruncInst(self.into()) }) != LLVMValue::default() }
	pub fn is_int_to_ptr_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAIntToPtrInst(self.into()) }) != LLVMValue::default() }
	pub fn is_ptr_to_int_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAPtrToIntInst(self.into()) }) != LLVMValue::default() }
	pub fn is_sext_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsASExtInst(self.into()) }) != LLVMValue::default() }
	pub fn is_sito_fpinst_node (self) -> bool { LLVMValue(unsafe { LLVMIsASIToFPInst(self.into()) }) != LLVMValue::default() }
	pub fn is_trunc_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsATruncInst(self.into()) }) != LLVMValue::default() }
	pub fn is_uito_fpinst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAUIToFPInst(self.into()) }) != LLVMValue::default() }
	pub fn is_zext_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAZExtInst(self.into()) }) != LLVMValue::default() }
	pub fn is_extract_value_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAExtractValueInst(self.into()) }) != LLVMValue::default() }
	pub fn is_load_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsALoadInst(self.into()) }) != LLVMValue::default() }
	pub fn is_vaarg_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAVAArgInst(self.into()) }) != LLVMValue::default() }
	pub fn is_freeze_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAFreezeInst(self.into()) }) != LLVMValue::default() }
	pub fn is_atomic_cmp_xchg_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAAtomicCmpXchgInst(self.into()) }) != LLVMValue::default() }
	pub fn is_atomic_rmwinst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAAtomicRMWInst(self.into()) }) != LLVMValue::default() }
	pub fn is_fence_inst_node (self) -> bool { LLVMValue(unsafe { LLVMIsAFenceInst(self.into()) }) != LLVMValue::default() }

	//
	//
	//

	pub fn count_params (self) -> u32 {
		assert!(self.is_function_kind());

		unsafe { LLVMCountParams(self.into()) }
	}

	pub fn get_params (self) -> Vec<LLVMValue> {
		let len = self.count_params() as usize;

		let mut buf = Vec::with_capacity(len);
		unsafe {
			LLVMGetParams(self.into(), buf.as_mut_ptr() as _);
			buf.set_len(len);
		}

		buf
	}


	pub fn add_incoming (self, incoming_values: &[LLVMValue], incoming_blocks: &[LLVMBlock]) {
		assert!(self.is_phi_node());
		assert_eq!(incoming_values.len(), incoming_blocks.len());

		unsafe { LLVMAddIncoming(self.into(), incoming_values.as_ptr() as _, incoming_blocks.as_ptr() as _, incoming_values.len() as _) }
	}

	pub fn add_case (self, predicate: LLVMValue, body: LLVMBlock) {
		assert!(self.is_switch_inst_node());
		unsafe { LLVMAddCase(self.into(), predicate.into(), body.into()) }
	}
}



pub struct LLVM {
	pub ctx: LLVMContextRef,
	pub module: LLVMModuleRef,
	pub builder: LLVMBuilderRef,
}


impl fmt::Display for LLVM {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let alloc = unsafe { LLVMPrintModuleToString(self.module) };
		let s = unsafe { std::ffi::CStr::from_ptr(alloc).to_str().unwrap_or("[Err printing llvm module to string]") };

		write!(f, "{}", s)?;

		unsafe { LLVMDisposeMessage(alloc) }

		Ok(())
	}
}

impl LLVM {
	pub fn new<T: ToLLVMText> (module_name: T) -> Self {
		unsafe {
			let ctx = LLVMContextCreate();
			let module = LLVMModuleCreateWithNameInContext(module_name.to_lltext(), ctx);
			let builder = LLVMCreateBuilderInContext(ctx);

			Self {
				ctx,
				module,
				builder
			}
		}
	}




	pub fn append_basic_block<T: ToLLVMText> (&self, function: LLVMValue, name: T) -> LLVMBlock {
		unsafe { LLVMAppendBasicBlockInContext(self.ctx, function.into(), name.to_lltext()).into() }
	}

	pub fn position_at_end (&self, bb: LLVMBlock) {
		unsafe { LLVMPositionBuilderAtEnd(self.builder, bb.into()) }
	}



	pub fn gep (&self, ty: LLVMType, ptr: LLVMValue, indices: &[LLVMValue]) -> LLVMValue {
		unsafe { LLVMBuildGEP2(
			self.builder,
			ty.into(), ptr.into(),
			indices.as_ptr() as _,
			indices.len() as _,
			Unnamed.to_lltext()
		).into() }
	}






	pub fn fill_agg<T: ToLLVMText + Copy> (&self, mut agg: LLVMValue, value: LLVMValue, len: u32, name: Option<T>) -> LLVMValue {
		for i in 0..len {
			agg = self.insert_value(agg, value, i);
			if let Some(name) = name { agg.set_name(name) }
		}

		agg
	}

	pub fn i2p (&self, e: LLVMValue, new_ty: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildIntToPtr(self.builder, e.into(), new_ty.into(), Unnamed.to_lltext()) .into() }
	}

	pub fn p2i (&self, e: LLVMValue, new_ty: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildPtrToInt(self.builder, e.into(), new_ty.into(), Unnamed.to_lltext()) .into() }
	}

	pub fn i2f (&self, signed: bool, e: LLVMValue, new_ty: LLVMType) -> LLVMValue {
		let to = if signed { LLVMBuildSIToFP } else { LLVMBuildUIToFP };
		unsafe { (to)(self.builder, e.into(), new_ty.into(), Unnamed.to_lltext()).into() }
	}

	pub fn f2i (&self, signed: bool, e: LLVMValue, new_ty: LLVMType) -> LLVMValue {
		let to = if signed { LLVMBuildFPToSI } else { LLVMBuildFPToUI };
		unsafe { (to)(self.builder, e.into(), new_ty.into(), Unnamed.to_lltext()).into() }
	}

	pub fn itrunc (&self, llval: LLVMValue, llty: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildTrunc(self.builder, llval.into(), llty.into(), Unnamed.to_lltext()).into() }
	}

	pub fn ftrunc (&self, llval: LLVMValue, llty: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildFPTrunc(self.builder, llval.into(), llty.into(), Unnamed.to_lltext()).into() }
	}

	pub fn fext (&self, llval: LLVMValue, llty: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildFPExt(self.builder, llval.into(), llty.into(), Unnamed.to_lltext()).into() }
	}

	pub fn zext (&self, llval: LLVMValue, llty: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildZExt(self.builder, llval.into(), llty.into(), Unnamed.to_lltext()).into() }
	}

	pub fn sext (&self, llval: LLVMValue, llty: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildSExt(self.builder, llval.into(), llty.into(), Unnamed.to_lltext()).into() }
	}

	pub fn trunc_or_bitcast (&self, llval: LLVMValue, llty: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildTruncOrBitCast(self.builder, llval.into(), llty.into(), Unnamed.to_lltext()).into() }
	}

	pub fn zext_or_bitcast (&self, llval: LLVMValue, llty: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildZExtOrBitCast(self.builder, llval.into(), llty.into(), Unnamed.to_lltext()).into() }
	}

	pub fn bitcast (&self, llval: LLVMValue, llty: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildBitCast(self.builder, llval.into(), llty.into(), Unnamed.to_lltext()).into() }
	}


	pub fn not (&self, e: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildNot(self.builder, e.into(), Unnamed.to_lltext()).into() }
	}


	pub fn and (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildAnd(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn or (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildOr(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn xor (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildXor(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn logical_r_shift (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildLShr(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn arithmetic_r_shift (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildAShr(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn l_shift (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildShl(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}



	pub fn icmp (&self, pred: LLVMIntPredicate, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildICmp(self.builder, pred, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn ineg (&self, e: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildNeg(self.builder, e.into(), Unnamed.to_lltext()).into() }
	}

	pub fn iadd (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildAdd(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn isub (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildSub(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn imul (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildMul(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn idiv (&self, signed: bool, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		let func = if signed { LLVMBuildSDiv } else { LLVMBuildUDiv };
		unsafe { (func)(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn irem (&self, signed: bool, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		let func = if signed { LLVMBuildSRem } else { LLVMBuildURem };
		unsafe { (func)(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}


	pub fn fcmp (&self, pred: LLVMRealPredicate, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildFCmp(self.builder, pred, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn fneg (&self, e: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildFNeg(self.builder, e.into(), Unnamed.to_lltext()).into() }
	}


	pub fn fadd (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildFAdd(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn fsub (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildFSub(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn fmul (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildFMul(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn fdiv (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildFDiv(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}

	pub fn frem (&self, a: LLVMValue, b: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildFRem(self.builder, a.into(), b.into(), Unnamed.to_lltext()).into() }
	}



	pub fn phi (&self, ty: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildPhi(self.builder, ty.into(), Unnamed.to_lltext()).into() }
	}

	pub fn unreachable (&self) -> LLVMValue {
		unsafe { LLVMBuildUnreachable(self.builder).into() }
	}

	pub fn indirect_branch (&self, dest: LLVMValue, num_dests: u32) -> LLVMValue {
		unsafe { LLVMBuildIndirectBr(self.builder, dest.into(), num_dests).into() }
	}

	pub fn switch (&self, cond: LLVMValue, default: LLVMBlock, num_cases: u32) -> LLVMValue {
		unsafe { LLVMBuildSwitch(self.builder, cond.into(), default.into(), num_cases).into() }
	}

	pub fn cond_branch (&self, cond: LLVMValue, a: LLVMBlock, b: LLVMBlock) -> LLVMValue {
		unsafe { LLVMBuildCondBr(self.builder, cond.into(), a.into(), b.into()).into() }
	}

	pub fn branch (&self, dest: LLVMBlock) -> LLVMValue {
		unsafe { LLVMBuildBr(self.builder, dest.into()).into() }
	}

	pub fn ret (&self, ret_val: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildRet(self.builder, ret_val.into()).into() }
	}


	pub fn ret_void (&self) -> LLVMValue {
		unsafe { LLVMBuildRetVoid(self.builder).into() }
	}


	pub fn insert_value (&self, agg: LLVMValue, new_field: LLVMValue, idx: u32) -> LLVMValue {
		unsafe { LLVMBuildInsertValue(self.builder, agg.into(), new_field.into(), idx, Unnamed.to_lltext()).into() }
	}

	pub fn extract_value (&self, llval: LLVMValue, idx: u32) -> LLVMValue {
		unsafe { LLVMBuildExtractValue(self.builder, llval.into(), idx, Unnamed.to_lltext()).into() }
	}

	pub fn load (&self, llptr: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildLoad(self.builder, llptr.into(), Unnamed.to_lltext()).into() }
	}

	pub fn store (&self, llval: LLVMValue, llptr: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildStore(self.builder, llval.into(), llptr.into()).into() }
	}

	pub fn call (&self, lltype: LLVMType, func: LLVMValue, args: &[LLVMValue]) -> LLVMValue {
		unsafe {
			LLVMBuildCall2(
				self.builder,
				lltype.into(), func.into(),
				args.as_ptr() as _, args.len() as _,
				Unnamed.to_lltext()
			).into()
		}
	}

	pub fn alloca (&self, lltype: LLVMType) -> LLVMValue {
		unsafe { LLVMBuildAlloca(
			self.builder,
			lltype.into(),
			Unnamed.to_lltext()
		).into() }
	}
}

impl Drop for LLVM {
	fn drop (&mut self) {
		unsafe {
			LLVMDisposeBuilder(self.builder);
			LLVMDisposeModule(self.module);
			LLVMContextDispose(self.ctx);
		}
	}
}