use std::fmt;

use llvm_sys::analysis::{LLVMVerifierFailureAction, LLVMVerifyFunction};
pub use llvm_sys::{LLVMTypeKind, LLVMTypeKind::*, LLVMValueKind, LLVMValueKind::*, core::*, prelude::*};
pub use llvm_sys::{LLVMIntPredicate, LLVMIntPredicate::*,};
pub use llvm_sys::{LLVMRealPredicate, LLVMRealPredicate::*,};

pub const LLVMOk: LLVMBool = 0;
pub const LLVMFalse: LLVMBool = 0;
pub const LLVMTrue: LLVMBool = 1;


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
	fn from(s: *const i8) -> LLVMString {
		unsafe {
			let strlen = |p: *const i8| -> usize { let mut len = 0; while *p.add(len) != 0 { len += 1; } len };
			let bytes = std::slice::from_raw_parts(s as _, strlen(s));

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


pub trait OptionalToLLVMText {
	fn opt_to_lltext (&self) -> *const i8;
}

impl<T> OptionalToLLVMText for T where T: ToLLVMText {
	fn opt_to_lltext (&self) -> *const i8 {
		self.to_lltext()
	}
}


impl<T> OptionalToLLVMText for Option<T> where T: ToLLVMText {
	fn opt_to_lltext (&self) -> *const i8 {
		match self {
			Some(v) => v.to_lltext(),
			None => Unnamed.opt_to_lltext()
		}
	}
}

pub struct Unnamed;
impl OptionalToLLVMText for Unnamed {
	fn opt_to_lltext (&self) -> *const i8 {
		b"0" as *const _ as *const _
	}
}



macro_rules! llvm_str {
	($str:literal) => {{
		LLVMStr::from_str(concat!($str, "\0"))
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
	pub fn of (value: LLVMValue) -> LLVMType {
		unsafe { LLVMTypeOf(value.into()).into() }
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

	#[track_caller]
	pub fn get_address_space (self) -> u32 {
		assert_eq!(self.kind(), LLVMPointerTypeKind);

		unsafe { LLVMGetPointerAddressSpace(self.into()) }
	}

	#[track_caller]
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

	#[track_caller]
	pub fn get_int_type_width (self) -> u32 {
		assert_eq!(self.kind(), LLVMIntegerTypeKind);

		unsafe { LLVMGetIntTypeWidth(self.into()) }
	}

	#[track_caller]
	pub fn count_element_types (self) -> u32 {
		assert_eq!(self.kind(), LLVMStructTypeKind);

		unsafe { LLVMCountStructElementTypes(self.0) }
	}

	#[track_caller]
	pub fn get_array_length (self) -> u32 {
		assert_eq!(self.kind(), LLVMArrayTypeKind);

		unsafe { LLVMGetArrayLength(self.0) }
	}

	#[track_caller]
	pub fn get_vector_size (self) -> u32 {
		assert_eq!(self.kind(), LLVMVectorTypeKind);

		unsafe { LLVMGetVectorSize(self.0) }
	}

	pub fn get_type_at_index (self, index: u32) -> LLVMType {
		unsafe { LLVMStructGetTypeAtIndex(self.0, index).into() }
	}

	pub fn is_packed_struct (self) -> bool {
		if self.kind() == LLVMStructTypeKind {
			unsafe { LLVMIsPackedStruct(self.into()) != LLVMFalse }
		} else {
			false
		}
	}

	#[track_caller]
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
		unsafe { LLVMStructTypeInContext(ctx, std::ptr::null_mut(), 0, LLVMFalse).into() }
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


impl LLVMValue {
	pub fn verify_function (self, action: LLVMVerifierFailureAction) -> bool {
		unsafe { LLVMVerifyFunction(self.into(), action) == LLVMOk }
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
		assert_eq!(incoming_values.len(), incoming_blocks.len());

		// TODO: assert this is a phi node
		unsafe { LLVMAddIncoming(self.into(), incoming_values.as_ptr() as _, incoming_blocks.as_ptr() as _, incoming_values.len() as _) }
	}

	pub fn add_case (self, predicate: LLVMValue, body: LLVMBlock) {
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




	pub fn append_basic_block<T: OptionalToLLVMText> (&self, function: LLVMValue, name: T) -> LLVMBlock {
		unsafe { LLVMAppendBasicBlockInContext(self.ctx, function.into(), name.opt_to_lltext()).into() }
	}

	pub fn position_at_end (&self, bb: LLVMBlock) {
		unsafe { LLVMPositionBuilderAtEnd(self.builder, bb.into()) }
	}



	pub fn gep<T: OptionalToLLVMText> (&self, ty: LLVMType, ptr: LLVMValue, indices: &[LLVMValue], name: T) -> LLVMValue {
		unsafe { LLVMBuildGEP2(
			self.builder,
			ty.into(), ptr.into(),
			indices.as_ptr() as _,
			indices.len() as _,
			name.opt_to_lltext()
		).into() }
	}






	pub fn fill_agg (&self, mut agg: LLVMValue, value: LLVMValue, len: u32) -> LLVMValue {
		for i in 0..len {
			agg = self.insert_value(agg, value, i, Unnamed);
		}

		agg
	}


	pub fn i2f<T: OptionalToLLVMText> (&self, signed: bool, e: LLVMValue, new_ty: LLVMType, name: T) -> LLVMValue {
		let to = if signed { LLVMBuildSIToFP } else { LLVMBuildUIToFP };
		unsafe { (to)(self.builder, e.into(), new_ty.into(), name.opt_to_lltext()).into() }
	}

	pub fn f2i<T: OptionalToLLVMText> (&self, signed: bool, e: LLVMValue, new_ty: LLVMType, name: T) -> LLVMValue {
		let to = if signed { LLVMBuildFPToSI } else { LLVMBuildFPToUI };
		unsafe { (to)(self.builder, e.into(), new_ty.into(), name.opt_to_lltext()).into() }
	}

	pub fn itrunc<T: OptionalToLLVMText> (&self, llval: LLVMValue, llty: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMBuildTrunc(self.builder, llval.into(), llty.into(), name.opt_to_lltext()).into() }
	}

	pub fn ftrunc<T: OptionalToLLVMText> (&self, llval: LLVMValue, llty: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMBuildFPTrunc(self.builder, llval.into(), llty.into(), name.opt_to_lltext()).into() }
	}

	pub fn fext<T: OptionalToLLVMText> (&self, llval: LLVMValue, llty: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMBuildFPExt(self.builder, llval.into(), llty.into(), name.opt_to_lltext()).into() }
	}

	pub fn zext<T: OptionalToLLVMText> (&self, llval: LLVMValue, llty: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMBuildZExt(self.builder, llval.into(), llty.into(), name.opt_to_lltext()).into() }
	}

	pub fn sext<T: OptionalToLLVMText> (&self, llval: LLVMValue, llty: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMBuildSExt(self.builder, llval.into(), llty.into(), name.opt_to_lltext()).into() }
	}

	pub fn trunc_or_bitcast<T: OptionalToLLVMText> (&self, llval: LLVMValue, llty: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMBuildTruncOrBitCast(self.builder, llval.into(), llty.into(), name.opt_to_lltext()).into() }
	}

	pub fn zext_or_bitcast<T: OptionalToLLVMText> (&self, llval: LLVMValue, llty: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMBuildZExtOrBitCast(self.builder, llval.into(), llty.into(), name.opt_to_lltext()).into() }
	}

	pub fn bitcast<T: OptionalToLLVMText> (&self, llval: LLVMValue, llty: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMBuildBitCast(self.builder, llval.into(), llty.into(), name.opt_to_lltext()).into() }
	}


	pub fn not<T: OptionalToLLVMText> (&self, e: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildNot(self.builder, e.into(), name.opt_to_lltext()).into() }
	}


	pub fn and<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildAnd(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn or<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildOr(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn xor<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildXor(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn logical_r_shift<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildLShr(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn arithmetic_r_shift<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildAShr(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn l_shift<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildShl(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}



	pub fn icmp<T: OptionalToLLVMText> (&self, pred: LLVMIntPredicate, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildICmp(self.builder, pred, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn ineg<T: OptionalToLLVMText> (&self, e: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildNeg(self.builder, e.into(), name.opt_to_lltext()).into() }
	}

	pub fn iadd<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildAdd(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn isub<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildSub(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn imul<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildMul(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn idiv<T: OptionalToLLVMText> (&self, signed: bool, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		let func = if signed { LLVMBuildSDiv } else { LLVMBuildUDiv };
		unsafe { (func)(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn irem<T: OptionalToLLVMText> (&self, signed: bool, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		let func = if signed { LLVMBuildSRem } else { LLVMBuildURem };
		unsafe { (func)(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}


	pub fn fcmp<T: OptionalToLLVMText> (&self, pred: LLVMRealPredicate, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildFCmp(self.builder, pred, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn fneg<T: OptionalToLLVMText> (&self, e: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildFNeg(self.builder, e.into(), name.opt_to_lltext()).into() }
	}


	pub fn fadd<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildFAdd(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn fsub<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildFSub(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn fmul<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildFMul(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn fdiv<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildFDiv(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}

	pub fn frem<T: OptionalToLLVMText> (&self, a: LLVMValue, b: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildFRem(self.builder, a.into(), b.into(), name.opt_to_lltext()).into() }
	}



	pub fn phi<T: OptionalToLLVMText> (&self, ty: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMBuildPhi(self.builder, ty.into(), name.opt_to_lltext()).into() }
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


	pub fn insert_value<T: OptionalToLLVMText> (&self, agg: LLVMValue, new_field: LLVMValue, idx: u32, name: T) -> LLVMValue {
		unsafe { LLVMBuildInsertValue(self.builder, agg.into(), new_field.into(), idx, name.opt_to_lltext()).into() }
	}

	pub fn extract_value<T: OptionalToLLVMText> (&self, llval: LLVMValue, idx: u32, name: T) -> LLVMValue {
		unsafe { LLVMBuildExtractValue(self.builder, llval.into(), idx, name.opt_to_lltext()).into() }
	}

	pub fn load<T: OptionalToLLVMText> (&self, llptr: LLVMValue, name: T) -> LLVMValue {
		unsafe { LLVMBuildLoad(self.builder, llptr.into(), name.opt_to_lltext()).into() }
	}

	pub fn store (&self, llval: LLVMValue, llptr: LLVMValue) -> LLVMValue {
		unsafe { LLVMBuildStore(self.builder, llval.into(), llptr.into()).into() }
	}

	pub fn call<T: OptionalToLLVMText> (&self, lltype: LLVMType, func: LLVMValue, args: &[LLVMValue], name: T) -> LLVMValue {
		unsafe {
			LLVMBuildCall2(
				self.builder,
				lltype.into(), func.into(),
				args.as_ptr() as _, args.len() as _,
				name.opt_to_lltext()
			).into()
		}
	}

	pub fn alloca<T: OptionalToLLVMText> (&self, lltype: LLVMType, name: T) -> LLVMValue {
		unsafe { LLVMBuildAlloca(
			self.builder,
			lltype.into(),
			name.opt_to_lltext()
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