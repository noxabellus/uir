use std::fmt;

use llvm_sys::{LLVMTypeKind, core::*, prelude::*};

pub const LLVMFalse: LLVMBool = 0;
pub const LLVMTrue: LLVMBool = 1;

#[derive(Default)]
pub struct LLVMString {
    bytes: Vec<u8>,
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

macro_rules! llvm_str {
    ($str:literal) => {
        concat!($str, "\0") as *const str as *const i8
    };
}

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LLVMType(LLVMTypeRef);

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LLVMValue(LLVMValueRef);

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


impl LLVMType {
	pub fn kind (self) -> LLVMTypeKind {
		unsafe { LLVMGetTypeKind(self.into()) }
	}

	pub fn is_kind (self, kind: LLVMTypeKind) -> bool {
		self.kind() == kind
	}

	pub fn is_void_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMVoidTypeKind) }
	pub fn is_half_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMHalfTypeKind) }
	pub fn is_float_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMFloatTypeKind) }
	pub fn is_double_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMDoubleTypeKind) }
	pub fn is_x86_fp80_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMX86_FP80TypeKind) }
	pub fn is_fp128_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMFP128TypeKind) }
	pub fn is_ppc_fp128_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMPPC_FP128TypeKind) }
	pub fn is_label_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMLabelTypeKind) }
	pub fn is_integer_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMIntegerTypeKind) }
	pub fn is_function_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMFunctionTypeKind) }
	pub fn is_struct_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMStructTypeKind) }
	pub fn is_array_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMArrayTypeKind) }
	pub fn is_pointer_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMPointerTypeKind) }
	pub fn is_vector_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMVectorTypeKind) }
	pub fn is_metadata_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMMetadataTypeKind) }
	pub fn is_x86_mmx_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMX86_MMXTypeKind) }
	pub fn is_token_kind (self) -> bool { self.is_kind(LLVMTypeKind::LLVMTokenTypeKind) }


	pub fn get_int_type_width (self) -> u32 {
		assert_eq!(self.kind(), LLVMTypeKind::LLVMIntegerTypeKind);

		unsafe { LLVMGetIntTypeWidth(self.into()) }
	}

	pub fn count_element_types (self) -> u32 {
		assert_eq!(self.kind(), LLVMTypeKind::LLVMStructTypeKind);

		unsafe { LLVMCountStructElementTypes(self.0) }
	}

	pub fn get_array_length (self) -> u32 {
		assert_eq!(self.kind(), LLVMTypeKind::LLVMArrayTypeKind);

		unsafe { LLVMGetArrayLength(self.0) }
	}

	pub fn get_vector_size (self) -> u32 {
		assert_eq!(self.kind(), LLVMTypeKind::LLVMVectorTypeKind);

		unsafe { LLVMGetVectorSize(self.0) }
	}

	pub fn get_type_at_index (self, index: u32) -> LLVMType {
		unsafe { LLVMStructGetTypeAtIndex(self.0, index).into() }
	}

	pub fn is_packed_struct (self) -> bool {
		if self.kind() == LLVMTypeKind::LLVMStructTypeKind {
			unsafe { LLVMIsPackedStruct(self.into()) != LLVMFalse }
		} else {
			false
		}
	}

	pub fn get_element_type (self) -> LLVMType {
		assert!(matches!(self.kind(), LLVMTypeKind::LLVMArrayTypeKind | LLVMTypeKind::LLVMVectorTypeKind));

		unsafe { LLVMGetElementType(self.0).into() }
	}

	pub fn as_pointer (self, address_space: u32) -> LLVMType {
		Self::pointer(self, address_space)
	}

	pub fn as_array (self, length: u32) -> LLVMType {
		Self::array(self, length)
	}

	pub fn int (context: LLVMContextRef, bits: u32) -> LLVMType {
		unsafe { LLVMIntTypeInContext(context, bits).into() }
	}

	pub fn int1 (context: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt1TypeInContext(context).into() }
	}

	pub fn int8 (context: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt8TypeInContext(context).into() }
	}

	pub fn int16 (context: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt16TypeInContext(context).into() }
	}

	pub fn int32 (context: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt32TypeInContext(context).into() }
	}

	pub fn int64 (context: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt64TypeInContext(context).into() }
	}

	pub fn int128 (context: LLVMContextRef) -> LLVMType {
		unsafe { LLVMInt128TypeInContext(context).into() }
	}

	pub fn float (context: LLVMContextRef) -> LLVMType {
		unsafe { LLVMFloatTypeInContext(context).into() }
	}

	pub fn double (context: LLVMContextRef) -> LLVMType {
		unsafe { LLVMDoubleTypeInContext(context).into() }
	}

	pub fn void (context: LLVMContextRef) -> LLVMType {
		unsafe { LLVMVoidTypeInContext(context).into() }
	}

	pub fn label (context: LLVMContextRef) -> LLVMType {
		unsafe { LLVMLabelTypeInContext(context).into() }
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

	pub fn named_empty_structure (context: LLVMContextRef, name: impl Into<LLVMString>) -> LLVMType {
		unsafe { LLVMStructCreateNamed(context, name.into().as_ptr()).into() }
	}

	pub fn anonymous_empty_structure (context: LLVMContextRef) -> LLVMType {
		unsafe { LLVMStructTypeInContext(context, std::ptr::null_mut(), 0, LLVMFalse).into() }
	}

	pub fn structure_set_body (self, field_tys: &[LLVMType], packed: bool) {
		unsafe { LLVMStructSetBody(self.into(), field_tys.as_ptr() as *mut _, field_tys.len() as _, packed as _) }
	}

	pub fn named_structure (context: LLVMContextRef, name: impl Into<LLVMString>, field_tys: &[LLVMType], packed: bool) -> LLVMType {
		let llt = LLVMType::named_empty_structure(context, name);
		llt.structure_set_body(field_tys, packed);
		llt
	}

	pub fn anonymous_structure (context: LLVMContextRef, field_tys: &[LLVMType], packed: bool) -> LLVMType {
		unsafe { LLVMStructTypeInContext(context, field_tys.as_ptr() as *const _ as *mut _, field_tys.len() as _, packed as _).into() }
	}
}


impl LLVMValue {
	pub fn const_null (ty: impl Into<LLVMTypeRef>) -> LLVMValue {
		unsafe { LLVMConstPointerNull(ty.into()).into() }
	}

	pub fn const_int (ty: impl Into<LLVMTypeRef>, value: u128) -> LLVMValue {
		unsafe { LLVMConstIntOfArbitraryPrecision(ty.into(), 2, &value as *const _ as *const _).into() }
	}

	pub fn const_real (ty: impl Into<LLVMTypeRef>, value: f64) -> LLVMValue {
		unsafe { LLVMConstReal(ty.into(), value).into() }
	}

	pub fn create_global (module: impl Into<LLVMModuleRef>, ty: impl Into<LLVMTypeRef>, name: impl Into<LLVMString>) -> LLVMValue {
		unsafe { LLVMAddGlobal(module.into(), ty.into(), name.into().as_ptr()).into() }
	}

	pub fn create_function (module: impl Into<LLVMModuleRef>, ty: impl Into<LLVMTypeRef>, name: impl Into<LLVMString>) -> LLVMValue {
		unsafe { LLVMAddFunction(module.into(), name.into().as_ptr(), ty.into()).into() }
	}

	pub fn set_global_initializer (self, const_init: impl Into<LLVMValueRef>) {
		unsafe { LLVMSetInitializer(self.into(), const_init.into()) }
	}
}