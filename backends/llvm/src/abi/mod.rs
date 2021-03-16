use super::wrapper::*;

use std::any::{ TypeId };
use uir_core::target::{self, Target};

use llvm_sys::{ core::*, prelude::* };


mod amd64;



#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArgAttr {
	SRet,
	ZExt,
	ByVal,
	ByRef,
	Preallocated,
	NoAlias,
	NonNull,
	NoCapture,
}

impl ArgAttr {
	pub fn as_cstr (self) -> &'static [i8] {
		use ArgAttr::*;
		unsafe { *(match self {
			SRet => "sret\0",
			ZExt => "zext\0",
			ByVal => "byval\0",
			ByRef => "byref\0",
			Preallocated => "preallocated\0",
			NoAlias => "noalias\0",
			NonNull => "nonnull\0",
			NoCapture => "nocapture\0",
		} as *const _ as *const _) }
	}

	pub fn to_llvm (self, ctx: LLVMContextRef) -> Option<LLVMAttributeRef> {
		use ArgAttr::*;
		if matches!(self,
			  SRet
			| ZExt
			| ByVal
			| NoAlias
			| NonNull
			| NoCapture
		) {
			// if cfg!(debug_assertions) {
				// eprintln!("Warning: {:?} does not support conversion to LLVM yet; returning None", self);
			// }

			None
		} else {
			let name = self.as_cstr();

			Some(unsafe { LLVMCreateEnumAttribute(ctx, LLVMGetEnumAttributeKindForName(name.as_ptr(), name.len() as _), 1) })
		}
	}

	pub fn apply (self, ctx: LLVMContextRef, func: LLVMValue, index: u32) {
		if let Some(llattr) = self.to_llvm(ctx) {
			unsafe { LLVMAddAttributeAtIndex(func.into(), index, llattr) }
		}
	}
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArgKind {
	Direct,
	Indirect,
	Ignore,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Arg {
	pub kind: ArgKind,
	pub base_type: LLVMType,
	pub cast_types: Vec<LLVMType>,
	pub pad_type: Option<LLVMType>,
	pub attribute: Option<ArgAttr>,
}

impl Arg {
	fn direct_custom (base_type: LLVMType, cast_types: Vec<LLVMType>, pad_type: Option<LLVMType>, attribute: Option<ArgAttr>) -> Self {
		Self {
			kind: ArgKind::Direct,
			base_type, cast_types, pad_type,
			attribute
		}
	}

	fn direct_cast (base_type: LLVMType, cast_types: Vec<LLVMType>) -> Self {
		Self::direct_custom(base_type, cast_types, None, None)
	}

	fn direct_attr (base_type: LLVMType, attribute: Option<ArgAttr>) -> Self {
		Self::direct_custom(base_type, vec![], None, attribute)
	}

	fn direct (base_type: LLVMType) -> Self {
		Self::direct_custom(base_type, vec![], None, None)
	}


	fn indirect (base_type: LLVMType, attribute: ArgAttr) -> Self {
		Self {
			kind: ArgKind::Indirect,
			base_type,
			cast_types: vec![],
			pad_type: None,
			attribute: Some(attribute)
		}
	}

	fn ignore (base_type: LLVMType) -> Self {
		Self {
			kind: ArgKind::Ignore,
			base_type,
			cast_types: vec![],
			pad_type: None,
			attribute: None
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Function {
	pub args: Vec<Arg>,
	pub result: Arg,
	pub ty: LLVMType
}

impl Function {
	pub fn from_data (ctx: LLVMContextRef, args: Vec<Arg>, result: Arg, is_var_args: bool) -> Self {
		if is_var_args { todo!() }

		let mut llargs = Vec::default();

		let ret = match result.kind {
			ArgKind::Direct => {
				if result.cast_types.is_empty() {
					result.base_type
				} else if result.cast_types.len() == 1 {
					result.cast_types[0]
				} else {
					LLVMType::anonymous_structure(ctx, &result.cast_types, false)
				}
			}

			ArgKind::Indirect => {
				llargs.push(result.base_type.as_pointer(0));
				LLVMType::void(ctx)
			}

			ArgKind::Ignore => {
				LLVMType::void(ctx)
			}
		};

		for arg in args.iter() {
			match arg.kind {
				ArgKind::Direct => {
					if arg.cast_types.is_empty() {
						llargs.push(arg.base_type)
					} else if arg.cast_types.len() == 1 {
						llargs.push(arg.cast_types[0])
					} else {
						arg.cast_types.iter().for_each(|&c| llargs.push(c))
					}
				}

				ArgKind::Indirect => {
					debug_assert!(!arg.base_type.is_pointer_kind());

					llargs.push(arg.base_type.as_pointer(0));
				}

				ArgKind::Ignore => {
					continue
				}
			}
		}

		Self {
			args,
			result,
			ty: LLVMType::function(llargs.as_slice(), ret, is_var_args)
		}
	}

	pub fn apply_attributes (&self, ctx: LLVMContextRef, func: LLVMValue, /* ProcCallingConvention calling_convention */) {
		let offset: u32 = if self.result.kind == ArgKind::Indirect { 1 } else { 0 };

		for (i, arg) in self.args.iter().enumerate() {
			if arg.kind == ArgKind::Ignore { continue }

			if let Some(attribute) = arg.attribute {
				attribute.apply(ctx, func, i as u32 + offset + 1);
			}
		}

		if offset != 0
		&& self.result.kind == ArgKind::Indirect {
			if let Some(attribute) = self.result.attribute {
				attribute.apply(ctx, func, offset);
				ArgAttr::NoAlias.apply(ctx, func, offset);
			}
		}

		// lbCallingConventionKind cc_kind = lbCallingConvention_C;
		// if (build_context.metrics.os != TargetOs_js)  {
		// 	cc_kind = lb_calling_convention_map[calling_convention];
		// }
		// LLVMSetFunctionCallConv(func, cc_kind);
	}
}


pub trait Abi: Target {
	fn get_info (&self, context: LLVMContextRef, args: &[LLVMType], ret_ty: Option<LLVMType>, is_var_args: bool) -> Function;
}

pub fn get_abi (t: &dyn Target) -> Option<&dyn Abi> {
	macro_rules! conversions {
		($( $ty:ident ),* $(,)?) => {
			Some(match t.type_id() {
				$(
					id if id == TypeId::of::<target::$ty>()
					=> unsafe { &*(t as *const dyn Target as *const target::$ty) }
				)*

				_ => return None
			})
		}
	}

	conversions! {
		AMD64,
	}
}