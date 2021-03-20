use crate::wrapper::*;

use std::any::{ TypeId };
use uir_core::{
	support::utils::clamp,
	target::{self, Target},
	ty::PrimitiveTy
};


mod amd64;



#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArgAttr {
	SRet,
	ZExt,
	ByVal,
	// ByRef,
	// Preallocated,
	// NoAlias,
	// NonNull,
	// NoCapture,
}

impl ArgAttr {
	pub fn as_cstr (self) -> &'static [i8] {
		use ArgAttr::*;
		unsafe { *(match self {
			SRet => "sret\0",
			ZExt => "zext\0",
			ByVal => "byval\0",
			// ByRef => "byref\0",
			// Preallocated => "preallocated\0",
			// NoAlias => "noalias\0",
			// NonNull => "nonnull\0",
			// NoCapture => "nocapture\0",
		} as *const _ as *const _) }
	}

	pub fn to_llvm (self, ctx: LLVMContextRef) -> Option<LLVMAttributeRef> {
		use ArgAttr::*;
		if matches!(self,
			  SRet
			| ZExt
			| ByVal
			// | NoAlias
			// | NonNull
			// | NoCapture
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
	// Ignore,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Arg {
	pub kind: ArgKind,
	pub base_type: LLVMType,
	pub cast_types: Vec<LLVMType>,
	// pub pad_type: Option<LLVMType>,
	pub attribute: Option<ArgAttr>,
}

impl Arg {
	fn direct_custom (base_type: LLVMType, cast_types: Vec<LLVMType>, attribute: Option<ArgAttr>) -> Self {
		Self {
			kind: ArgKind::Direct,
			base_type, cast_types,
			attribute
		}
	}

	fn direct_cast (base_type: LLVMType, cast_types: Vec<LLVMType>) -> Self {
		Self::direct_custom(base_type, cast_types, None)
	}

	fn direct_attr (base_type: LLVMType, attribute: Option<ArgAttr>) -> Self {
		Self::direct_custom(base_type, vec![], attribute)
	}

	fn direct (base_type: LLVMType) -> Self {
		Self::direct_custom(base_type, vec![], None)
	}


	fn indirect (base_type: LLVMType, attribute: ArgAttr) -> Self {
		Self {
			kind: ArgKind::Indirect,
			base_type,
			cast_types: vec![],
			attribute: Some(attribute)
		}
	}

	// fn ignore (base_type: LLVMType) -> Self {
	// 	Self {
	// 		kind: ArgKind::Ignore,
	// 		base_type,
	// 		cast_types: vec![],
	// 		attribute: None
	// 	}
	// }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Function {
	pub args: Vec<Arg>,
	pub result: Arg,
	pub lltype: LLVMType
}

impl Function {
	pub fn from_data (ctx: LLVMContextRef, args: Vec<Arg>, result: Arg) -> Self {
		// if is_var_args { todo!() }

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

			// ArgKind::Ignore => {
			// 	LLVMType::void(ctx)
			// }
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

				// ArgKind::Ignore => {
				// 	continue
				// }
			}
		}

		Self {
			args,
			result,
			lltype: LLVMType::function(llargs.as_slice(), ret, false)
		}
	}

	pub fn apply_attributes (&self, ctx: LLVMContextRef, func: LLVMValue, /* ProcCallingConvention calling_convention */) {
		let offset: u32 = if self.result.kind == ArgKind::Indirect { 1 } else { 0 };

		for (i, arg) in self.args.iter().enumerate() {
			// if arg.kind == ArgKind::Ignore { continue }

			if let Some(attribute) = arg.attribute {
				attribute.apply(ctx, func, i as u32 + offset + 1);
			}
		}

		if offset != 0 {
			if let Some(attribute) = self.result.attribute {
				attribute.apply(ctx, func, offset);
				// TODO: ArgAttr::NoAlias.apply(ctx, func, offset);
			}
		}

		// lbCallingConventionKind cc_kind = lbCallingConvention_C;
		// if (build_context.metrics.os != TargetOs_js)  {
		// 	cc_kind = lb_calling_convention_map[calling_convention];
		// }
		// LLVMSetFunctionCallConv(func, cc_kind);
	}
}



fn llvm_align_formula (offset: u32, align: u32) -> u32 {
	(offset + align - 1) / align * align
}

pub trait Abi: Target {
	fn get_info (&self, context: LLVMContextRef, args: &[LLVMType], ret_ty: LLVMType) -> Function;
	fn word_bits (&self) -> u32 {
		self.word_size() as u32 * 8
	}

	fn llvm_ty_to_prim (&self, ty: LLVMType) -> PrimitiveTy {
		match ty.kind() {
			LLVMIntegerTypeKind => match ty.get_int_type_width_bytes() {
				1 => PrimitiveTy::UInt8,
				2 => PrimitiveTy::UInt16,
				4 => PrimitiveTy::UInt32,
				8 => PrimitiveTy::UInt64,
				16 => PrimitiveTy::UInt128,
				x => unreachable!("Cannot create prim ty from unsupported integer size {:?}", x)
			},
			LLVMFloatTypeKind => PrimitiveTy::Real32,
			LLVMDoubleTypeKind => PrimitiveTy::Real64,
			LLVMPointerTypeKind => self.pointer_int(),
			LLVMX86_MMXTypeKind => PrimitiveTy::Real64,
			x => unreachable!("Cannot create prim ty from unsupported type {:?}", x)
		}
	}

	fn size_of (&self, ty: LLVMType) -> u32 {
		match ty.kind() {
			LLVMVoidTypeKind => 0,

			| LLVMIntegerTypeKind
			| LLVMFloatTypeKind
			| LLVMDoubleTypeKind
			| LLVMPointerTypeKind
			| LLVMX86_MMXTypeKind
			=> self.primitive_layout(self.llvm_ty_to_prim(ty)).size,

			LLVMStructTypeKind => {
				let field_count: u32 = ty.count_element_types();
				let mut offset = 0;
				if ty.is_packed_struct() {
					for i in 0..field_count {
						let field = ty.get_type_at_index(i);
						offset += self.size_of(field);
					}
				} else {
					for i in 0..field_count {
						let field = ty.get_type_at_index(i);
						let align = self.align_of(field);
						offset = llvm_align_formula(offset, align);
						offset += self.size_of(field);
					}
					offset = llvm_align_formula(offset, self.align_of(ty));
				}
				offset
			}
			LLVMArrayTypeKind => {
				let elem = ty.get_element_type();
				let elem_size = self.size_of(elem);
				let count = ty.get_array_length();
				count * elem_size
			}

			LLVMVectorTypeKind => {
				clamp((ty.get_array_length() * self.size_of(ty.get_element_type())).next_power_of_two(), 1, 16)
			},

			_ => unreachable!("Unhandled type for size_of: {:?}", ty)
		}
	}

	fn align_of (&self, ty: LLVMType) -> u32 {
		match ty.kind() {
			LLVMVoidTypeKind => 1,

			| LLVMIntegerTypeKind
			| LLVMFloatTypeKind
			| LLVMDoubleTypeKind
			| LLVMPointerTypeKind
			| LLVMX86_MMXTypeKind
			=> self.primitive_layout(self.llvm_ty_to_prim(ty)).align,

			LLVMStructTypeKind => {
				if ty.is_packed_struct() {
					1
				} else {
					let field_count = ty.count_element_types();
					let mut max_align = 1;
					for i in 0..field_count {
						let field = ty.get_type_at_index(i);
						let field_align = self.align_of(field);
						max_align = max_align.max(field_align);
					}
					max_align
				}
			}
			LLVMArrayTypeKind => self.align_of(ty.get_element_type()),
			LLVMVectorTypeKind =>	clamp((ty.get_array_length() * self.size_of(ty.get_element_type())).next_power_of_two(), 1, 16),

			_ => unreachable!("Unhandled type for align_of: {:?}", ty)
		}
	}
}

pub fn get_abi (t: &dyn Target) -> Option<Box<dyn Abi>> {
	macro_rules! conversions {
		($( $ty:ident ),* $(,)?) => {
			Some(match t.type_id() {
				$(
					id if id == TypeId::of::<target::$ty>()
					=> unsafe { Box::new(*(t as *const dyn Target as *const target::$ty)) as Box<dyn Abi + 'static> }
				)*

				_ => return None
			})
		}
	}

	conversions! {
		AMD64,
	}
}