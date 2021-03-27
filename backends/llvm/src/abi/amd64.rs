use uir_core::{target::{ Target, AMD64 }, ty::PrimitiveTy};

use super::{Abi, Arg, ArgAttr, Function, llvm_align_formula};
use crate::wrapper::*;



impl Abi for AMD64 {
	fn triple (&self) -> LLVMString {
		LLVMString::from("x86_64-pc-linux-gnu")
	}

	fn datalayout (&self) -> LLVMString {
		LLVMString::from("e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128")
	}

	fn get_info (&self, ctx: LLVMContextRef, arg_types: &[LLVMType], return_type: LLVMType/*, is_var_args: bool, ProcCallingConvention calling_convention*/ ) -> Function {
		// f.calling_convention = calling_convention;

		let args = arg_types.iter().copied().map(|ty| amd64_type(ctx, ty, ByVal)).collect::<Vec<_>>();

		let result = if return_type.is_void_kind() {
			Arg::direct(return_type)
		} else {
			amd64_type(ctx, return_type, SRet)
		};

		Function::from_data(ctx, args, result)
	}
}



fn amd64_type (ctx: LLVMContextRef, ty: LLVMType, indirect_attribute: ArgAttr) -> Arg {
	if ty.is_register() {
		Arg::direct_attr(ty, if ty.is_integer_kind() && ty.get_int_type_width() == 1 {
			Some(ZExt)
		} else {
			None
		})
	} else {
		let cls = classify(ty);

		if RegClass::is_mem_cls(cls.as_slice(), indirect_attribute) {
			Arg::indirect(ty, indirect_attribute, AMD64.align_of(ty))
		} else {
			Arg::direct_cast(ty, RegClass::llreg(ctx, cls.as_slice()))
		}
	}
}



#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum RegClass {
	NoClass,
	Int,
	SSEFs,
	SSEFv,
	SSEDs,
	SSEDv,
	SSEInt8,
	SSEInt16,
	SSEInt32,
	SSEInt64,
	SSEUp,
	// X87,
	// X87Up,
	// ComplexX87,
	Memory,
}

use RegClass::*;
use ArgAttr::*;

impl Default for RegClass {
	fn default () -> Self {
		Self::NoClass
	}
}

impl RegClass {
	fn is_sse (self) -> bool {
		matches!(self,
			  SSEFs
			| SSEFv
			| SSEDv
		)
	}

	fn get_up (self) -> Option<Self> {
		Some(match self {
			| SSEFs
			| SSEFv
			| SSEDv
			=> SSEUp,

			// X87
			// => X87Up,

			_ => return None
		})
	}

	fn all_mem (arr: &mut [RegClass]) {
		arr.iter_mut().for_each(|cl| *cl = Memory)
	}


	fn is_mem_cls (cls: &[RegClass], attribute: ArgAttr) -> bool {
		let first = if let Some(f) = cls.first() { *f } else { return false };

			(attribute == ByVal && matches!(first, Memory/* | X87 | ComplexX87*/))
		|| (attribute == SRet && matches!(first, Memory))
	}

	fn llreg (ctx: LLVMContextRef, reg_classes: &[RegClass]) -> Vec<LLVMType> {
		let mut types = Vec::with_capacity(reg_classes.len());

		let mut i = 0;

		while i < reg_classes.len() {
			let reg_class = reg_classes[i];

			match reg_class {
				Int => types.push(LLVMType::int64(ctx)),

				| SSEFv
				| SSEDv
				| SSEInt8
				| SSEInt16
				| SSEInt32
				| SSEInt64
				=> {
					let elem_prim = match reg_class {
						SSEFv    => PrimitiveTy::Real32,
						SSEDv    => PrimitiveTy::Real64,
						SSEInt8  => PrimitiveTy::UInt8,
						SSEInt16 => PrimitiveTy::UInt16,
						SSEInt32 => PrimitiveTy::UInt32,
						SSEInt64 => PrimitiveTy::UInt64,
						_ => unreachable!()
					};

					let elem_type = LLVMType::primitive(ctx, elem_prim);
					let elems_per_word = 8 / AMD64.primitive_layout(elem_prim).size;

					types.push(LLVMType::vector(elem_type, elems_per_word));
				}

				SSEFs => types.push(LLVMType::float(ctx)),
				SSEDs => types.push(LLVMType::double(ctx)),

				_ => unreachable!("Unhandled RegClass {:?}", reg_class)
			}

			i += 1;
		}

		debug_assert!(!types.is_empty());

		types
	}
}




fn classify (ty: LLVMType) -> Vec<RegClass> {
	let words = (AMD64.size_of(ty) + 7) / 8;

	let mut reg_classes = vec![NoClass; words as usize];

	if words > 4 {
		RegClass::all_mem(&mut reg_classes);
	} else {
		classify_with(ty, &mut reg_classes, 0, 0);
		fixup(ty, &mut reg_classes);
	}

	reg_classes
}



fn classify_with (ty: LLVMType, cls: &mut [RegClass], ix: u32, off: u32) {
	let align = AMD64.align_of(ty);
	let size  = AMD64.size_of(ty);

	assert!(off % align == 0);

	if off % align != 0 {
		let a = off / 8;
		let b = (off + size + 7) / 8;
		for i in a..b {
			unify(cls, ix + i, Memory);
		}

		return
	}


	let jx = ix + off / 8;

	match ty.kind() {
		| LLVMIntegerTypeKind
		| LLVMPointerTypeKind
		=> unify(cls, jx, Int),

		LLVMFloatTypeKind => {
			let reg =
				if off % 8 == 4 {
					SSEFv
				} else {
					SSEFs
				};

			unify(cls, jx, reg);
		}

		LLVMDoubleTypeKind => unify(cls, jx, SSEDs),

		LLVMStructTypeKind => {
			debug_assert!(!ty.is_packed_struct());

			// let packed = ty.is_packed_struct();
			let field_count = ty.count_element_types();

			let mut field_off = off;
			for field_index in 0..field_count {
				let field_type = ty.get_type_at_index(field_index);

				// if !packed {
					field_off = llvm_align_formula(field_off, AMD64.align_of(field_type));
				// }

				classify_with(field_type, cls, ix, field_off);

				field_off += AMD64.size_of(field_type);
			}
		}

		LLVMArrayTypeKind => {
			let len = ty.get_array_length();
			let elem = ty.get_element_type();
			let elem_size = AMD64.size_of(elem);
			for i in 0..len {
				classify_with(elem, cls, ix, off + i * elem_size);
			}
		}

		LLVMVectorTypeKind => {
			let len = ty.get_vector_size();
			let elem = ty.get_element_type();
			let elem_size = AMD64.size_of(elem);
			let reg =
				match elem.kind() {
					LLVMIntegerTypeKind => {
						match elem.get_int_type_width() {
							8  => SSEInt8,
							16 => SSEInt16,
							32 => SSEInt32,
							64 => SSEInt64,
							x => unreachable!("Unhandled integer width {} for vector type {:?}", x, ty)
						}
					}

					LLVMFloatTypeKind => SSEFv,

					LLVMDoubleTypeKind => SSEDv,

					_ => unreachable!("Unhandled vector element type {:?} for vector type {:?}", elem, ty)
				};

			unify(cls, jx, reg);

			for i in 0..len {
				unify(cls, ix + (off + i * elem_size) / 8, SSEUp)
			}
		}

		_ => unreachable!("Unhandled type {:?}", ty)
	}
}



fn unify (cls: &mut [RegClass], i: u32, newv: RegClass) {
	if cls.is_empty() { return }

	match (&mut cls[i as usize], newv) {
		(x, y) if *x == y => { },

		(x @ NoClass, y) => *x = y,

		| (_, NoClass)
		| (Memory, _) | (_, Memory)
		| (Int, _) | (_, Int)
		=> { },

		// | (x @ X87, _) | (x, X87)
		// | (x @ X87Up, _) | (x, X87Up)
		// | (x @ ComplexX87, _) | (x, ComplexX87)
		// => *x = Memory,

		(x, y) => *x = y,
	}
}



fn fixup (ty: LLVMType, cls: &mut [RegClass]) {
	if cls.len() > 2
	&& (ty.is_struct_kind() || ty.is_array_kind()) {
		if cls[0].is_sse() {
			for &cl in cls[1..].iter() {
				if cl != SSEUp {
					RegClass::all_mem(cls);
					break
				}
			}
		} else {
			RegClass::all_mem(cls);
		}
	} else {
		let mut iter = cls.iter_mut().peekable();

		while let Some(cl) = iter.next() {
			match cl {
				| Memory
				// | X87Up
				=> {
					RegClass::all_mem(cls);
					break
				}

				x @ SSEUp => { *x = SSEDv }

				x => {
					if let Some(ref mut up) = x.get_up() {
						while iter.peek() == Some(&up) { iter.next(); }
					}
				}
			}
		}
	}
}