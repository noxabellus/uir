use uir_core::{
	support::utils::clamp,
	target::{ AMD64 },
};

use super::{Abi, Arg, ArgAttr, Function};
use crate::wrapper::*;



impl Abi for AMD64 {
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

fn llvm_align_formula (offset: u32, align: u32) -> u32 {
	(offset + align - 1) / align * align
}






fn size_of (ty: LLVMType) -> u32 {
	match ty.kind() {
		LLVMVoidTypeKind => 0,
		LLVMIntegerTypeKind => (ty.get_int_type_width() + 7) / 8,
		LLVMFloatTypeKind => 4,
		LLVMDoubleTypeKind => 8,
		LLVMPointerTypeKind => 8,
		LLVMStructTypeKind => {
			let field_count: u32 = ty.count_element_types();
			let mut offset = 0;
			if ty.is_packed_struct() {
				for i in 0..field_count {
					let field = ty.get_type_at_index(i);
					offset += size_of(field);
				}
			} else {
				for i in 0..field_count {
					let field = ty.get_type_at_index(i);
					let align = align_of(field);
					offset = llvm_align_formula(offset, align);
					offset += size_of(field);
				}
				offset = llvm_align_formula(offset, align_of(ty));
			}
			offset
		}
		LLVMArrayTypeKind => {
			let elem = ty.get_element_type();
			let elem_size = size_of(elem);
			let count = ty.get_array_length();
			count * elem_size
		}

		LLVMX86_MMXTypeKind => 8,

		LLVMVectorTypeKind => {
			clamp((ty.get_array_length() * size_of(ty.get_element_type())).next_power_of_two(), 1, 16)
		},

		_ => unreachable!("Unhandled type for size_of: {:?}", ty)
	}
}

fn align_of (ty: LLVMType) -> u32 {
	match ty.kind() {
		LLVMVoidTypeKind => 1,
		LLVMIntegerTypeKind => clamp((ty.get_int_type_width() + 7) / 8, 1, 16),
		LLVMFloatTypeKind => 4,
		LLVMDoubleTypeKind => 8,
		LLVMPointerTypeKind => 8,
		LLVMStructTypeKind => {
			if ty.is_packed_struct() {
				1
			} else {
				let field_count = ty.count_element_types();
				let mut max_align = 1;
				for i in 0..field_count {
					let field = ty.get_type_at_index(i);
					let field_align = align_of(field);
					max_align = max_align.max(field_align);
				}
				max_align
			}
		}
		LLVMArrayTypeKind => align_of(ty.get_element_type()),

		LLVMX86_MMXTypeKind => 8,
		LLVMVectorTypeKind =>	clamp((ty.get_array_length() * size_of(ty.get_element_type())).next_power_of_two(), 1, 16),

		_ => unreachable!("Unhandled type for align_of: {:?}", ty)
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
	X87,
	X87Up,
	ComplexX87,
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

			X87
			=> X87Up,

			_ => return None
		})
	}

	fn all_mem (arr: &mut [RegClass]) {
		arr.iter_mut().for_each(|cl| *cl = Memory)
	}
}



fn is_mem_cls (cls: &[RegClass], attribute: ArgAttr) -> bool {
	let first = if let Some(f) = cls.first() { *f } else { return false };

	   (attribute == ByVal && matches!(first, Memory | X87 | ComplexX87))
	|| (attribute == SRet && matches!(first, Memory))
}

fn is_register (ty: LLVMType) -> bool {
	matches!(ty.kind(),
		  LLVMIntegerTypeKind
		| LLVMFloatTypeKind
		| LLVMDoubleTypeKind
		| LLVMPointerTypeKind
	)
}

fn zext_attr (ty: LLVMType) -> Option<ArgAttr> {
	if ty.is_integer_kind() && ty.get_int_type_width() == 1 {
		Some(ZExt)
	} else {
		None
	}
}

fn amd64_type (ctx: LLVMContextRef, ty: LLVMType, indirect_attribute: ArgAttr) -> Arg {
	if is_register(ty) {
		Arg::direct_attr(ty, zext_attr(ty))
	} else {
		let cls = classify(ty);

		if is_mem_cls(cls.as_slice(), indirect_attribute) {
			Arg::indirect(ty, indirect_attribute)
		} else {
			Arg::direct_cast(ty, llreg(ctx, cls.as_slice()))
		}
	}
}

fn classify (ty: LLVMType) -> Vec<RegClass> {
	let words = (size_of(ty) + 7) / 8;

	let mut reg_classes = vec![NoClass; words as usize];

	if words > 4 {
		RegClass::all_mem(&mut reg_classes);
	} else {
		classify_with(ty, &mut reg_classes, 0, 0);
		fixup(ty, &mut reg_classes);
	}

	reg_classes
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

		| (x @ X87, _) | (x, X87)
		| (x @ X87Up, _) | (x, X87Up)
		| (x @ ComplexX87, _) | (x, ComplexX87)
		=> *x = Memory,

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
				| X87Up => {
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
				let (elems_per_word, elem_type) = match reg_class {
					SSEFv    => (2, LLVMType::float(ctx)),
					SSEDv    => (1, LLVMType::double(ctx)),
					SSEInt8  => (8, LLVMType::int8(ctx)),
					SSEInt16 => (4, LLVMType::int16(ctx)),
					SSEInt32 => (2, LLVMType::int32(ctx)),
					SSEInt64 => (1, LLVMType::int64(ctx)),
					_ => unreachable!()
				};

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


fn classify_with (ty: LLVMType, cls: &mut [RegClass], ix: u32, off: u32) {
	let align = align_of(ty);
	let size  = size_of(ty);

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
			let packed = ty.is_packed_struct();
			let field_count = ty.count_element_types();

			let mut field_off = off;
			for field_index in 0..field_count {
				let field_type = ty.get_type_at_index(field_index);

				if !packed {
					field_off = llvm_align_formula(field_off, align_of(field_type));
				}

				classify_with(field_type, cls, ix, field_off);

				field_off += size_of(field_type);
			}
		}

		LLVMArrayTypeKind => {
			let len = ty.get_array_length();
			let elem = ty.get_element_type();
			let elem_size = size_of(elem);
			for i in 0..len {
				classify_with(elem, cls, ix, off + i * elem_size);
			}
		}

		LLVMVectorTypeKind => {
			let len = ty.get_vector_size();
			let elem = ty.get_element_type();
			let elem_size = size_of(elem);
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