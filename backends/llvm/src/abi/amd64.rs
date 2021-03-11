use uir_core::{
	support::utils::clamp,
	target::{ AMD64 },
};

use llvm_sys::{ LLVMTypeKind, prelude::* };

use super::{Abi, Arg, ArgAttr, Function};
use crate::wrapper::*;



impl Abi for AMD64 {
	fn get_info (&self, ctx: LLVMContextRef, arg_types: &[LLVMType], return_type: Option<LLVMType>, is_var_args: bool, /*ProcCallingConvention calling_convention*/ ) -> Function {
		// f.calling_convention = calling_convention;

		let args = arg_types.iter().copied().map(|ty| amd64_type(ctx, ty, ArgAttr::ByVal)).collect::<Vec<_>>();

		let result = return_type.map_or_else(
			|| Arg::direct(LLVMType::void(ctx)),
			|rt| amd64_type(ctx, rt, ArgAttr::SRet)
		);

		Function::from_data(ctx, args, result, is_var_args)
	}
}

fn llvm_align_formula (offset: u32, align: u32) -> u32 {
	(offset + align - 1) / align * align
}






fn size_of (ty: LLVMType) -> u32 {
	use LLVMTypeKind::*;
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
	use LLVMTypeKind::*;
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

impl Default for RegClass {
	fn default () -> Self {
		Self::NoClass
	}
}

impl RegClass {
	fn is_sse (self) -> bool {
		matches!(self,
			  RegClass::SSEFs
			| RegClass::SSEFv
			| RegClass::SSEDv
		)
	}

	fn all_mem (arr: &mut [RegClass]) {
		arr.iter_mut().for_each(|cl| *cl = RegClass::Memory)
	}
}



fn is_mem_cls (cls: &[RegClass], attribute: ArgAttr) -> bool {
	let first = if let Some(f) = cls.first() { *f } else { return false };

	match attribute {
		ArgAttr::ByVal => {
			first == RegClass::Memory || first == RegClass::X87 || first == RegClass::ComplexX87
		}

		ArgAttr::SRet => {
			first == RegClass::Memory
		}

		_ => false
	}
}

fn is_register (ty: LLVMType) -> bool {
	use LLVMTypeKind::*;
	matches!(ty.kind(),
		  LLVMIntegerTypeKind
		| LLVMFloatTypeKind
		| LLVMDoubleTypeKind
		| LLVMPointerTypeKind
	)
}

fn zext_attr (ty: LLVMType) -> Option<ArgAttr> {
	if ty.is_integer_kind() && ty.get_int_type_width() == 1 {
		Some(ArgAttr::ZExt)
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
			Arg::direct_custom(ty, llreg(ctx, cls.as_slice()), None, None)
		}
	}
}

fn classify (ty: LLVMType) -> Vec<RegClass> {
	let words = (size_of(ty) + 7) / 8;

	debug_assert!(dbg!(words) > 0);

	let mut reg_classes = vec![RegClass::NoClass; words as usize];

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

		(x @ RegClass::NoClass, y) => *x = y,

		| (_, RegClass::NoClass)
		| (RegClass::Memory, _) | (_, RegClass::Memory)
		| (RegClass::Int, _) | (_, RegClass::Int)
		=> { },

		| (x @ RegClass::X87, _) | (x, RegClass::X87)
		| (x @ RegClass::X87Up, _) | (x, RegClass::X87Up)
		| (x @ RegClass::ComplexX87, _) | (x, RegClass::ComplexX87)
		=> *x = RegClass::Memory,

		(x, y) => *x = y,
	}
}

fn fixup (ty: LLVMType, cls: &mut [RegClass]) {
	let e = cls.len();

	if e > 2
	&& (ty.is_struct_kind() || ty.is_array_kind()) {
		if cls[0].is_sse() {
			for i in 1..e {
				if cls[i] != RegClass::SSEUp {
					RegClass::all_mem(cls);
					return;
				}
			}
		} else {
			RegClass::all_mem(cls);
		}
	} else {
		let mut i = 0;

		while i < e {
			match &mut cls[i] {
				| RegClass::Memory
				| RegClass::X87Up => {
					RegClass::all_mem(cls);
					return
				}

				x @ RegClass::SSEUp => {
					*x = RegClass::SSEDv;
				}

				x if x.is_sse() => {
					i += 1;
					while i != e && cls[i] == RegClass::SSEUp {
						i += 1;
					}
				}

				RegClass::X87 => {
					i += 1;
					while i != e && cls[i] == RegClass::X87Up {
						i += 1;
					}
				}

				_ => i += 1
			}
		}
	}
}

fn llvec_len (reg_classes: &[RegClass], offset: usize) -> u32 {
	let mut len = 1;

	for i in (offset + 1)..reg_classes.len() {
		if reg_classes[offset] != RegClass::SSEFv
		&& reg_classes[i] != RegClass::SSEUp {
			break
		}

		len += 1;
	}

	len
}


fn llreg (ctx: LLVMContextRef, reg_classes: &[RegClass]) -> Vec<LLVMType> {
	let mut types = Vec::with_capacity(reg_classes.len());

	let mut i = 0;

	while i < reg_classes.len() {
		let reg_class = reg_classes[i];

		match reg_class {
			RegClass::Int => types.push(LLVMType::int64(ctx)),

			| RegClass::SSEFv
			| RegClass::SSEDv
			| RegClass::SSEInt8
			| RegClass::SSEInt16
			| RegClass::SSEInt32
			| RegClass::SSEInt64
			=> {
				let (elems_per_word, elem_type) = match reg_class {
					RegClass::SSEFv => (2, LLVMType::float(ctx)),
					RegClass::SSEDv => (1, LLVMType::double(ctx)),
					RegClass::SSEInt8 => (8, LLVMType::int8(ctx)),
					RegClass::SSEInt16 => (4, LLVMType::int16(ctx)),
					RegClass::SSEInt32 => (2, LLVMType::int32(ctx)),
					RegClass::SSEInt64 => (1, LLVMType::int64(ctx)),
					_ => unreachable!()
				};

				let vec_len = llvec_len(reg_classes, i);
				let vec_type = LLVMType::vector(elem_type, vec_len * elems_per_word);

				types.push(vec_type);

				i += vec_len as usize;

				continue;
			}
			RegClass::SSEFs => types.push(LLVMType::float(ctx)),
			RegClass::SSEDs => types.push(LLVMType::double(ctx)),

			_ => unreachable!("Unhandled RegClass {:?}", reg_class)
		}

		i += 1;
	}

	debug_assert!(!types.is_empty());

	types
}


fn classify_with (ty: LLVMType, cls: &mut [RegClass], ix: u32, off: u32) {
	let t_align = align_of(ty);
	let t_size  = size_of(ty);

	let misalign = off % t_align;
	if misalign != 0 {
		for i in (off / 8)..((off + t_size + 7) / 8) {
			unify(cls, ix + i, RegClass::Memory);
		}

		return
	}

	use LLVMTypeKind::*;

	match ty.kind() {
		| LLVMIntegerTypeKind
		| LLVMPointerTypeKind
		=> unify(cls, ix + off / 8, RegClass::Int),

		LLVMFloatTypeKind => unify(cls, ix + off/8, if off % 8 == 4 { RegClass::SSEFv } else { RegClass::SSEFs }),

		LLVMDoubleTypeKind => unify(cls, ix + off / 8, RegClass::SSEDs),

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
			let mut reg = match elem.kind() {
				LLVMIntegerTypeKind => {
					match elem.get_int_type_width() {
						8 =>  RegClass::SSEInt8,
						16 => RegClass::SSEInt16,
						32 => RegClass::SSEInt32,
						64 => RegClass::SSEInt64,
						x => unreachable!("Unhandled integer width {} for vector type {:?}", x, ty)
					}
				}

				LLVMFloatTypeKind => RegClass::SSEFv,

				LLVMDoubleTypeKind => RegClass::SSEDv,

				_ => unreachable!("Unhandled vector element type {:?} for vector type {:?}", elem, ty)
			};

			for i in 0..len {
				unify(cls, ix + (off + i * elem_size) / 8, reg);

				reg = RegClass::SSEUp;
			}
		}

		_ => unreachable!("Unhandled type {:?}", ty)
	}
}

fn compute_arg_types (arg_types: &[LLVMType]) -> Vec<Arg> {
	arg_types.iter().map(|&ty| {
		if ty.is_struct_kind() {
			if size_of(ty) == 0 {
				Arg::ignore(ty)
			} else {
				Arg::indirect(ty, ArgAttr::ByVal)
			}
		} else {
			Arg::direct_attr(ty, zext_attr(ty))
		}
	}).collect()
}

fn compute_return_type (ctx: LLVMContextRef, return_type: Option<LLVMType>) -> Arg {
	let return_type =  if let Some(t) = return_type { t } else {
		return Arg::direct(LLVMType::void(ctx))
	};

	if return_type.is_struct_kind() {
		match size_of(return_type) {
			1 => Arg::direct_cast(return_type, vec![LLVMType::int8(ctx)]),
			2 => Arg::direct_cast(return_type, vec![LLVMType::int16(ctx)]),
			4 => Arg::direct_cast(return_type, vec![LLVMType::int32(ctx)]),
			8 => Arg::direct_cast(return_type, vec![LLVMType::int64(ctx)]),

			_ => Arg::indirect(return_type, ArgAttr::SRet)
		}
	} else {
		Arg::direct_attr(return_type, zext_attr(return_type))
	}
}



/*
	// #define LB_ABI_INFO(name) lbFunctionType *name(LLVMContextRef c, LLVMType *arg_types, unsigned arg_count, LLVMType return_type, bool return_is_defined, ProcCallingConvention calling_convention)
	// typedef LB_ABI_INFO(lbAbiInfoType);


	// // NOTE(bill): I hate `namespace` in C++ but this is just because I don't want to prefix everything
	// namespace lbAbi386 {
	// 	Array<lbArgType> compute_arg_types(LLVMContextRef c, LLVMType *arg_types, unsigned arg_count);
	// 	lbArgType compute_return_type(LLVMContextRef c, LLVMType return_type, bool return_is_defined);

	// 	LB_ABI_INFO(abi_info) {
	// 		lbFunctionType *ft = gb_alloc_item(heap_allocator(), lbFunctionType);
	// 		f.ctx = c;
	// 		f.args = compute_arg_types(c, arg_types, arg_count);
	// 		f.result = compute_return_type(c, return_type, return_is_defined);
	// 		f.calling_convention = calling_convention;
	// 		return ft;
	// 	}

	// 	lbArgType non_struct(LLVMContextRef c, LLVMType type, bool is_return) {
	// 		if (!is_return && size_of(type) > 8) {
	// 			return Arg::indirect(type, nullptr);
	// 		}

	// 		if (build_context.metrics.os == TargetOs_windows &&
	// 		    build_context.word_size == 8 &&
	// 		    lb_is_type_kind(type, LLVMIntegerTypeKind) &&
	// 		    type == LLVMIntTypeInContext(c, 128)) {
	// 		    	// NOTE(bill): Because Windows AMD64 is weird
	// 		    	// TODO(bill): LLVM is probably bugged here and doesn't correctly generate the right code
	// 		    	// So even though it is "technically" wrong, no cast might be the best option
	// 		    	LLVMType cast_type = nullptr;
	// 		    	if (true || !is_return) {
	// 				cast_type = LLVMVectorType(LLVMInt64TypeInContext(c), 2);
	// 			}
	// 			return Arg::direct(type, cast_type, nullptr, nullptr);
	// 		}

	// 		LLVMAttributeRef attr = nullptr;
	// 		LLVMType i1 = LLVMInt1TypeInContext(c);
	// 		if (type == i1) {
	// 			attr = lb_create_enum_attribute(c, "zeroext", true);
	// 		}
	// 		return Arg::direct(type, nullptr, nullptr, attr);
	// 	}

	// 	Array<lbArgType> compute_arg_types(LLVMContextRef c, LLVMType *arg_types, unsigned arg_count) {
	// 		let args = array_make<lbArgType>(heap_allocator(), arg_count);

	// 		for (unsigned i = 0; i < arg_count; i += 1) {
	// 			LLVMType t = arg_types[i];
	// 			LLVMTypeKind kind = LLVMGetTypeKind(t);
	// 			i64 sz = size_of(t);
	// 			if (kind == LLVMStructTypeKind) {
	// 				if (sz == 0) {
	// 					args[i] = Arg::ignore(t);
	// 				} else {
	// 					args[i] = Arg::indirect(t, lb_create_enum_attribute(c, "byval", true));
	// 				}
	// 			} else {
	// 				args[i] = non_struct(c, t, false);
	// 			}
	// 		}
	// 		return args;
	// 	}

	// 	lbArgType compute_return_type(LLVMContextRef c, LLVMType return_type, bool return_is_defined) {
	// 		if (!return_is_defined) {
	// 			return Arg::direct(LLVMVoidTypeInContext(c));
	// 		} else if (lb_is_type_kind(return_type, LLVMStructTypeKind) || lb_is_type_kind(return_type, LLVMArrayTypeKind)) {
	// 			i64 sz = size_of(return_type);
	// 			switch (sz) {
	// 			1 => return Arg::direct(return_type, LLVMIntTypeInContext(c,  8), nullptr, nullptr);
	// 			2 => return Arg::direct(return_type, LLVMIntTypeInContext(c, 16), nullptr, nullptr);
	// 			4 => return Arg::direct(return_type, LLVMIntTypeInContext(c, 32), nullptr, nullptr);
	// 			8 => return Arg::direct(return_type, LLVMIntTypeInContext(c, 64), nullptr, nullptr);
	// 			}
	// 			LLVMAttributeRef attr = lb_create_enum_attribute(c, "sret", true);
	// 			return Arg::indirect(return_type, attr);
	// 		}
	// 		return non_struct(c, return_type, true);
	// 	}
	// };

	// namespace lbAbiAmd64Win64 {
	// 	Array<lbArgType> compute_arg_types(LLVMContextRef c, LLVMType *arg_types, unsigned arg_count);


	// 	LB_ABI_INFO(abi_info) {
	// 		lbFunctionType *ft = gb_alloc_item(heap_allocator(), lbFunctionType);
	// 		f.ctx = c;
	// 		f.args = compute_arg_types(c, arg_types, arg_count);
	// 		f.result = lbAbi386::compute_return_type(c, return_type, return_is_defined);
	// 		f.calling_convention = calling_convention;
	// 		return ft;
	// 	}

	// 	Array<lbArgType> compute_arg_types(LLVMContextRef c, LLVMType *arg_types, unsigned arg_count) {
	// 		let args = array_make<lbArgType>(heap_allocator(), arg_count);

	// 		for (unsigned i = 0; i < arg_count; i += 1) {
	// 			LLVMType t = arg_types[i];
	// 			LLVMTypeKind kind = LLVMGetTypeKind(t);
	// 			if (kind == LLVMStructTypeKind) {
	// 				i64 sz = size_of(t);
	// 				switch (sz) {
	// 				1 =>
	// 				2 =>
	// 				4 =>
	// 				8 =>
	// 					args[i] = Arg::direct(t, LLVMIntTypeInContext(c, 8*cast(unsigned)sz), nullptr, nullptr);
	// 					break;
	// 				_ =>
	// 					args[i] = Arg::indirect(t, nullptr);
	// 					break;
	// 				}
	// 			} else {
	// 				args[i] = lbAbi386::non_struct(c, t, false);
	// 			}
	// 		}
	// 		return args;
	// 	}
	// };

	// // NOTE(bill): I hate `namespace` in C++ but this is just because I don't want to prefix everything

	// namespace lbAbiArm64 {
	// 	Array<lbArgType> compute_arg_types(LLVMContextRef c, LLVMType *arg_types, unsigned arg_count);
	// 	lbArgType compute_return_type(LLVMContextRef c, LLVMType return_type, bool return_is_defined);
	// 	bool is_homogenous_aggregate(LLVMContextRef c, LLVMType type, LLVMType *base_type_, unsigned *member_count_);

	// 	LB_ABI_INFO(abi_info) {
	// 		lbFunctionType *ft = gb_alloc_item(heap_allocator(), lbFunctionType);
	// 		f.ctx = c;
	// 		f.result = compute_return_type(c, return_type, return_is_defined);
	// 		ft -> args = compute_arg_types(c, arg_types, arg_count);
	// 		f.calling_convention = calling_convention;
	// 		return ft;
	// 	}

	// 	bool is_register(LLVMType type) {
	// 		LLVMTypeKind kind = LLVMGetTypeKind(type);
	// 		switch (kind) {
	// 		LLVMIntegerTypeKind =>
	// 		LLVMFloatTypeKind =>
	// 		LLVMDoubleTypeKind =>
	// 		LLVMPointerTypeKind =>
	// 			return true;
	// 		}
	// 		return false;
	// 	}

	// 	lbArgType non_struct(LLVMContextRef c, LLVMType type) {
	// 		LLVMAttributeRef attr = nullptr;
	// 		LLVMType i1 = LLVMInt1TypeInContext(c);
	// 		if (type == i1) {
	// 			attr = lb_create_enum_attribute(c, "zeroext", true);
	// 		}
	// 		return Arg::direct(type, nullptr, nullptr, attr);
	// 	}

	// 	bool is_homogenous_array(LLVMContextRef c, LLVMType type, LLVMType *base_type_, unsigned *member_count_) {
	// 		GB_ASSERT(lb_is_type_kind(type, LLVMArrayTypeKind));
	// 		unsigned len = LLVMGetArrayLength(type);
	// 		if (len == 0) {
	// 			return false;
	// 		}
	// 		LLVMType elem = LLVMGetElementType(type);
	// 		LLVMType base_type = nullptr;
	// 		unsigned member_count = 0;
	// 		if (is_homogenous_aggregate(c, elem, &base_type, &member_count)) {
	// 			if (base_type_) *base_type_ = base_type;
	// 			if (member_count_) *member_count_ = member_count * len;
	// 			return true;

	// 		}
	// 		return false;
	// 	}
	// 	bool is_homogenous_struct(LLVMContextRef c, LLVMType type, LLVMType *base_type_, unsigned *member_count_) {
	// 		GB_ASSERT(lb_is_type_kind(type, LLVMStructTypeKind));
	// 		unsigned elem_count = LLVMCountStructElementTypes(type);
	// 		if (elem_count == 0) {
	// 			return false;
	// 		}
	// 		LLVMType base_type = nullptr;
	// 		unsigned member_count = 0;

	// 		for (unsigned i = 0; i < elem_count; i += 1) {
	// 			LLVMType field_type = nullptr;
	// 			unsigned field_member_count = 0;

	// 			LLVMType elem = LLVMStructGetTypeAtIndex(type, i);
	// 			if (!is_homogenous_aggregate(c, elem, &field_type, &field_member_count)) {
	// 				return false;
	// 			}

	// 			if (base_type == nullptr) {
	// 				base_type = field_type;
	// 				member_count = field_member_count;
	// 			} else {
	// 				if (base_type != field_type) {
	// 					return false;
	// 				}
	// 				member_count += field_member_count;
	// 			}
	// 		}

	// 		if (base_type == nullptr) {
	// 			return false;
	// 		}

	// 		if (size_of(type) == size_of(base_type) * member_count) {
	// 			if (base_type_) *base_type_ = base_type;
	// 			if (member_count_) *member_count_ = member_count;
	// 			return true;
	// 		}

	// 		return false;
	// 	}


	// 	bool is_homogenous_aggregate(LLVMContextRef c, LLVMType type, LLVMType *base_type_, unsigned *member_count_) {
	// 		LLVMTypeKind kind = LLVMGetTypeKind(type);
	// 		switch (kind) {
	// 		LLVMFloatTypeKind =>
	// 		LLVMDoubleTypeKind =>
	// 			if (base_type_) *base_type_ = type;
	// 			if (member_count_) *member_count_ = 1;
	// 			return true;
	// 		LLVMArrayTypeKind =>
	// 			return is_homogenous_array(c, type, base_type_, member_count_);
	// 		LLVMStructTypeKind =>
	// 			return is_homogenous_struct(c, type, base_type_, member_count_);
	// 		}
	// 		return false;
	// 	}

	// 	lbArgType compute_return_type(LLVMContextRef c, LLVMType type, bool return_is_defined) {
	// 		LLVMType homo_base_type = {};
	// 		unsigned homo_member_count = 0;

	// 		if (!return_is_defined) {
	// 			return Arg::direct(LLVMVoidTypeInContext(c));
	// 		} else if (is_register(type)) {
	// 			return non_struct(c, type);
	// 		} else if (is_homogenous_aggregate(c, type, &homo_base_type, &homo_member_count)) {
	// 			return Arg::direct(type, LLVMArrayType(homo_base_type, homo_member_count), nullptr, nullptr);
	// 		} else {
	// 			i64 size = size_of(type);
	// 			if (size <= 16) {
	// 				LLVMType cast_type = nullptr;
	// 				if (size <= 1) {
	// 					cast_type = LLVMIntTypeInContext(c, 8);
	// 				} else if (size <= 2) {
	// 					cast_type = LLVMIntTypeInContext(c, 16);
	// 				} else if (size <= 4) {
	// 					cast_type = LLVMIntTypeInContext(c, 32);
	// 				} else if (size <= 8) {
	// 					cast_type = LLVMIntTypeInContext(c, 64);
	// 				} else {
	// 					unsigned count = cast(unsigned)((size+7)/8);
	// 					cast_type = LLVMArrayType(LLVMIntTypeInContext(c, 64), count);
	// 				}
	// 				return Arg::direct(type, cast_type, nullptr, nullptr);
	// 			} else {
	// 				LLVMAttributeRef attr = lb_create_enum_attribute(c, "sret", true);
	// 				return Arg::indirect(type, attr);
	// 			}
	// 		}
	// 	}

	// 	Array<lbArgType> compute_arg_types(LLVMContextRef c, LLVMType *arg_types, unsigned arg_count) {
	// 		let args = array_make<lbArgType>(heap_allocator(), arg_count);

	// 		for (unsigned i = 0; i < arg_count; i += 1) {
	// 			LLVMType type = arg_types[i];

	// 			LLVMType homo_base_type = {};
	// 			unsigned homo_member_count = 0;

	// 			if (is_register(type)) {
	// 				args[i] = non_struct(c, type);
	// 			} else if (is_homogenous_aggregate(c, type, &homo_base_type, &homo_member_count)) {
	// 				args[i] = Arg::direct(type, LLVMArrayType(homo_base_type, homo_member_count), nullptr, nullptr);
	// 			} else {
	// 				i64 size = size_of(type);
	// 				if (size <= 16) {
	// 					LLVMType cast_type = nullptr;
	// 					if (size <= 1) {
	// 						cast_type = LLVMIntTypeInContext(c, 8);
	// 					} else if (size <= 2) {
	// 						cast_type = LLVMIntTypeInContext(c, 16);
	// 					} else if (size <= 4) {
	// 						cast_type = LLVMIntTypeInContext(c, 32);
	// 					} else if (size <= 8) {
	// 						cast_type = LLVMIntTypeInContext(c, 64);
	// 					} else {
	// 						unsigned count = cast(unsigned)((size+7)/8);
	// 						cast_type = LLVMArrayType(LLVMIntTypeInContext(c, 64), count);
	// 					}
	// 					args[i] = Arg::direct(type, cast_type, nullptr, nullptr);
	// 				} else {
	// 					args[i] = Arg::indirect(type, nullptr);
	// 				}
	// 			}
	// 		}
	// 		return args;
	// 	}
	// }


	// LB_ABI_INFO(lb_get_abi_info) {
	// 	switch (calling_convention) {
	// 	ProcCC_None =>
	// 	ProcCC_InlineAsm =>
	// 		{
	// 			lbFunctionType *ft = gb_alloc_item(heap_allocator(), lbFunctionType);
	// 			f.ctx = c;
	// 			f.args = array_make<lbArgType>(heap_allocator(), arg_count);
	// 			for (unsigned i = 0; i < arg_count; i += 1) {
	// 				f.args[i] = Arg::direct(arg_types[i]);
	// 			}
	// 			if (return_is_defined) {
	// 				f.result = Arg::direct(return_type);
	// 			} else {
	// 				f.result = Arg::direct(LLVMVoidTypeInContext(c));
	// 			}
	// 			f.calling_convention = calling_convention;
	// 			return ft;
	// 		}
	// 	}

	// 	if (build_context.metrics.arch == TargetArch_amd64) {
	// 		if (build_context.metrics.os == TargetOs_windows) {
	// 			return lbAbiAmd64Win64::abi_info(c, arg_types, arg_count, return_type, return_is_defined, calling_convention);
	// 		} else {
	// 			return lbAbiAmd64SysV::abi_info(c, arg_types, arg_count, return_type, return_is_defined, calling_convention);
	// 		}
	// 	} else if (build_context.metrics.arch == TargetArch_386) {
	// 		return lbAbi386::abi_info(c, arg_types, arg_count, return_type, return_is_defined, calling_convention);
	// 	} else if (build_context.metrics.arch == TargetArch_arm64) {
	// 		return lbAbiArm64::abi_info(c, arg_types, arg_count, return_type, return_is_defined, calling_convention);
	// 	} else if (build_context.metrics.arch == TargetArch_wasm32) {
	// 		return lbAbi386::abi_info(c, arg_types, arg_count, return_type, return_is_defined, calling_convention);
	// 	}
	// 	GB_PANIC("Unsupported ABI");
	// 	return {};
	// }
*/