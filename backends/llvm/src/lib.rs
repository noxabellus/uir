#![allow(non_upper_case_globals, dead_code)]

use std::{cell::{Ref, RefCell, RefMut}, collections::HashMap, ops};


#[macro_use]
pub(crate) mod wrapper;
pub(crate) mod abi;

use abi::{Abi, ArgAttr, ArgKind};

use uir_core::{ir::*, support::{slotmap::KeyData, stack::Stack, utils::RefAndThen}, ty::*};

use wrapper::*;


#[derive(Default)]
pub struct LLVMMutableState {
	pub types: HashMap<TyKey, LLVMType>,
	pub globals: HashMap<GlobalKey, LLVMValue>,
	pub functions: HashMap<FunctionKey, LLVMValue>,
	pub target_signature_types: HashMap<LLVMType, abi::Function>,
	pub stack: Stack<StackVal>,
	pub active_fn: Option<(LLVMValue, FunctionKey)>,
	pub active_block: Option<(LLVMBlock, BlockKey)>,
}

#[derive(Default)]
pub struct LLVMFunctionState {
	pub params: HashMap<ParamKey, LLVMValue>,
	pub locals: HashMap<LocalKey, LLVMValue>,
	pub blocks: HashMap<BlockKey, LLVMBlock>,
	pub sret  : Option<LLVMValue>,
}

pub struct LLVMBackend {
	pub ctx: RefCell<Context>,

	pub abi: Box<dyn Abi>,
	pub ll: LLVM,

	pub state: RefCell<LLVMMutableState>,
	pub function_state: RefCell<Option<LLVMFunctionState>>,
}

impl ops::Deref for LLVMBackend {
	type Target = LLVM;
	fn deref (&self) -> &LLVM { &self.ll }
}

impl ops::DerefMut for LLVMBackend {
	fn deref_mut (&mut self) -> &mut LLVM { &mut self.ll }
}

pub struct StackVal {
	pub llvalue: LLVMValue,
	pub lltype: LLVMType,
	pub ir_idx: Option<usize>,
}

impl StackVal {
	pub fn new (llvalue: LLVMValue, lltype: LLVMType, ir_idx: Option<usize>) -> Self {
		Self { llvalue, lltype, ir_idx }
	}

	pub fn implicit (llvalue: LLVMValue, lltype: LLVMType) -> Self {
		Self { llvalue, lltype, ir_idx: None }
	}

	pub fn source (llvalue: LLVMValue, lltype: LLVMType, ir_idx: usize) -> Self {
		Self { llvalue, lltype, ir_idx: Some(ir_idx) }
	}
}

impl LLVMBackend {
	pub fn new (ctx: Context) -> Option<Self> {
		let abi = abi::get_abi(ctx.target.as_ref())?;

		let ll = LLVM::new(llvm_str!("UIR_MODULE"));

		let state = RefCell::default();
		let function_state = RefCell::default();

		let ctx = RefCell::new(ctx);

		Some(Self {
			abi,
			ctx,
			ll,
			state,
			function_state,
		})
	}

	pub fn ctx (&self) -> Ref<Context> {
		self.ctx.borrow()
	}

	pub fn ctx_mut (&self) -> RefMut<Context> {
		self.ctx.borrow_mut()
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

	pub fn target_signature_type_map (&self) -> Ref<HashMap<LLVMType, abi::Function>> {
		Ref::map(self.state.borrow(), |state| &state.target_signature_types)
	}

	pub fn target_signature_type_map_mut (&self) -> RefMut<HashMap<LLVMType, abi::Function>> {
		RefMut::map(self.state.borrow_mut(), |state| &mut state.target_signature_types)
	}

	pub fn stack (&self) -> Ref<Stack<StackVal>> {
		Ref::map(self.state.borrow(), |state| &state.stack)
	}

	pub fn stack_mut (&self) -> RefMut<Stack<StackVal>> {
		RefMut::map(self.state.borrow_mut(), |state| &mut state.stack)
	}

	pub fn active_fn (&self) -> Option<(LLVMValue, FunctionKey)> {
		self.state.borrow().active_fn
	}

	pub fn set_active_fn (&self, xfn: (LLVMValue, FunctionKey)) -> Option<(LLVMValue, FunctionKey)> {
		self.state.borrow_mut().active_fn.replace(xfn)
	}

	pub fn clear_active_fn (&self) -> Option<(LLVMValue, FunctionKey)> {
		self.state.borrow_mut().active_fn.take()
	}

	pub fn active_block (&self) -> Option<(LLVMBlock, BlockKey)> {
		self.state.borrow().active_block
	}

	pub fn set_active_block (&self, xblk: (LLVMBlock, BlockKey)) -> Option<(LLVMBlock, BlockKey)> {
		self.state.borrow_mut().active_block.replace(xblk)
	}

	pub fn clear_active_block (&self) -> Option<(LLVMBlock, BlockKey)> {
		self.state.borrow_mut().active_block.take()
	}

	pub fn ir (&self, ir_idx: usize) -> Option<Ref<Ir>> {
		let (_, active_fn_key) = self.active_fn()?;
		let (_, active_block_key) = self.active_block()?;

		self
			.ctx()
			.and_then(|ctx|
				ctx
					.functions.get(active_fn_key)
					.expect("valid active function")

					.block_data.get(active_block_key)
					.expect("valid active block")

					.ir.get(ir_idx)
			)
	}


	pub fn prim_ty (&self, prim: PrimitiveTy) -> LLVMType {
		use PrimitiveTy::*;

		match prim {
			Bool
			=> LLVMType::int1(self.ll.ctx),

			| SInt8 | SInt16 | SInt32 | SInt64 | SInt128
			| UInt8 | UInt16 | UInt32 | UInt64 | UInt128
			=> LLVMType::int(self.ll.ctx, (prim.size() * 8) as _),

			Real32
			=> LLVMType::float(self.ll.ctx),

			Real64
			=> LLVMType::double(self.ll.ctx),
		}
	}

	pub fn emit_ty (&self, ty_key: TyKey) -> LLVMType {
		if let Some(llty) = self.type_map().get(&ty_key) {
			return *llty
		}

		let ty = self.ctx().and_then(|ctx| ctx.tys.get(ty_key)).expect("valid ty key");

		let llty = {
			use TyData::*;

			match &ty.data {
				Void => LLVMType::void(self.ll.ctx),

				Block => LLVMType::label(self.ll.ctx),

				Primitive(prim) => self.prim_ty(*prim),

				Pointer { target_ty } => self.emit_ty(*target_ty).as_pointer(0),

				Array { length, element_ty } => self.emit_ty(*element_ty).as_array(*length as _),

				Structure { field_tys } => {
					let llname = if let Some(name) = ty.name.as_ref() {
						LLVMString::from(name)
					} else {
						LLVMString::from(format!("$s({})", self.ctx().tys.get_index(ty_key).unwrap()))
					};

					let llty = LLVMType::named_empty_structure(self.ll.ctx, llname);

					self.type_map_mut().insert(ty_key, llty);

					let elem_types = field_tys.iter().map(|&ty_key| self.emit_ty(ty_key)).collect::<Vec<_>>();
					llty.structure_set_body(elem_types.as_slice(), false);

					llty
				}

				Function { parameter_tys, result_ty } => {
					let param_types = parameter_tys.iter().map(|&ty_key| self.emit_ty(ty_key)).collect::<Vec<_>>();
					let result_type = result_ty.map(|ty_key| self.emit_ty(ty_key));
					LLVMType::function(&param_types, result_type.unwrap_or_else(|| LLVMType::void(self.ll.ctx)), false)
				}
			}
		};

		self.type_map_mut().insert(ty_key, llty);

		llty
	}

	pub fn abi_info(&self, lltype: LLVMType) -> Ref<abi::Function> {
		assert!(lltype.kind() == LLVMFunctionTypeKind, "abi_info called on non-functional type {}", lltype);

		let existing = self.target_signature_type_map().and_then(|map| map.get(&lltype));
		if let Some(existing) = existing { return existing }

		let parameter_tys = lltype.get_param_types();
		let return_ty = lltype.get_return_type();

		let abi = self.abi.get_info(self.ll.ctx, &parameter_tys, return_ty);
		self.target_signature_type_map_mut().insert(lltype, abi);

		Ref::map(self.target_signature_type_map(), |map| map.get(&lltype).unwrap())
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

	pub fn generate_id<K: Into<KeyData>> (prefix: &str, k: K) -> LLVMString {
		LLVMString::from(format!("${}({})", prefix, u64::from(k.into())))
	}

	pub fn emit_global (&self, global_key: GlobalKey) -> LLVMValue {
		if let Some(llglobal) = self.global_map_mut().get(&global_key) {
			return *llglobal
		}

		let global = self.ctx().and_then(|ctx| ctx.globals.get(global_key)).expect("valid global key");

		let llty = self.emit_ty(global.ty);

		let llname = if let Some(name) = global.name.as_ref() {
			LLVMString::from(name)
		} else {
			Self::generate_id("g", global_key)
		};

		let llglobal = LLVMValue::create_global(self.module, llty, llname);

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

		let function = self.ctx().and_then(|ctx| ctx.functions.get(function_key)).expect("valid function key");

		let llty = self.emit_ty(function.ty);
		let abi = self.abi_info(llty);

		let llname = if let Some(name) = function.name.as_ref() {
			LLVMString::from(name)
		} else {
			Self::generate_id("f", function_key)
		};

		LLVMValue::create_function(self.module, abi.lltype, llname)
	}


	pub fn emit_entry (&self) -> LLVMBlock {
		let function_key = self.active_fn().expect("active function for emit_entry").1;
		let function = self.ctx().and_then(|ctx| ctx.functions.get(function_key)).expect("valid function key");
		let llfunc = *self.function_map().get(&function_key).expect("initialized function");
		debug_assert_eq!(self.active_fn().map(|x| x.0), Some(llfunc));

		let lltype = self.emit_ty(function.ty);
		let abi = self.abi_info(lltype);

		let entry = self.ll.append_basic_block(llfunc, Some(llvm_str!("entry")));
		self.ll.position_at_end(entry);

		let mut function_state = LLVMFunctionState::default();

		let mut llparams = llfunc.get_params().into_iter();


		if abi.result.kind == ArgKind::Indirect {
			function_state.sret = Some(llparams.next().unwrap());
		}


	 	for (abi_arg, &param_key) in abi.args.iter().zip(function.param_order.iter()) {
			let param = match abi_arg.kind {
				ArgKind::Direct => {
					let llvalue = if let Some(ArgAttr::ZExt) = abi_arg.attribute {
						// TODO: this is currently only handling i8 -> i1
						let int1 = LLVMType::int1(self.ll.ctx);
						debug_assert!(abi_arg.base_type == int1);

						self.ll.trunc_or_bitcast(llparams.next().unwrap(), int1, None::<LLVMString>) // TODO: name truncs
					} else if abi_arg.cast_types.is_empty() {
						llparams.next().unwrap()
					} else {
						let mut agg = None;
						for i in 0..abi_arg.cast_types.len() as u32 {
							let llparam = llparams.next().unwrap();

							agg = Some(self.ll.insert_value(agg, llparam, i, None::<LLVMString>)); // TODO: name inserts
						}

						self.ll.trunc_or_bitcast(agg.unwrap(), abi_arg.base_type, None::<LLVMString>) // TODO: name casts
					};

					let param = self.ll.alloca(abi_arg.base_type, None::<LLVMString>); // TODO: name params
					self.ll.store(llvalue, param);

					param
				},

				ArgKind::Indirect => {
					llparams.next().unwrap()
				}
			};

			function_state.params.insert(param_key, param);
		}


		for (&local_key, local) in function.locals.iter() {
			let lltype = self.emit_ty(local.ty);
			function_state.locals.insert(local_key, self.alloca(lltype, None::<LLVMString>)); // TODO name locals
		}


		entry
	}


	pub fn emit_return (&self) -> LLVMValue {
		let function_key = self.active_fn().expect("active function for emit_return").1;
		let function = self.ctx().and_then(|ctx| ctx.functions.get(function_key)).expect("valid function key");
		let llfunc = *self.function_map().get(&function_key).expect("initialized function");
		debug_assert_eq!(self.active_fn().map(|x| x.0), Some(llfunc));

		let lltype = self.emit_ty(function.ty);
		let abi = self.abi_info(lltype);

		let function_state = self.function_state.borrow().and_then(|f| f.as_ref()).unwrap();

		match abi.result.kind {
			ArgKind::Direct => {
				if abi.result.base_type == LLVMType::void(self.ll.ctx) {
					self.ll.ret_void()
				} else {
					let StackVal { llvalue: base_llvalue, .. } = self.stack_mut().pop().expect("return value on stack");

					let llvalue = if abi.result.attribute == Some(ArgAttr::ZExt) {
						// TODO: this is currently only handling i1 -> i8
						self.ll.zext_or_bitcast(base_llvalue, LLVMType::int8(self.ll.ctx), None::<LLVMString>) // TODO: name zext
					} else if abi.result.cast_types.is_empty() {
						base_llvalue
					} else {
						let arg_struct = LLVMType::anonymous_structure(self.ll.ctx, &abi.result.cast_types, false);
						self.ll.zext_or_bitcast(base_llvalue, arg_struct, None::<LLVMString>) // TODO: name cast
					};

					self.ll.ret(llvalue)
				}
			}

			ArgKind::Indirect => {
				let StackVal { llvalue: base_llvalue, .. } = self.stack_mut().pop().expect("return value on stack");
				self.store(base_llvalue, function_state.sret.unwrap());

				self.ll.ret_void()
			}
		}
	}



	fn emit_call (&self) -> LLVMValue {
		let StackVal { llvalue, lltype, ir_idx } = self.stack_mut().pop().expect("function on stack");

		assert!(lltype.is_function_kind());

		let abi = self.abi_info(lltype);
		debug_assert_eq!(lltype, abi.lltype);
		debug_assert_eq!(lltype.count_param_types() as usize, abi.args.len());



		let mut llargs: Vec<LLVMValue> = vec![];

		for abi_arg in abi.args.iter().rev() {
			let StackVal { lltype: base_lltype, llvalue: base_llvalue, ir_idx: _ }
				= self.stack_mut().pop().expect("parameter for call");

			assert_eq!(base_lltype, abi_arg.base_type);

			let value = match abi_arg.kind {
				ArgKind::Direct => {
					if let Some(ArgAttr::ZExt) = abi_arg.attribute {
						// TODO: this is currently only handling i1 -> i8
						debug_assert!(abi_arg.base_type == LLVMType::int1(self.ll.ctx));

						self.ll.zext_or_bitcast(base_llvalue, LLVMType::int8(self.ll.ctx), None::<LLVMString>) // TODO: name zexts
					} else if abi_arg.cast_types.is_empty() {
						base_llvalue
					} else {
						let arg_struct = LLVMType::anonymous_structure(self.ll.ctx, &abi_arg.cast_types, false);

						self.ll.zext_or_bitcast(base_llvalue, arg_struct, None::<LLVMString>) // TODO: name destructure casts
					}
				}

				ArgKind::Indirect => {
					let llslot = self.ll.alloca(abi_arg.base_type.as_pointer(0), None::<LLVMString>); // TODO: name slots

					self.ll.store(llslot, base_llvalue)
				}
			};

			if abi_arg.cast_types.len() > 1 {
				for i in 0..abi_arg.cast_types.len() as u32 {
					llargs.push(self.ll.extract_value(value, i, None::<LLVMString>))
				}
			} else {
				llargs.push(value);
			}
		}



		if abi.result.kind == ArgKind::Indirect {
			let name =
				ir_idx
					.and_then(|i| self.ir(i).and_then(|j| j.and_then(|k| k.name.as_ref())))
					.map(|name| format!("$alloca(sret {})", name))
					.unwrap_or_else(|| format!("$alloca(sret anon {})", abi.result.base_type));

			let llvalue = self.ll.alloca(abi.result.base_type, Some(name));

			llargs.push(llvalue);
		}


		let name = ir_idx.and_then(|i| self.ir(i)).and_then(|j| j.name.clone());

		llargs.reverse();
		let result = self.ll.call(abi.lltype, llvalue, llargs.as_slice(), name);

		if abi.result.base_type.is_void_kind() { return result }

		let (llvalue, lltype) = match abi.result.kind {
			ArgKind::Indirect => {
				let load = self.ll.load(result, None::<LLVMString>); // TODO: name sret loads
				(load, abi.result.base_type)
			}

			ArgKind::Direct => {
				(if abi.result.cast_types.is_empty() {
					result
				} else {
					self.ll.trunc_or_bitcast(result, abi.result.base_type, None::<LLVMString>) // TODO: name trunc rets
				}, abi.result.base_type)
			}
		};

		self.stack_mut().push(StackVal::new(llvalue, lltype, ir_idx));


		llvalue
	}
}




#[cfg(test)]
mod llvm_tests {

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

				let backend = LLVMBackend::new(ctx).unwrap();

				let ll_direct_function_ty = backend.emit_ty(direct_function_ty);
				let ll_struct_function_ty = backend.emit_ty(struct_function_ty);

				let direct_function_abi = backend.abi_info(ll_direct_function_ty);
				let struct_function_abi = backend.abi_info(ll_struct_function_ty);

				let ll_direct_function = LLVMValue::create_function(backend.module, ll_direct_function_ty, concat!("fn_direct_", stringify!($name)));
				let ll_struct_function = LLVMValue::create_function(backend.module, ll_struct_function_ty, concat!("fn_struct_", stringify!($name)));

				direct_function_abi.apply_attributes(backend.ll.ctx, ll_direct_function);
				struct_function_abi.apply_attributes(backend.ll.ctx, ll_struct_function);

				let ll_mod = llvm_from_c(build_c_abi_str!($name ($( $field_name : $field_ty ),*)));

				let truth_ll_direct_function = LLVMValue::get_function(ll_mod, concat!("fn_direct_", stringify!($name)));
				let truth_ll_struct_function = LLVMValue::get_function(ll_mod, concat!("fn_struct_", stringify!($name)));

				let truth_ll_direct_function_ty = LLVMType::of(truth_ll_direct_function);
				let truth_ll_struct_function_ty = LLVMType::of(truth_ll_struct_function);

				let truth_ctx = unsafe { LLVMGetModuleContext(ll_mod) };

				println!("direct abi: {:#?}", direct_function_abi);
				println!("struct abi: {:#?}", struct_function_abi);


				println!("got: {:#?}\nexpected: {:#?}", ll_direct_function, truth_ll_direct_function);
				println!();
				println!("got: {:#?}\nexpected: {:#?}", ll_struct_function, truth_ll_struct_function);

				println!("got: {}\nexpected: {}", ll_direct_function_ty, truth_ll_direct_function_ty);
				println!();
				println!("got: {}\nexpected: {}", ll_struct_function_ty, truth_ll_struct_function_ty);

				assert!(llvm_ty_eq(truth_ctx, truth_ll_direct_function_ty, backend.ll.ctx, ll_direct_function_ty));
				assert!(llvm_ty_eq(truth_ctx, truth_ll_struct_function_ty, backend.ll.ctx, ll_struct_function_ty));
			} )*
		} };
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