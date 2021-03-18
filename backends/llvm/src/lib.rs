#![allow(non_upper_case_globals, dead_code)]

use std::{cell::{Ref, RefCell, RefMut}, collections::HashMap, ops};


#[macro_use]
pub(crate) mod wrapper;
pub(crate) mod abi;

use abi::{Abi, ArgAttr, ArgKind};

use uir_core::{ir::*, support::{slotmap::KeyData, stack::Stack, utils::{RefAndThen}}, ty::*};

use wrapper::*;


#[derive(Default)]
pub struct LLVMMutableState {
	pub types: HashMap<TyKey, LLVMType>,
	pub globals: HashMap<GlobalKey, LLVMValue>,
	pub functions: HashMap<FunctionKey, LLVMValue>,
	pub target_signature_types: HashMap<LLVMType, abi::Function>,
}

pub struct LLVMFunctionState<'c> {
	pub func: &'c Function,
	pub llfunc: LLVMValue,
	pub fn_key: FunctionKey,
	pub llblock: LLVMBlock,
	pub block_key: BlockKey,
	pub params: HashMap<ParamKey, LLVMValue>,
	pub locals: HashMap<LocalKey, LLVMValue>,
	pub blocks: HashMap<BlockKey, LLVMBlock>,
	pub stack : Stack<StackVal>,
	pub sret  : Option<LLVMValue>,
}

impl<'c> LLVMFunctionState<'c> {
	pub fn new (llfunc: LLVMValue, fn_key: FunctionKey, func: &'c Function) -> Self {
		Self {
			llfunc,
			fn_key,
			func,
			llblock: LLVMBlock::default(),
			block_key: BlockKey::default(),
			params: HashMap::default(),
			locals: HashMap::default(),
			blocks: HashMap::default(),
			stack: Stack::default(),
			sret: None,
		}
	}
}

pub struct LLVMBackend {
	pub ctx: RefCell<Context>,

	pub abi: Box<dyn Abi>,
	pub ll: LLVM,

	pub state: RefCell<LLVMMutableState>,
}

impl ops::Deref for LLVMBackend {
	type Target = LLVM;
	fn deref (&self) -> &LLVM { &self.ll }
}

impl ops::DerefMut for LLVMBackend {
	fn deref_mut (&mut self) -> &mut LLVM { &mut self.ll }
}

#[derive(Clone, Copy)]
pub struct StackVal {
	pub llvalue: LLVMValue,
	pub lltype: LLVMType,
	pub ir_idx: Option<usize>,
	pub ty_key: TyKey,
}

impl StackVal {
	pub fn new (llvalue: LLVMValue, lltype: LLVMType, ir_idx: Option<usize>, ty_key: TyKey) -> Self {
		Self { llvalue, lltype, ir_idx, ty_key }
	}

	pub fn implicit (llvalue: LLVMValue, lltype: LLVMType, ty_key: TyKey) -> Self {
		Self { llvalue, lltype, ir_idx: None, ty_key }
	}

	pub fn source (llvalue: LLVMValue, lltype: LLVMType, ir_idx: usize, ty_key: TyKey) -> Self {
		Self { llvalue, lltype, ir_idx: Some(ir_idx), ty_key }
	}
}

impl LLVMBackend {
	pub fn new (ctx: Context) -> Option<Self> {
		let abi = abi::get_abi(ctx.target.as_ref())?;

		let ll = LLVM::new(llvm_str!("UIR_MODULE"));

		let state = RefCell::default();

		let ctx = RefCell::new(ctx);

		Some(Self {
			abi,
			ctx,
			ll,
			state,
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


	pub fn ir (&self, fstate: &mut LLVMFunctionState, ir_idx: usize) -> Option<Ref<Ir>> {

		self
			.ctx()
			.and_then(|ctx|
				ctx
					.functions.get(fstate.fn_key)
					.unwrap()

					.block_data.get(fstate.block_key)
					.unwrap()

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

		let ty = self.ctx().and_then(|ctx| ctx.tys.get(ty_key)).unwrap();

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


	pub fn emit_constant (&self, constant: &Constant) -> (LLVMValue, LLVMType) {
		use Constant::*;

		match constant {
			Null(ty_key) => { let ty = self.emit_ty(*ty_key); (LLVMValue::const_null(ty), ty) },

			Bool(val) => { let ty = self.prim_ty(PrimitiveTy::Bool); (LLVMValue::const_int(ty, *val as _), ty) },

			SInt8(val) => { let ty = self.prim_ty(PrimitiveTy::SInt8); (LLVMValue::const_int(ty, *val as _), ty) },
			SInt16(val) => { let ty = self.prim_ty(PrimitiveTy::SInt16); (LLVMValue::const_int(ty, *val as _), ty) },
			SInt32(val) => { let ty = self.prim_ty(PrimitiveTy::SInt32); (LLVMValue::const_int(ty, *val as _), ty) },
			SInt64(val) => { let ty = self.prim_ty(PrimitiveTy::SInt64); (LLVMValue::const_int(ty, *val as _), ty) },

			SInt128(val) => {
				let ty = self.prim_ty(PrimitiveTy::SInt128);
				(LLVMValue::const_int(
					ty,
					*val as _
				), ty)
			}

			UInt8(val) => { let ty = self.prim_ty(PrimitiveTy::UInt8); (LLVMValue::const_int(ty, *val as _), ty) },
			UInt16(val) => { let ty = self.prim_ty(PrimitiveTy::UInt16); (LLVMValue::const_int(ty, *val as _), ty) },
			UInt32(val) => { let ty = self.prim_ty(PrimitiveTy::UInt32); (LLVMValue::const_int(ty, *val as _), ty) },
			UInt64(val) => { let ty = self.prim_ty(PrimitiveTy::UInt64); (LLVMValue::const_int(ty, *val as _), ty) },

			UInt128(val) =>  {
				let ty = self.prim_ty(PrimitiveTy::UInt128);
				(LLVMValue::const_int(
					ty,
					*val
				), ty)
			}

			Real32(val) => { let ty = self.prim_ty(PrimitiveTy::Real32); (LLVMValue::const_real(ty, *val as _), ty) },
			Real64(val) => { let ty = self.prim_ty(PrimitiveTy::Real64); (LLVMValue::const_real(ty, *val), ty) },

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

		let global = self.ctx().and_then(|ctx| ctx.globals.get(global_key)).unwrap();

		let llty = self.emit_ty(global.ty);

		let llname = if let Some(name) = global.name.as_ref() {
			LLVMString::from(name)
		} else {
			Self::generate_id("g", global_key)
		};

		let llglobal = LLVMValue::create_global(self.module, llty, llname);

		if let Some(init_const) = global.init.as_ref() {
			let (llinit, llconst_ty) = self.emit_constant(init_const);
			assert_eq!(llty, llconst_ty);

			llglobal.set_global_initializer(llinit)
		}

		llglobal
	}


	pub fn emit_function_decl (&self, function_key: FunctionKey) -> LLVMValue {
		if let Some(llfunction) = self.function_map_mut().get(&function_key) {
			return *llfunction
		}

		let function = self.ctx().and_then(|ctx| ctx.functions.get(function_key)).unwrap();

		let llty = self.emit_ty(function.ty);
		let abi = self.abi_info(llty);

		let llname = if let Some(name) = function.name.as_ref() {
			LLVMString::from(name)
		} else {
			Self::generate_id("f", function_key)
		};

		LLVMValue::create_function(self.module, abi.lltype, llname)
	}


	pub fn ir_ty (&self, fstate: &mut LLVMFunctionState, ir_idx: usize) -> TyKey {
		fstate.func.ty_map.get(fstate.block_key, ir_idx)
	}

	pub fn emit_function_body (&self, function_key: FunctionKey) -> LLVMValue {
		let func = self.ctx().and_then(|ctx| ctx.functions.get(function_key)).unwrap();

		let llfunc = self.emit_function_decl(function_key);

		let mut fstate = LLVMFunctionState::new(llfunc, function_key, &func);

		let _entry = self.emit_entry(&mut fstate);

		for &block_key in func.block_order.iter() {
			let block = func.block_data.get(block_key).unwrap();
			let name = block.name.as_deref().unwrap_or("$block");

			let block = self.ll.append_basic_block(llfunc, Some(name));

			fstate.blocks.insert(block_key, block);
		}

		let user_entry = *func.block_order.first().unwrap();
		let lluser_entry = *fstate.blocks.get(&user_entry).unwrap();

		self.ll.branch(lluser_entry);


		let mut block_in_vals = HashMap::<BlockKey, Stack<StackVal>>::default();
		let mut block_out_vals = HashMap::<BlockKey, Stack<StackVal>>::default();
		for &block_key in func.block_order.iter() {
			let llblock = *fstate.blocks.get(&block_key).unwrap();

			fstate.llblock = llblock;
			fstate.block_key = block_key;

			let (in_vals, out_vals) = self.emit_block_body(&mut fstate);
			block_in_vals.insert(block_key, in_vals);
			block_out_vals.insert(block_key, out_vals);
		}

		for &block_key in func.block_order.iter() {
			self.emit_block_terminator(&mut fstate, &block_in_vals, block_out_vals.remove(&block_key).unwrap())
		}

		llfunc
	}

	pub fn emit_block_body (&self, fstate: &mut LLVMFunctionState) -> (Stack<StackVal>, Stack<StackVal>) {
		let block = fstate.func.block_data.get(fstate.block_key).unwrap();
		self.position_at_end(fstate.llblock);

		let mut iter = block.ir.iter().enumerate().peekable();

		let mut in_vals = Stack::default();

		while let Some((ir_idx, ir)) = iter.next() {
			match &ir.data {
				x if x.is_terminator() => unreachable!(),

				IrData::Phi(ty_key) => {
					let name = ir.name.as_deref().unwrap_or("phi");
					let llty = self.emit_ty(*ty_key);
					let phi = self.ll.phi(llty, Some(name));
					let ty_key = self.ir_ty(fstate, ir_idx);

					let stack_val = StackVal::source(phi, llty, ir_idx, ty_key);

					in_vals.push(stack_val);
					fstate.stack.push(stack_val)
				}


				IrData::Constant(constant) => {
					let (llconst, llconst_ty) = self.emit_constant(constant);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llconst, llconst_ty, ir_idx, ty_key))
				}


				IrData::BuildAggregate(_ty_key, _aggregate_data) => { todo!() }


				IrData::GlobalRef(gkey) => {
					let global = self.ctx().and_then(|ctx| ctx.globals.get(*gkey)).unwrap();
					let llg = self.emit_global(*gkey);
					let llty = self.emit_ty(global.ty).as_pointer(0);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llg, llty, ir_idx, ty_key))
				}

				IrData::FunctionRef(fkey) => {
					let function = self.ctx().and_then(|ctx| ctx.functions.get(*fkey)).unwrap();
					let llf = self.emit_function_decl(*fkey);
					let llty = self.emit_ty(function.ty).as_pointer(0);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llf, llty, ir_idx, ty_key))
				}

				IrData::BlockRef(bkey) => {
					let llbb = *fstate.blocks.get(bkey).unwrap();
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llbb.as_value(), LLVMType::label(self.ll.ctx), ir_idx, ty_key))
				}

				IrData::ParamRef(pkey) => {
					let llparam = *fstate.params.get(pkey).unwrap();
					let llty = self.emit_ty(fstate.func.param_data.get(*pkey).unwrap().ty);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llparam, llty, ir_idx, ty_key))
				}

				IrData::LocalRef(lkey) => {
					let llvar = *fstate.locals.get(lkey).unwrap();
					let llty = self.emit_ty(fstate.func.locals.get(*lkey).unwrap().ty);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llvar, llty, ir_idx, ty_key))
				}


				IrData::BinaryOp(bin_op) => {
					let a = fstate.stack.pop().unwrap();
					let b = fstate.stack.pop().unwrap();

					let ty = self.ctx().and_then(|ctx| ctx.tys.get(a.ty_key)).unwrap();

					assert_eq!(a.lltype, b.lltype);

					let (llvalue, lltype) = self.emit_bin_op(*bin_op, a, b, ty);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llvalue, lltype, ir_idx, ty_key))
				}

				IrData::UnaryOp(un_op) => {
					let e = fstate.stack.pop().unwrap();

					let ty = self.ctx().and_then(|ctx| ctx.tys.get(e.ty_key)).unwrap();

					let (llvalue, lltype) = self.emit_un_op(*un_op, e, ty);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llvalue, lltype, ir_idx, ty_key))
				}

				IrData::CastOp(cast_op, target_ty_key) => {
					let e = fstate.stack.pop().unwrap();

					let ty = self.ctx().and_then(|ctx| ctx.tys.get(e.ty_key)).unwrap();
					let target_ty = self.ctx().and_then(|ctx| ctx.tys.get(*target_ty_key)).unwrap();
					let lltype = self.emit_ty(*target_ty_key);

					let llvalue = self.emit_cast_op(*cast_op, e, ty, target_ty, lltype);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llvalue, lltype, ir_idx, ty_key))
				}

				IrData::Gep(num_indices) => {
					let ptr = fstate.stack.pop().unwrap();
					assert!(ptr.lltype.is_pointer_kind());

					let indices = (0..*num_indices).into_iter().map(|_| fstate.stack.pop().unwrap().llvalue).collect::<Vec<_>>();
					let ty_key = self.ir_ty(fstate, ir_idx);
					let llty = self.emit_ty(ty_key);
					let gep = self.ll.gep(llty, ptr.llvalue, &indices, None::<LLVMString>); // TODO: name geps
					fstate.stack.push(StackVal::source(gep, llty, ir_idx, ty_key))
				}

				IrData::Load => {
					let StackVal { lltype, llvalue, .. } = fstate.stack.pop().unwrap();
					assert!(lltype.is_pointer_kind());
					assert!(!lltype.get_element_type().is_function_kind()); // TODO: more robust unloadable type check?

					let load = self.ll.load(llvalue, None::<LLVMString>); // TODO: name loads
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(load, lltype, ir_idx, ty_key))
				}

				IrData::Store => {
					let StackVal { lltype: llptr_ty, llvalue: llptr, .. } = fstate.stack.pop().unwrap();
					let StackVal { lltype: llval_ty, llvalue: llval, .. } = fstate.stack.pop().unwrap();
					assert_eq!(llptr_ty.get_element_type(), llval_ty);

					self.ll.store(llval, llptr);
				}



				IrData::Call => {
					if let Some((llval, llty)) = self.emit_call(fstate) {
						let ty_key = self.ir_ty(fstate, ir_idx);
						fstate.stack.push(StackVal::source(llval, llty, ir_idx, ty_key))
					}
				}

				IrData::Duplicate => {
					let val = *fstate.stack.peek().unwrap();
					fstate.stack.push(val);
				}

				IrData::Discard => {
					fstate.stack.pop();
				}

				IrData::Swap => {
					let a = fstate.stack.pop().unwrap();
					let b = fstate.stack.pop().unwrap();
					fstate.stack.push(b);
					fstate.stack.push(a);
				}


				| IrData::Branch { .. }
				| IrData::CondBranch { .. }
				| IrData::Switch { .. }
				| IrData::ComputedBranch { .. }
				| IrData::Ret
				| IrData::Unreachable
				=> unreachable!()
			}

			if matches!(iter.peek(), Some((_, x)) if x.is_terminator()) {
				assert!(ir_idx == block.ir.len() - 1);
				return (in_vals, std::mem::take(&mut fstate.stack))
			}
		}

		unreachable!()
	}

	pub fn emit_block_terminator (&self, fstate: &mut LLVMFunctionState, in_val_map: &HashMap<BlockKey, Stack<StackVal>>, mut out_vals: Stack<StackVal>) {
		let block = fstate.func.block_data.get(fstate.block_key).unwrap();
		self.position_at_end(fstate.llblock);

		let term = block.ir.last().unwrap();

		let fixup_phis = |dest, out_vals: &Stack<StackVal>| {
			let in_vals = in_val_map.get(dest).unwrap();
			assert_eq!(out_vals.len(), in_vals.len());

			for (
				&StackVal { llvalue: llphi, lltype: llin_ty, .. },
				&StackVal { llvalue: llterm, lltype: llout_ty, .. },
			) in in_vals.as_slice().iter().zip(out_vals.iter()) {
				assert_eq!(llin_ty, llout_ty);

				llphi.add_incoming(&[llterm], &[fstate.llblock])
			}
		};

		match &term.data {
			IrData::Branch(dest) => {
				let lldest = *fstate.blocks.get(dest).unwrap();
				self.ll.branch(lldest);

				fixup_phis(dest, &out_vals);
			}

			IrData::CondBranch(a, b) => {
				let StackVal { llvalue, .. } = out_vals.pop().unwrap();

				let lla = *fstate.blocks.get(a).unwrap();
				let llb = *fstate.blocks.get(b).unwrap();
				self.ll.cond_branch(llvalue, lla, llb);

				fixup_phis(a, &out_vals);
				fixup_phis(b, &out_vals);
			}

			IrData::Switch(branches, default_block) => {
				let lldefault = *fstate.blocks.get(default_block).unwrap();
				let StackVal { llvalue, lltype, .. } = out_vals.pop().unwrap();
				let switch = self.ll.switch(llvalue, lldefault, branches.len() as u32);
				branches.iter().for_each(|(constant, block)| {
					let (llconst, llconst_ty) = self.emit_constant(constant);
					assert_eq!(llconst_ty, lltype);

					let llblock = *fstate.blocks.get(block).unwrap();

					switch.add_case(llconst, llblock);
					fixup_phis(block, &out_vals);
				});

				fixup_phis(default_block, &out_vals);
			}

			IrData::ComputedBranch(dests) => {
				let StackVal { llvalue, lltype, .. } = out_vals.pop().unwrap();

				assert!(lltype == LLVMType::label(self.ll.ctx));

				self.ll.indirect_branch(llvalue, dests.len() as u32);

				dests.iter().for_each(|dest| fixup_phis(dest, &out_vals));
			}

			IrData::Ret => {
				self.emit_return(fstate, out_vals);
			}

			IrData::Unreachable
			=> {
				assert!(out_vals.is_empty());
				self.ll.unreachable();
			}

			| IrData::Phi { .. }
			| IrData::Constant { .. }
			| IrData::BuildAggregate { .. }
			| IrData::GlobalRef { .. }
			| IrData::FunctionRef { .. }
			| IrData::BlockRef { .. }
			| IrData::ParamRef { .. }
			| IrData::LocalRef { .. }
			| IrData::BinaryOp { .. }
			| IrData::UnaryOp { .. }
			| IrData::CastOp { .. }
			| IrData::Gep { .. }
			| IrData::Load
			| IrData::Store
			| IrData::Call
			| IrData::Duplicate
			| IrData::Discard
			| IrData::Swap
			=> unreachable!()
		}
	}


	pub fn emit_entry (&self, fstate: &mut LLVMFunctionState) -> LLVMBlock {
		let lltype = self.emit_ty(fstate.func.ty);
		let abi = self.abi_info(lltype);

		let entry = self.ll.append_basic_block(fstate.llfunc, Some(llvm_str!("entry")));
		self.ll.position_at_end(entry);

		let mut llparams = fstate.llfunc.get_params().into_iter();


		if abi.result.kind == ArgKind::Indirect {
			fstate.sret = Some(llparams.next().unwrap());
		}


	 	for (abi_arg, &param_key) in abi.args.iter().zip(fstate.func.param_order.iter()) {
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

			fstate.params.insert(param_key, param);
		}


		for (&local_key, local) in fstate.func.locals.iter() {
			let lltype = self.emit_ty(local.ty);
			fstate.locals.insert(local_key, self.alloca(lltype, None::<LLVMString>)); // TODO name locals
		}


		entry
	}


	pub fn emit_return (&self, fstate: &mut LLVMFunctionState, mut stack: Stack<StackVal>) -> LLVMValue {
		let lltype = self.emit_ty(fstate.func.ty);
		let abi = self.abi_info(lltype);

		let val = match abi.result.kind {
			ArgKind::Direct => {
				if abi.result.base_type == LLVMType::void(self.ll.ctx) {
					self.ll.ret_void()
				} else {
					let StackVal { llvalue: base_llvalue, .. } = stack.pop().unwrap();

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
				let StackVal { llvalue: base_llvalue, .. } = fstate.stack.pop().unwrap();
				self.store(base_llvalue, fstate.sret.unwrap());

				self.ll.ret_void()
			}
		};

		assert!(stack.is_empty());

		val
	}



	fn emit_call (&self, fstate: &mut LLVMFunctionState) -> Option<(LLVMValue, LLVMType)> {
		let StackVal { llvalue, lltype, ir_idx, ty_key: _ } = fstate.stack.pop().unwrap();


		assert!(lltype.is_function_kind());

		let abi = self.abi_info(lltype);
		debug_assert_eq!(lltype, abi.lltype);
		debug_assert_eq!(lltype.count_param_types() as usize, abi.args.len());



		let mut llargs: Vec<LLVMValue> = vec![];

		for abi_arg in abi.args.iter().rev() {
			let StackVal { lltype: base_lltype, llvalue: base_llvalue, ir_idx: _, ty_key: _ }
				= fstate.stack.pop().unwrap();

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
					.and_then(|i| self.ir(fstate, i).and_then(|j| j.and_then(|k| k.name.as_ref())))
					.map(|name| format!("$alloca(sret {})", name))
					.unwrap_or_else(|| format!("$alloca(sret anon {})", abi.result.base_type));

			let llvalue = self.ll.alloca(abi.result.base_type, Some(name));

			llargs.push(llvalue);
		}


		let name = ir_idx.and_then(|i| self.ir(fstate, i)).and_then(|j| j.name.clone());

		llargs.reverse();
		let result = self.ll.call(abi.lltype, llvalue, llargs.as_slice(), name);

		if abi.result.base_type.is_void_kind() { return None }

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

		Some((llvalue, lltype))
	}



	fn emit_bin_op (&self, bin_op: BinaryOp, a: StackVal, b: StackVal, ty: Ref<Ty>) -> (LLVMValue, LLVMType) {
		use BinaryOp::*;


		match bin_op {  // TODO: name bin ops
			Add if ty.is_int()
			=> (self.ll.iadd(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			Sub if ty.is_int()
			=> (self.ll.isub(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			Mul if ty.is_int()
			=> (self.ll.imul(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			Div if ty.is_int()
			=> (self.ll.idiv(ty.is_signed(), a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			Rem if ty.is_int()
			=> (self.ll.irem(ty.is_signed(), a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),



			Add if ty.is_real()
			=> (self.ll.fadd(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			Sub if ty.is_real()
			=> (self.ll.fsub(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			Mul if ty.is_real()
			=> (self.ll.fmul(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			Div if ty.is_real()
			=> (self.ll.fdiv(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			Rem if ty.is_real()
			=> (self.ll.frem(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),




			Eq if ty.is_bool() || ty.is_int()
			=> (self.ll.icmp(LLVMIntEQ, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),
			Ne if ty.is_bool() || ty.is_int()
			=> (self.ll.icmp(LLVMIntNE, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),

			Eq if ty.is_real()
			=> (self.ll.fcmp(LLVMRealUEQ, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),
			Ne if ty.is_real()
			=> (self.ll.fcmp(LLVMRealUNE, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),

			Eq if ty.is_pointer() => {
				let intptr = LLVMType::int(self.ll.ctx, self.abi.word_bits());
				let lla = self.ll.bitcast(a.llvalue, intptr, None::<LLVMString>);
				let llb = self.ll.bitcast(b.llvalue, intptr, None::<LLVMString>);
				(self.ll.icmp(LLVMIntEQ, lla, llb, None::<LLVMString>), LLVMType::int1(self.ll.ctx))
			}
			Ne if ty.is_pointer() => {
				let intptr = LLVMType::int(self.ll.ctx, self.abi.word_bits());
				let lla = self.ll.bitcast(a.llvalue, intptr, None::<LLVMString>);
				let llb = self.ll.bitcast(b.llvalue, intptr, None::<LLVMString>);
				(self.ll.icmp(LLVMIntNE, lla, llb, None::<LLVMString>), LLVMType::int1(self.ll.ctx))
			}

			Eq if ty.is_function() => { todo!() } // TODO: function comparison
			Ne if ty.is_function() => { todo!() }



			Lt if ty.is_int()
			=> (self.ll.icmp(if ty.is_signed() { LLVMIntSLT } else { LLVMIntULT }, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),
			Gt if ty.is_int()
			=> (self.ll.icmp(if ty.is_signed() { LLVMIntSGT } else { LLVMIntUGT }, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),
			Le if ty.is_int()
			=> (self.ll.icmp(if ty.is_signed() { LLVMIntSLE } else { LLVMIntULE }, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),
			Ge if ty.is_int()
			=> (self.ll.icmp(if ty.is_signed() { LLVMIntSGE } else { LLVMIntUGE }, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),

			Lt if ty.is_real()
			=> (self.ll.fcmp(LLVMRealOLT, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),
			Gt if ty.is_real()
			=> (self.ll.fcmp(LLVMRealOGT, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),
			Le if ty.is_real()
			=> (self.ll.fcmp(LLVMRealOLE, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),
			Ge if ty.is_real()
			=> (self.ll.fcmp(LLVMRealOGE, a.llvalue, b.llvalue, None::<LLVMString>), LLVMType::int1(self.ll.ctx)),


			LAnd if ty.is_bool()
			=> (self.ll.and(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			LOr if ty.is_bool()
			=> (self.ll.or(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),


			BAnd if ty.is_int()
			=> (self.ll.and(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			BOr if ty.is_int()
			=> (self.ll.or(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			BXor
			=> (self.ll.xor(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),

			LSh
			=> (self.ll.l_shift(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			RShA
			=> (self.ll.arithmetic_r_shift(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),
			RShL
			=> (self.ll.logical_r_shift(a.llvalue, b.llvalue, None::<LLVMString>), a.lltype),

			_ => unreachable!()
		}
	}


	fn emit_un_op (&self, un_op: UnaryOp, e: StackVal, ty: Ref<Ty>) -> (LLVMValue, LLVMType) {
		use UnaryOp::*;

		match un_op {
			Neg if ty.is_sint()
			=> (self.ll.ineg(e.llvalue, None::<LLVMString>), e.lltype),

			Neg if ty.is_real()
			=> (self.ll.fneg(e.llvalue, None::<LLVMString>), e.lltype),

			LNot if ty.is_bool()
			=> (self.ll.not(e.llvalue, None::<LLVMString>), e.lltype),

			BNot if ty.is_int()
			=> (self.ll.not(e.llvalue, None::<LLVMString>), e.lltype),


			_ => unreachable!()
		}
	}

	fn emit_cast_op (&self, cast_op: CastOp, e: StackVal, ty: Ref<Ty>, target_ty: Ref<Ty>, lltgt_ty: LLVMType) -> LLVMValue {
		use CastOp::*;

		match cast_op {
			IntToReal if ty.is_int() && target_ty.is_real()
			=> self.ll.i2f(ty.is_signed(), e.llvalue, lltgt_ty, None::<LLVMString>),

			RealToInt if ty.is_real() && target_ty.is_int()
			=> self.ll.f2i(target_ty.is_signed(), e.llvalue, lltgt_ty, None::<LLVMString>),

			ZeroExtend if ty.is_int() && target_ty.is_int()
			=> self.ll.zext(e.llvalue, lltgt_ty, None::<LLVMString>),

			SignExtend if ty.is_int() && target_ty.is_int()
			=> self.ll.sext(e.llvalue, lltgt_ty, None::<LLVMString>),

			RealExtend if ty.is_real() && target_ty.is_real()
			=> self.ll.fext(e.llvalue, lltgt_ty, None::<LLVMString>),

			Truncate if ty.is_int() && target_ty.is_int()
			=> self.ll.itrunc(e.llvalue, lltgt_ty, None::<LLVMString>),

			RealTruncate if ty.is_real() && target_ty.is_real()
			=> self.ll.ftrunc(e.llvalue, lltgt_ty, None::<LLVMString>),

			Bitcast
			=> self.ll.bitcast(e.llvalue, lltgt_ty, None::<LLVMString>),

			_ => unreachable!()
		}
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

// #[repr(u8)]
// #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
// enum StackOp { Pop, Push }

// struct State {
// 	len: usize,
// 	mem: Vec<u128>,
// }


// impl StackOp {
//   fn to_bit (self, i: u8) -> u8 { (self as u8) << i }
//   fn to_byte (arr: [StackOp; 8]) -> u8 {
// 		arr.iter().enumerate().fold(0, |acc, (i, op)| acc | op.to_bit(i as u8))
// 	}
// }

// impl State {
// 	fn op (&mut self, op: StackOp) -> State {

// 	}
// }