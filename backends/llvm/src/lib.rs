#![allow(non_upper_case_globals, dead_code)]

use std::{cell::{Ref, RefCell, RefMut}, collections::HashMap, ops};


#[macro_use]
pub(crate) mod wrapper;
pub(crate) mod abi;

#[cfg(test)]
mod test;

use abi::{Abi, ArgAttr, ArgKind};

use uir_core::{ir::*, support::{slotmap, stack::Stack, utils::{RefAndThen}}, ty::*};

use wrapper::*;


#[derive(Default)]
pub struct LLVMMutableState {
	pub types: RefCell<HashMap<TyKey, LLVMType>>,
	pub globals: RefCell<HashMap<GlobalKey, LLVMValue>>,
	pub functions: RefCell<HashMap<FunctionKey, LLVMValue>>,
	pub target_signature_types: RefCell<HashMap<LLVMType, abi::Function>>,
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

pub struct LLVMBackend<'a> {
	pub ctx: &'a Context,
	pub abi: Box<dyn Abi>,
	pub ll: LLVM,
	pub state: LLVMMutableState,
}

impl<'a> ops::Deref for LLVMBackend<'a> {
	type Target = LLVM;
	fn deref (&self) -> &LLVM { &self.ll }
}

impl<'a> ops::DerefMut for LLVMBackend<'a> {
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

impl<'a> LLVMBackend<'a> {
	pub fn new (ctx: &'a Context) -> Option<Self> {
		let abi = abi::get_abi(ctx.target.as_ref())?;

		let ll = LLVM::new(llvm_str!("UIR_MODULE"));

		let state = LLVMMutableState::default();

		// let ctx = RefCell::new(ctx);

		Some(Self {
			abi,
			ctx,
			ll,
			state,
		})
	}


	#[track_caller]
	pub fn type_map (&self) -> Ref<HashMap<TyKey, LLVMType>> {
		self.state.types.borrow()
	}

	#[track_caller]
	pub fn type_map_mut (&self) -> RefMut<HashMap<TyKey, LLVMType>> {
		self.state.types.borrow_mut()
	}

	#[track_caller]
	pub fn global_map (&self) -> Ref<HashMap<GlobalKey, LLVMValue>> {
		self.state.globals.borrow()
	}

	#[track_caller]
	pub fn global_map_mut (&self) -> RefMut<HashMap<GlobalKey, LLVMValue>> {
		self.state.globals.borrow_mut()
	}

	#[track_caller]
	pub fn function_map (&self) -> Ref<HashMap<FunctionKey, LLVMValue>> {
		self.state.functions.borrow()
	}

	#[track_caller]
	pub fn function_map_mut (&self) -> RefMut<HashMap<FunctionKey, LLVMValue>> {
		self.state.functions.borrow_mut()
	}

	#[track_caller]
	pub fn target_signature_type_map (&self) -> Ref<HashMap<LLVMType, abi::Function>> {
		self.state.target_signature_types.borrow()
	}

	#[track_caller]
	pub fn target_signature_type_map_mut (&self) -> RefMut<HashMap<LLVMType, abi::Function>> {
		self.state.target_signature_types.borrow_mut()
	}


	pub fn ir (&self, fstate: &mut LLVMFunctionState<'a>, ir_idx: usize) -> Option<&'a Ir> {
		self.ctx
			.functions.get(fstate.fn_key)
			.unwrap()

			.block_data.get(fstate.block_key)
			.unwrap()

			.ir.get(ir_idx)
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

		let ty = self.ctx.tys.get(ty_key).unwrap();

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
						LLVMString::from(format!("$s({})", self.ctx.tys.get_index(ty_key).unwrap()))
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
			Null(ty_key) => { let ty = self.emit_ty(*ty_key); (LLVMValue::null_ptr(ty), ty) },

			Bool(val) => { let ty = self.prim_ty(PrimitiveTy::Bool); (LLVMValue::int(ty, *val as _), ty) },

			SInt8(val) => { let ty = self.prim_ty(PrimitiveTy::SInt8); (LLVMValue::int(ty, *val as _), ty) },
			SInt16(val) => { let ty = self.prim_ty(PrimitiveTy::SInt16); (LLVMValue::int(ty, *val as _), ty) },
			SInt32(val) => { let ty = self.prim_ty(PrimitiveTy::SInt32); (LLVMValue::int(ty, *val as _), ty) },
			SInt64(val) => { let ty = self.prim_ty(PrimitiveTy::SInt64); (LLVMValue::int(ty, *val as _), ty) },

			SInt128(val) => {
				let ty = self.prim_ty(PrimitiveTy::SInt128);
				(LLVMValue::int(
					ty,
					*val as _
				), ty)
			}

			UInt8(val) => { let ty = self.prim_ty(PrimitiveTy::UInt8); (LLVMValue::int(ty, *val as _), ty) },
			UInt16(val) => { let ty = self.prim_ty(PrimitiveTy::UInt16); (LLVMValue::int(ty, *val as _), ty) },
			UInt32(val) => { let ty = self.prim_ty(PrimitiveTy::UInt32); (LLVMValue::int(ty, *val as _), ty) },
			UInt64(val) => { let ty = self.prim_ty(PrimitiveTy::UInt64); (LLVMValue::int(ty, *val as _), ty) },

			UInt128(val) =>  {
				let ty = self.prim_ty(PrimitiveTy::UInt128);
				(LLVMValue::int(
					ty,
					*val
				), ty)
			}

			Real32(val) => { let ty = self.prim_ty(PrimitiveTy::Real32); (LLVMValue::real(ty, *val as _), ty) },
			Real64(val) => { let ty = self.prim_ty(PrimitiveTy::Real64); (LLVMValue::real(ty, *val), ty) },

			Aggregate(ty_key, aggregate_data) => {
				let ty = self.ctx.tys.get(*ty_key).unwrap();
				let llty = self.emit_ty(*ty_key);

				let llval = match aggregate_data {
					ConstantAggregateData::Uninitialized => LLVMValue::undef(llty),

					ConstantAggregateData::Zeroed => LLVMValue::zero(llty),

					ConstantAggregateData::CopyFill(elem) => {
						let (llelem, llelem_ty) = self.emit_constant(elem);

						let out = LLVMValue::zero(llty);

						match &ty.data {
							TyData::Array { length, element_ty: expected_ty } => {
								assert_eq!(self.emit_ty(*expected_ty), llelem_ty);
								out.const_fill_agg(llelem, *length)
							}

							TyData::Structure { field_tys } => {
								field_tys.iter().for_each(|x| assert_eq!(self.emit_ty(*x), llelem_ty));
								out.const_fill_agg(llelem, field_tys.len() as u32)
							}

							_ => unreachable!()
						}
					},

					ConstantAggregateData::Indexed(indexed_elems) => {
						let mut out = LLVMValue::zero(llty);

						match &ty.data {
							TyData::Array { length, element_ty: expected_ty } => {
								let expected_ty = self.emit_ty(*expected_ty);

								for &(i, ref elem) in indexed_elems.iter() {
									let (llelem, llelem_ty) = self.emit_constant(elem);

									assert!(i < *length);

									assert_eq!(expected_ty, llelem_ty);

									out = out.const_insert_value(llelem, i);
								}
							}

							TyData::Structure { field_tys } => {
								for &(i, ref elem) in indexed_elems.iter() {
									let field_ty = field_tys[i as usize];
									let field_llty = self.emit_ty(field_ty);

									let (llelem, llelem_ty) = self.emit_constant(elem);
									assert_eq!(field_llty, llelem_ty);

									out = out.const_insert_value(llelem, i);
								}
							}

							_ => unreachable!()
						}

						out
					},

					ConstantAggregateData::Complete(elems) => {
						let mut out = LLVMValue::zero(llty);

						match &ty.data {
							TyData::Array { length, element_ty: expected_ty } => {
								let expected_ty = self.emit_ty(*expected_ty);
								for i in 0..*length {
									let (llelem, llelem_ty) = self.emit_constant(&elems[i as usize]);
									assert_eq!(expected_ty, llelem_ty);

									out = out.const_insert_value(llelem, i);
								}
							}

							TyData::Structure { field_tys } => {
								for (i, &field_ty) in field_tys.iter().enumerate() {
									let field_llty = self.emit_ty(field_ty);

									let (llelem, llelem_ty) = self.emit_constant(&elems[i as usize]);
									assert_eq!(field_llty, llelem_ty);

									out = out.const_insert_value(llelem, i as u32);
								}
							}

							_ => unreachable!()
						}

						out
					},
				};

				(llval, llty)
			}
		}
	}

	pub fn generate_id<K: slotmap::Key> (prefix: &str, k: K) -> LLVMString {
		LLVMString::from(format!("${}({})", prefix, k.as_integer()))
	}

	pub fn emit_global (&self, global_key: GlobalKey) -> LLVMValue {
		if let Some(llglobal) = self.global_map_mut().get(&global_key) {
			return *llglobal
		}

		let global = self.ctx.globals.get(global_key).unwrap();

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

		self.global_map_mut().insert(global_key, llglobal);

		llglobal
	}


	pub fn emit_function_decl (&self, function_key: FunctionKey) -> LLVMValue {
		if let Some(llfunction) = self.function_map_mut().get(&function_key) {
			return *llfunction
		}

		let function = self.ctx.functions.get(function_key).unwrap();

		let llty = self.emit_ty(function.ty);
		let abi = self.abi_info(llty);
		let abi_llty = abi.lltype;

		let llname = if let Some(name) = function.name.as_ref() {
			LLVMString::from(name)
		} else {
			Self::generate_id("f", function_key)
		};

		let func = LLVMValue::create_function(self.module, abi_llty, llname);

		self.function_map_mut().insert(function_key, func);

		func
	}


	pub fn ir_ty (&self, fstate: &mut LLVMFunctionState, ir_idx: usize) -> TyKey {
		fstate.func.ty_map.get(fstate.block_key, ir_idx)
	}

	pub fn emit_function_body (&self, function_key: FunctionKey) -> LLVMValue {
		let func = self.ctx.functions.get(function_key).unwrap();

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
			let llblock = *fstate.blocks.get(&block_key).unwrap();
			fstate.llblock = llblock;
			fstate.block_key = block_key;
			self.emit_block_terminator(&mut fstate, &block_in_vals, block_out_vals.remove(&block_key).unwrap())
		}

		llfunc
	}

	pub fn emit_block_body (&self, fstate: &mut LLVMFunctionState<'a>) -> (Stack<StackVal>, Stack<StackVal>) {
		let block = fstate.func.block_data.get(fstate.block_key).unwrap();
		self.position_at_end(fstate.llblock);

		let mut iter = block.ir.iter().enumerate().peekable();

		let mut in_vals = Stack::default();

		while let Some((ir_idx, ir)) = iter.next() {
			match &ir.data {
				x if x.is_terminator() => unreachable!(),

				IrData::Phi(phi_ty_key) => {
					// dbg!(phi_ty_key);

					let name = ir.name.as_deref().unwrap_or("phi");
					let llty = self.emit_ty(*phi_ty_key);
					let phi = self.ll.phi(llty, Some(name));
					let ty_key = self.ir_ty(fstate, ir_idx);

					let stack_val = StackVal::source(phi, llty, ir_idx, ty_key);

					in_vals.push(stack_val);
					fstate.stack.push(stack_val)
				}


				IrData::Constant(constant) => {
					// dbg!(constant);

					let (llconst, llconst_ty) = self.emit_constant(constant);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llconst, llconst_ty, ir_idx, ty_key))
				}


				IrData::BuildAggregate(ty_key, aggregate_data) => {
					// dbg!(ty_key, aggregate_data);

					let ty = self.ctx.tys.get(*ty_key).unwrap();
					let llty = self.emit_ty(*ty_key);

					let llval = match aggregate_data {
						AggregateData::Uninitialized => LLVMValue::undef(llty),
						AggregateData::Zeroed => LLVMValue::zero(llty),
						AggregateData::CopyFill => {
							let elem = fstate.stack.pop().unwrap();

							let out = LLVMValue::zero(llty);

							match &ty.data {
								TyData::Array { length, element_ty } => {
									assert_eq!(self.emit_ty(*element_ty), elem.lltype);
									self.ll.fill_agg(out, elem.llvalue, *length)
								}

								TyData::Structure { field_tys } => {
									field_tys.iter().for_each(|x| assert_eq!(self.emit_ty(*x), elem.lltype));
									self.ll.fill_agg(out, elem.llvalue, field_tys.len() as u32)
								}

								_ => unreachable!()
							}
						},
						AggregateData::Indexed(indices) => {
							let mut out = LLVMValue::zero(llty);

							match &ty.data {
								TyData::Array { length, element_ty } => {
									let elem_llty = self.emit_ty(*element_ty);

									for &i in indices.iter() {
										assert!(i < *length);

										let elem = fstate.stack.pop().unwrap();
										assert_eq!(elem_llty, elem.lltype);

										out = self.ll.insert_value(out, elem.llvalue, i, None::<LLVMString>);
									}
								}

								TyData::Structure { field_tys } => {
									for &i in indices.iter() {
										let field_ty = *field_tys.get(i as usize).unwrap();
										let field_llty = self.emit_ty(field_ty);

										let elem = fstate.stack.pop().unwrap();
										assert_eq!(field_llty, elem.lltype);

										out = self.ll.insert_value(out, elem.llvalue, i, None::<LLVMString>);
									}
								}

								_ => unreachable!()
							}

							out
						},

						AggregateData::Complete => {
							let mut out = LLVMValue::zero(llty);

							match &ty.data {
								TyData::Array { length, element_ty } => {
									let elem_llty = self.emit_ty(*element_ty);
									for i in 0..*length {
										let elem = fstate.stack.pop().unwrap();
										assert_eq!(elem.lltype, elem_llty);

										out = self.ll.insert_value(out, elem.llvalue, i, None::<LLVMString>);
									}
								}

								TyData::Structure { field_tys } => {
									for (i, &field_ty) in field_tys.iter().enumerate() {
										let field_llty = self.emit_ty(field_ty);

										let elem = fstate.stack.pop().unwrap();
										assert_eq!(elem.lltype, field_llty);

										out = self.ll.insert_value(out, elem.llvalue, i as u32, None::<LLVMString>);
									}
								}

								_ => unreachable!()
							}

							out
						},
					};

					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llval, llty, ir_idx, ty_key))
				}


				IrData::GlobalRef(gkey) => {
					// dbg!(gkey);

					let global = self.ctx.globals.get(*gkey).unwrap();
					let llg = self.emit_global(*gkey);
					let llty = self.emit_ty(global.ty).as_pointer(0);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llg, llty, ir_idx, ty_key))
				}

				IrData::FunctionRef(fkey) => {
					// dbg!(fkey);

					let function = self.ctx.functions.get(*fkey).unwrap();
					let llf = self.emit_function_decl(*fkey);
					let llty = self.emit_ty(function.ty).as_pointer(0);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llf, llty, ir_idx, ty_key))
				}

				IrData::BlockRef(bkey) => {
					// dbg!(bkey);

					let llbb = *fstate.blocks.get(bkey).unwrap();
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llbb.as_value(), LLVMType::label(self.ll.ctx), ir_idx, ty_key))
				}

				IrData::ParamRef(pkey) => {
					// dbg!(pkey);

					let llparam = *fstate.params.get(pkey).unwrap();
					let llty = self.emit_ty(fstate.func.param_data.get(*pkey).unwrap().ty).as_pointer(0);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llparam, llty, ir_idx, ty_key))
				}

				IrData::LocalRef(lkey) => {
					// dbg!(lkey);

					let llvar = *fstate.locals.get(lkey).unwrap();
					let llty = self.emit_ty(fstate.func.locals.get(*lkey).unwrap().ty).as_pointer(0);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llvar, llty, ir_idx, ty_key))
				}


				IrData::BinaryOp(bin_op) => {
					// dbg!(bin_op);

					let a = fstate.stack.pop().unwrap();
					let b = fstate.stack.pop().unwrap();

					let ty = self.ctx.tys.get(a.ty_key).unwrap();

					assert_eq!(a.lltype, b.lltype);

					let (llvalue, lltype) = self.emit_bin_op(*bin_op, a, b, ty);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llvalue, lltype, ir_idx, ty_key))
				}

				IrData::UnaryOp(un_op) => {
					// dbg!(un_op);

					let e = fstate.stack.pop().unwrap();

					let ty = self.ctx.tys.get(e.ty_key).unwrap();

					let (llvalue, lltype) = self.emit_un_op(*un_op, e, ty);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llvalue, lltype, ir_idx, ty_key))
				}

				IrData::CastOp(cast_op, target_ty_key) => {
					// dbg!(cast_op, target_ty_key);

					let e = fstate.stack.pop().unwrap();

					let ty = self.ctx.tys.get(e.ty_key).unwrap();
					let target_ty = self.ctx.tys.get(*target_ty_key).unwrap();
					let lltype = self.emit_ty(*target_ty_key);

					let llvalue = self.emit_cast_op(*cast_op, e, ty, target_ty, lltype);
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(llvalue, lltype, ir_idx, ty_key))
				}

				IrData::Gep(gep_num_indices) => {
					// dbg!(gep_num_indices);


					let mut gep_stack = fstate.stack.pop_n_to(*gep_num_indices as usize + 1).unwrap().reversed();

					let StackVal { llvalue: lltarget, lltype, .. } = gep_stack.pop().unwrap();
					assert!(lltype.is_pointer_kind());
					let llbase_ty = lltype.get_element_type();

					let indices =
						gep_stack
							.into_iter()
							.map(|x| {
								assert!(x.lltype.is_integer_kind());
								x.llvalue
							})
							.collect::<Vec<_>>();

					let ty_key = self.ir_ty(fstate, ir_idx);
					let llty = self.emit_ty(ty_key);
					let gep = self.ll.gep(llbase_ty, lltarget, &indices, None::<LLVMString>); // TODO: name geps
					fstate.stack.push(StackVal::source(gep, llty, ir_idx, ty_key))
				}

				IrData::Load => {
					// dbg!("load");

					let StackVal { lltype, llvalue, .. } = fstate.stack.pop().unwrap();
					assert!(!lltype.get_element_type().is_function_kind()); // TODO: more robust unloadable type check?

					let load = self.ll.load(llvalue, None::<LLVMString>); // TODO: name loads
					let ty_key = self.ir_ty(fstate, ir_idx);
					fstate.stack.push(StackVal::source(load, lltype.get_element_type(), ir_idx, ty_key))
				}

				IrData::Store => {
					// dbg!("stor");

					let StackVal { lltype: llptr_ty, llvalue: llptr, .. } = fstate.stack.pop().unwrap();
					let StackVal { lltype: llval_ty, llvalue: llval, .. } = fstate.stack.pop().unwrap();
					assert_eq!(llptr_ty.get_element_type(), llval_ty);

					self.ll.store(llval, llptr);
				}



				IrData::Call => {
					// dbg!("call");

					if let Some((llval, llty)) = self.emit_call(fstate) {
						let ty_key = self.ir_ty(fstate, ir_idx);
						fstate.stack.push(StackVal::source(llval, llty, ir_idx, ty_key))
					}
				}

				IrData::Duplicate => {
					// dbg!("duplicate");

					let val = *fstate.stack.peek().unwrap();
					fstate.stack.push(val);
				}

				IrData::Discard => {
					// dbg!("discard");

					fstate.stack.pop();
				}

				IrData::Swap => {
					// dbg!("swap");

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

			if let Some(&(j, x)) = iter.peek() {
				if x.is_terminator() {
					assert_eq!(j, block.ir.len() - 1);
					return (in_vals, std::mem::take(&mut fstate.stack))
				}
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
			IrData::Branch(branch_dest) => {
				// dbg!(branch_dest);

				let lldest = *fstate.blocks.get(branch_dest).unwrap();
				self.ll.branch(lldest);

				fixup_phis(branch_dest, &out_vals);
			}

			IrData::CondBranch(then_branch, else_branch) => {
				// dbg!(then_branch, else_branch);

				let StackVal { llvalue, .. } = out_vals.pop().unwrap();

				let lla = *fstate.blocks.get(then_branch).unwrap();
				let llb = *fstate.blocks.get(else_branch).unwrap();
				self.ll.cond_branch(llvalue, lla, llb);

				fixup_phis(then_branch, &out_vals);
				fixup_phis(else_branch, &out_vals);
			}

			IrData::Switch(switch_branches, default_block) => {
				// dbg!(switch_branches, default_block);

				let lldefault = *fstate.blocks.get(default_block).unwrap();
				let StackVal { llvalue, lltype, .. } = out_vals.pop().unwrap();
				let switch = self.ll.switch(llvalue, lldefault, switch_branches.len() as u32);
				switch_branches.iter().for_each(|(constant, block)| {
					let (llconst, llconst_ty) = self.emit_constant(constant);
					assert_eq!(llconst_ty, lltype);

					let llblock = *fstate.blocks.get(block).unwrap();

					switch.add_case(llconst, llblock);
					fixup_phis(block, &out_vals);
				});

				fixup_phis(default_block, &out_vals);
			}

			IrData::ComputedBranch(computed_dests) => {
				// dbg!(computed_dests);

				let StackVal { llvalue, lltype, .. } = out_vals.pop().unwrap();

				assert!(lltype == LLVMType::label(self.ll.ctx));

				self.ll.indirect_branch(llvalue, computed_dests.len() as u32);

				computed_dests.iter().for_each(|dest| fixup_phis(dest, &out_vals));
			}

			IrData::Ret => {
				// dbg!("ret");

				self.emit_return(fstate, out_vals);
			}

			IrData::Unreachable
			=> {
				// dbg!("unreachable");

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

		let entry = self.ll.append_basic_block(fstate.llfunc, Some(llvm_str!("abi")));
		self.ll.position_at_end(entry);

		let mut llparams = fstate.llfunc.get_params().into_iter();


		if abi.result.kind == ArgKind::Indirect {
			fstate.sret = Some(llparams.next().unwrap());
		}


	 	for (abi_arg, &param_key) in abi.args.iter().zip(fstate.func.param_order.iter()) {
			let param = match abi_arg.kind {
				ArgKind::Direct => {
					let alloca = self.ll.alloca(abi_arg.base_type, None::<LLVMString>); // TODO: name params
					let mut abi_ptr = alloca;

					let llvalue = if let Some(ArgAttr::ZExt) = abi_arg.attribute {
						// TODO: this is currently only handling i8 -> i1
						let int1 = LLVMType::int1(self.ll.ctx);
						debug_assert!(abi_arg.base_type == int1);

						self.ll.itrunc(llparams.next().unwrap(), int1, None::<LLVMString>) // TODO: name truncs
					} else if abi_arg.cast_types.is_empty() {
						llparams.next().unwrap()
					} else {
						let cast_ty = LLVMType::anonymous_structure(self.ll.ctx, &abi_arg.cast_types, false);
						let mut agg = LLVMValue::zero(cast_ty);
						for i in 0..abi_arg.cast_types.len() as u32 {
							let llparam = llparams.next().unwrap();

							agg = self.ll.insert_value(agg, llparam, i, None::<LLVMString>); // TODO: name inserts
						}

						abi_ptr = self.ll.bitcast(abi_ptr, cast_ty.as_pointer(0), None::<LLVMString>); // TODO: name casts

						agg
					};

					self.ll.store(llvalue, abi_ptr);

					alloca
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
						self.ll.zext(base_llvalue, LLVMType::int8(self.ll.ctx), None::<LLVMString>) // TODO: name zext
					} else if abi.result.cast_types.is_empty() {
						base_llvalue
					} else {
						let arg_ty =
							if abi.result.cast_types.len() == 1 {
								*abi.result.cast_types.first().unwrap()
							} else {
								LLVMType::anonymous_structure(self.ll.ctx, &abi.result.cast_types, false)
							};

						let alloca = self.ll.alloca(arg_ty, None::<LLVMString>); // TODO: name temporary abi alloca?
						let cast = self.ll.bitcast(alloca, abi.result.base_type.as_pointer(0), None::<LLVMString>); // TODO: name cast

						self.ll.store(base_llvalue, cast);

						self.ll.load(alloca, None::<LLVMString>) // TODO: name abi return?
					};

					self.ll.ret(llvalue)
				}
			}

			ArgKind::Indirect => {
				let StackVal { llvalue: base_llvalue, .. } = stack.pop().unwrap();
				self.store(base_llvalue, fstate.sret.unwrap());

				self.ll.ret_void()
			}
		};

		assert!(stack.is_empty());

		val
	}



	fn emit_call (&self, fstate: &mut LLVMFunctionState<'a>) -> Option<(LLVMValue, LLVMType)> {
		let StackVal { llvalue, mut lltype, ir_idx, ty_key: _ } = fstate.stack.pop().unwrap();

		if lltype.is_pointer_kind() { lltype = lltype.get_element_type() }

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

						self.ll.zext(base_llvalue, LLVMType::int8(self.ll.ctx), None::<LLVMString>) // TODO: name zexts
					} else if abi_arg.cast_types.is_empty() {
						base_llvalue
					} else {
						let arg_struct = LLVMType::anonymous_structure(self.ll.ctx, &abi_arg.cast_types, false);

						self.ll.bitcast(base_llvalue, arg_struct, None::<LLVMString>) // TODO: name destructure casts
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
					.and_then(|i| self.ir(fstate, i).and_then(|k| k.name.as_ref()))
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
					self.ll.bitcast(result, abi.result.base_type, None::<LLVMString>) // TODO: name trunc rets
				}, abi.result.base_type)
			}
		};

		Some((llvalue, lltype))
	}



	fn emit_bin_op (&self, bin_op: BinaryOp, a: StackVal, b: StackVal, ty: &'a Ty) -> (LLVMValue, LLVMType) {
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

			Eq if ty.is_pointer() => { // TODO: int to ptr instr
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


	fn emit_un_op (&self, un_op: UnaryOp, e: StackVal, ty: &'a Ty) -> (LLVMValue, LLVMType) {
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

	fn emit_cast_op (&self, cast_op: CastOp, e: StackVal, ty: &'a Ty, target_ty: &'a Ty, lltgt_ty: LLVMType) -> LLVMValue {
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

			Bitcast if ty.is_primitive() || ty.is_pointer()
			=> self.ll.bitcast(e.llvalue, lltgt_ty, None::<LLVMString>),

			Bitcast if ty.is_aggregate()
			=> {
				let alloca = self.ll.alloca(e.lltype.as_pointer(0), None::<LLVMString>);
				self.ll.store(e.llvalue, alloca);
				let cast = self.ll.bitcast(alloca, lltgt_ty.as_pointer(0), None::<LLVMString>);
				self.ll.load(cast, None::<LLVMString>)
			}

			_ => unreachable!()
		}
	}
}