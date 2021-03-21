
use crate::abi::{self, Abi, ArgAttr, ArgKind};

use uir_core::{ir::*, support::{slotmap::{self, Key}, stack::Stack}, ty::*};

use std::{collections::HashMap, ops};

use crate::wrapper::*;


pub struct Emitter<'a> {
	pub ctx: &'a Context,
	pub abi: Box<dyn Abi>,
	pub ll: LLVM,
	pub types: HashMap<TyKey, LLVMType>,
	pub globals: HashMap<GlobalKey, LLVMValue>,
	pub functions: HashMap<FunctionKey, LLVMValue>,
	pub target_signature_types: HashMap<LLVMType, abi::Function>,
}

pub struct EmitterFunctionState<'c> {
	pub func: &'c Function,
	pub llfunc: LLVMValue,
	pub fn_key: FunctionKey,
	pub llblock: LLVMBlock,
	pub block_key: BlockKey,
	pub params: HashMap<ParamKey, LLVMValue>,
	pub locals: HashMap<LocalKey, LLVMValue>,
	pub blocks: HashMap<BlockKey, LLVMBlock>,
	pub stack : Stack<Value>,
	pub sret  : Option<LLVMValue>,
}

impl<'a> ops::Deref for Emitter<'a> {
	type Target = LLVM;
	fn deref (&self) -> &LLVM { &self.ll }
}

impl<'a> ops::DerefMut for Emitter<'a> {
	fn deref_mut (&mut self) -> &mut LLVM { &mut self.ll }
}

impl<'c> EmitterFunctionState<'c> {
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

#[derive(Clone, Copy)]
pub struct Value {
	pub llvalue: LLVMValue,
	pub lltype: LLVMType,
	pub ir_idx: Option<usize>,
	pub ty_key: TyKey,
}

impl Value {
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

impl<'a> Emitter<'a> {
	pub fn new (ctx: &'a Context) -> Option<Self> {
		let abi = abi::get_abi(ctx.target.as_ref())?;

		let ll = LLVM::new(llvm_str!("UIR_MODULE")); // TODO module names

		Some(Self {
			abi,
			ctx,
			ll,
			types: HashMap::default(),
			globals: HashMap::default(),
			functions: HashMap::default(),
			target_signature_types: HashMap::default(),
		})
	}


	pub fn ir (&self, fstate: &mut EmitterFunctionState<'a>, ir_idx: usize) -> Option<&'a Ir> {
		self.ctx
			.functions.get(fstate.fn_key)
			.unwrap()

			.block_data.get(fstate.block_key)
			.unwrap()

			.ir.get(ir_idx)
	}


	pub fn emit_prim_ty (&self, prim: PrimitiveTy) -> LLVMType {
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

	pub fn emit_ty (&mut self, ty_key: TyKey) -> LLVMType {
		if let Some(llty) = self.types.get(&ty_key) {
			return *llty
		}

		let ty = self.ctx.tys.get(ty_key).unwrap();

		let llty = {
			use TyData::*;

			match &ty.data {
				Void => LLVMType::void(self.ll.ctx),

				Block => LLVMType::label(self.ll.ctx),

				Primitive(prim) => self.emit_prim_ty(*prim),

				Pointer { target_ty } => self.emit_ty(*target_ty).as_pointer(0),

				Array { length, element_ty } => self.emit_ty(*element_ty).as_array(*length as _),

				Structure { field_tys } => {
					let llname = if let Some(name) = ty.name.as_ref() {
						LLVMString::from(name)
					} else {
						LLVMString::from(format!("$s({})", ty_key.as_integer()))
					};

					let llty = LLVMType::named_empty_structure(self.ll.ctx, llname);

					self.types.insert(ty_key, llty);

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

		self.types.insert(ty_key, llty);

		llty
	}

	pub fn abi_info(&mut self, lltype: LLVMType) -> abi::Function {
		assert!(lltype.kind() == LLVMFunctionTypeKind);

		match self.target_signature_types.get(&lltype).cloned() {
			Some(existing) => existing,
			None => {
				let parameter_tys = lltype.get_param_types();
				let return_ty = lltype.get_return_type();

				let abi = self.abi.get_info(self.ll.ctx, &parameter_tys, return_ty);
				self.target_signature_types.insert(lltype, abi.clone());

				abi
			}
		}
	}


	pub fn emit_constant (&mut self, constant: &Constant) -> (LLVMValue, LLVMType) {
		use Constant::*;

		match constant {
			Null(ty_key) => { let ty = self.emit_ty(*ty_key); (LLVMValue::null_ptr(ty), ty) },

			Bool(val) => { let ty = self.emit_prim_ty(PrimitiveTy::Bool); (LLVMValue::int(ty, *val as _), ty) },

			SInt8(val) => { let ty = self.emit_prim_ty(PrimitiveTy::SInt8); (LLVMValue::int(ty, *val as _), ty) },
			SInt16(val) => { let ty = self.emit_prim_ty(PrimitiveTy::SInt16); (LLVMValue::int(ty, *val as _), ty) },
			SInt32(val) => { let ty = self.emit_prim_ty(PrimitiveTy::SInt32); (LLVMValue::int(ty, *val as _), ty) },
			SInt64(val) => { let ty = self.emit_prim_ty(PrimitiveTy::SInt64); (LLVMValue::int(ty, *val as _), ty) },

			SInt128(val) => {
				let ty = self.emit_prim_ty(PrimitiveTy::SInt128);
				(LLVMValue::int(
					ty,
					*val as _
				), ty)
			}

			UInt8(val) => { let ty = self.emit_prim_ty(PrimitiveTy::UInt8); (LLVMValue::int(ty, *val as _), ty) },
			UInt16(val) => { let ty = self.emit_prim_ty(PrimitiveTy::UInt16); (LLVMValue::int(ty, *val as _), ty) },
			UInt32(val) => { let ty = self.emit_prim_ty(PrimitiveTy::UInt32); (LLVMValue::int(ty, *val as _), ty) },
			UInt64(val) => { let ty = self.emit_prim_ty(PrimitiveTy::UInt64); (LLVMValue::int(ty, *val as _), ty) },

			UInt128(val) =>  {
				let ty = self.emit_prim_ty(PrimitiveTy::UInt128);
				(LLVMValue::int(
					ty,
					*val
				), ty)
			}

			Real32(val) => { let ty = self.emit_prim_ty(PrimitiveTy::Real32); (LLVMValue::real(ty, *val as _), ty) },
			Real64(val) => { let ty = self.emit_prim_ty(PrimitiveTy::Real64); (LLVMValue::real(ty, *val), ty) },

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

	pub fn emit_global (&mut self, global_key: GlobalKey) -> LLVMValue {
		if let Some(llglobal) = self.globals.get(&global_key) {
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

		self.globals.insert(global_key, llglobal);

		llglobal
	}


	pub fn emit_function_decl (&mut self, function_key: FunctionKey) -> LLVMValue {
		if let Some(llfunction) = self.functions.get(&function_key) {
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

		self.functions.insert(function_key, func);

		func
	}


	#[cfg_attr(debug_assertions, track_caller)]
	pub fn ir_ty (&self, fstate: &mut EmitterFunctionState, ir_idx: usize) -> TyKey {
		fstate.func.ty_map.get(fstate.block_key, ir_idx)
	}

	pub fn emit_function (&mut self, function_key: FunctionKey) -> LLVMValue {
		let func = self.ctx.functions.get(function_key).unwrap();

		let llfunc = self.emit_function_decl(function_key);

		let mut fstate = EmitterFunctionState::new(llfunc, function_key, &func);

		let _entry = self.emit_entry(&mut fstate);

		for &block_key in func.block_order.iter() {
			let block = func.block_data.get(block_key).unwrap();
			let name = block.name.as_deref().unwrap_or("$block");

			let block = self.ll.append_basic_block(llfunc, LLVMString::from(name));

			fstate.blocks.insert(block_key, block);
		}

		let user_entry = *func.block_order.first().unwrap();
		let lluser_entry = *fstate.blocks.get(&user_entry).unwrap();

		self.ll.branch(lluser_entry);


		let mut block_in_vals = HashMap::<BlockKey, Stack<Value>>::default();
		let mut block_out_vals = HashMap::<BlockKey, Stack<Value>>::default();
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
			self.emit_terminator_node(&mut fstate, &block_in_vals, block_out_vals.remove(&block_key).unwrap())
		}

		llfunc
	}

	pub fn emit_block_body (&mut self, fstate: &mut EmitterFunctionState<'a>) -> (Stack<Value>, Stack<Value>) {
		let block = fstate.func.block_data.get(fstate.block_key).unwrap();
		self.position_at_end(fstate.llblock);

		let mut iter = block.ir.iter().enumerate().peekable();

		let mut in_vals = Stack::default();
		while let Some(&(ir_idx, ir)) = iter.peek() {
			if !ir.is_init() { break }
			in_vals.push(self.emit_init_node(fstate, ir_idx, ir));
			iter.next();
		}

		while let Some(&(ir_idx, ir)) = iter.peek() {
			if ir.is_terminator() { break }

			self.emit_body_node(fstate, ir_idx, ir);

			iter.next();
		}

		let x = iter.next().unwrap().1;
		assert!(x.is_terminator());
		assert!(iter.next().is_none());

		(in_vals, std::mem::take(&mut fstate.stack))
	}

	pub fn emit_init_node (&mut self, fstate: &mut EmitterFunctionState<'a>, ir_idx: usize, ir: &Ir) -> Value {
		match &ir.data {
			IrData::Phi(phi_ty_key) => {
				// dbg!(phi_ty_key);

				let lltype = self.emit_ty(*phi_ty_key);
				let llvalue = self.ll.phi(lltype);
				let ty_key = self.ir_ty(fstate, ir_idx);

				if let Some(name) = ir.name.as_deref() {
					llvalue.set_name(LLVMString::from(name));
				}

				let stack_val = Value::source(llvalue, lltype, ir_idx, ty_key);

				fstate.stack.push(stack_val);

				stack_val
			}

			| IrData::Constant { .. }
			| IrData::BuildAggregate { .. }
			| IrData::GetElement { .. }
			| IrData::SetElement { .. }
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
			| IrData::Branch { .. }
			| IrData::CondBranch { .. }
			| IrData::Switch { .. }
			| IrData::ComputedBranch { .. }
			| IrData::Call
			| IrData::Ret
			| IrData::Duplicate { .. }
			| IrData::Discard { .. }
			| IrData::Swap { .. }
			| IrData::Unreachable
			=> unreachable!()
		}
	}

	pub fn emit_body_node (&mut self, fstate: &mut EmitterFunctionState<'a>, ir_idx: usize, ir: &Ir) -> Option<Value> {
		match &ir.data {
			IrData::Phi(_) => unreachable!(),


			IrData::Constant(constant) => {
				// dbg!(constant);

				let (llconst, llconst_ty) = self.emit_constant(constant);
				let ty_key = self.ir_ty(fstate, ir_idx);
				fstate.stack.push(Value::source(llconst, llconst_ty, ir_idx, ty_key))
			}


			IrData::BuildAggregate(ty_key, aggregate_data) => {
				// dbg!(ty_key, aggregate_data);

				let ty = self.ctx.tys.get(*ty_key).unwrap();
				let llty = self.emit_ty(*ty_key);

				let name = ir.name.as_deref().map(LLVMString::from);

				let llval = match aggregate_data {
					AggregateData::Uninitialized => LLVMValue::undef(llty),

					AggregateData::Zeroed => LLVMValue::zero(llty),

					AggregateData::CopyFill => {
						let elem = fstate.stack.pop().unwrap();

						let out = LLVMValue::zero(llty);

						match &ty.data {
							TyData::Array { length, element_ty } => {
								assert_eq!(self.emit_ty(*element_ty), elem.lltype);
								self.ll.fill_agg(out, elem.llvalue, *length, name.as_ref())
							}

							TyData::Structure { field_tys } => {
								field_tys.iter().for_each(|x| assert_eq!(self.emit_ty(*x), elem.lltype));
								self.ll.fill_agg(out, elem.llvalue, field_tys.len() as u32, name.as_ref())
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

									out = self.ll.insert_value(out, elem.llvalue, i);

									if let Some(name) = name.as_ref() { out.set_name(name) }
								}
							}

							TyData::Structure { field_tys } => {
								for &i in indices.iter() {
									let field_ty = *field_tys.get(i as usize).unwrap();
									let field_llty = self.emit_ty(field_ty);

									let elem = fstate.stack.pop().unwrap();
									assert_eq!(field_llty, elem.lltype);

									out = self.ll.insert_value(out, elem.llvalue, i);

									if let Some(name) = name.as_ref() { out.set_name(name) }
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

									out = self.ll.insert_value(out, elem.llvalue, i);

									if let Some(name) = name.as_ref() { out.set_name(name) }
								}
							}

							TyData::Structure { field_tys } => {
								for (i, &field_ty) in field_tys.iter().enumerate() {
									let field_llty = self.emit_ty(field_ty);

									let elem = fstate.stack.pop().unwrap();
									assert_eq!(elem.lltype, field_llty);

									out = self.ll.insert_value(out, elem.llvalue, i as u32);

									if let Some(name) = name.as_ref() { out.set_name(name) }
								}
							}

							_ => unreachable!()
						}

						out
					},
				};

				let ty_key = self.ir_ty(fstate, ir_idx);
				fstate.stack.push(Value::source(llval, llty, ir_idx, ty_key))
			}

			IrData::SetElement(idx) => {
				let elem = fstate.stack.pop().unwrap();

				let agg = fstate.stack.pop().unwrap();
				match agg.lltype.kind() {
					LLVMStructTypeKind => {
						assert!(agg.lltype.count_element_types() > *idx);
						assert!(agg.lltype.get_type_at_index(*idx) == elem.lltype);
					}
					LLVMArrayTypeKind => {
						assert!(agg.lltype.get_array_length() > *idx);
						assert!(agg.lltype.get_element_type() == elem.lltype);
					}
					_ => unreachable!()
				}

				let llvalue = self.ll.insert_value(agg.llvalue, elem.llvalue, *idx);

				if let Some(name) = ir.name.as_deref() {
					llvalue.set_name(LLVMString::from(name));
				}

				let ty_key = self.ir_ty(fstate, ir_idx);
				fstate.stack.push(Value::source(llvalue, agg.lltype, ir_idx, ty_key))
			}

			IrData::GetElement(idx) => {
				let agg = fstate.stack.pop().unwrap();

				let llelem_ty = match agg.lltype.kind() {
					LLVMStructTypeKind => {
						assert!(agg.lltype.count_element_types() > *idx);
						agg.lltype.get_type_at_index(*idx)
					}
					LLVMArrayTypeKind => {
						assert!(agg.lltype.get_array_length() > *idx);
						agg.lltype.get_element_type()
					}
					_ => unreachable!()
				};

				let llvalue = self.ll.extract_value(agg.llvalue, *idx);

				if let Some(name) = ir.name.as_deref() {
					llvalue.set_name(LLVMString::from(name));
				}

				let ty_key = self.ir_ty(fstate, ir_idx);

				fstate.stack.push(Value::source(llvalue, llelem_ty, ir_idx, ty_key))
			}


			IrData::GlobalRef(gkey) => {
				// dbg!(gkey);

				let global = self.ctx.globals.get(*gkey).unwrap();
				let llg = self.emit_global(*gkey);
				let llty = self.emit_ty(global.ty).as_pointer(0);
				let ty_key = self.ir_ty(fstate, ir_idx);
				fstate.stack.push(Value::source(llg, llty, ir_idx, ty_key))
			}

			IrData::FunctionRef(fkey) => {
				// dbg!(fkey);

				let function = self.ctx.functions.get(*fkey).unwrap();
				let llf = self.emit_function_decl(*fkey);
				let llty = self.emit_ty(function.ty).as_pointer(0);
				let ty_key = self.ir_ty(fstate, ir_idx);
				fstate.stack.push(Value::source(llf, llty, ir_idx, ty_key))
			}

			IrData::BlockRef(bkey) => {
				// dbg!(bkey);

				let llbb = *fstate.blocks.get(bkey).unwrap();
				let ty_key = self.ir_ty(fstate, ir_idx);
				fstate.stack.push(Value::source(llbb.as_value(), LLVMType::label(self.ll.ctx), ir_idx, ty_key))
			}

			IrData::ParamRef(pkey) => {
				// dbg!(pkey);

				let llparam = *fstate.params.get(pkey).unwrap();
				let llty = self.emit_ty(fstate.func.param_data.get(*pkey).unwrap().ty).as_pointer(0);
				let ty_key = self.ir_ty(fstate, ir_idx);
				fstate.stack.push(Value::source(llparam, llty, ir_idx, ty_key))
			}

			IrData::LocalRef(lkey) => {
				// dbg!(lkey);

				let llvar = *fstate.locals.get(lkey).unwrap();
				let llty = self.emit_ty(fstate.func.locals.get(*lkey).unwrap().ty).as_pointer(0);
				let ty_key = self.ir_ty(fstate, ir_idx);
				fstate.stack.push(Value::source(llvar, llty, ir_idx, ty_key))
			}


			IrData::BinaryOp(bin_op) => {
				// dbg!(bin_op);

				let a = fstate.stack.pop().unwrap();
				let b = fstate.stack.pop().unwrap();

				let ty = self.ctx.tys.get(a.ty_key).unwrap();

				assert_eq!(a.lltype, b.lltype);

				let (llvalue, lltype) = self.emit_bin_op(*bin_op, a, b, ty);
				let ty_key = self.ir_ty(fstate, ir_idx);

				if let Some(name) = ir.name.as_deref() {
					llvalue.set_name(LLVMString::from(name));
				}

				fstate.stack.push(Value::source(llvalue, lltype, ir_idx, ty_key))
			}

			IrData::UnaryOp(un_op) => {
				// dbg!(un_op);

				let e = fstate.stack.pop().unwrap();

				let ty = self.ctx.tys.get(e.ty_key).unwrap();

				let (llvalue, lltype) = self.emit_un_op(*un_op, e, ty);
				let ty_key = self.ir_ty(fstate, ir_idx);

				if let Some(name) = ir.name.as_deref() {
					llvalue.set_name(LLVMString::from(name));
				}

				fstate.stack.push(Value::source(llvalue, lltype, ir_idx, ty_key))
			}

			IrData::CastOp(cast_op, target_ty_key) => {
				// dbg!(cast_op, target_ty_key);

				let e = fstate.stack.pop().unwrap();

				let ty = self.ctx.tys.get(e.ty_key).unwrap();
				let target_ty = self.ctx.tys.get(*target_ty_key).unwrap();
				let lltype = self.emit_ty(*target_ty_key);

				let llvalue = self.emit_cast_op(*cast_op, e, ty, target_ty, lltype);
				let ty_key = self.ir_ty(fstate, ir_idx);

				if let Some(name) = ir.name.as_deref() {
					llvalue.set_name(LLVMString::from(name));
				}

				fstate.stack.push(Value::source(llvalue, lltype, ir_idx, ty_key))
			}

			IrData::Gep(gep_num_indices) => {
				// dbg!(gep_num_indices);

				let mut gep_stack = fstate.stack.pop_n_to(*gep_num_indices as usize + 1).unwrap().reversed();

				let Value { llvalue: lltarget, lltype, .. } = gep_stack.pop().unwrap();
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
				let llvalue = self.ll.gep(llbase_ty, lltarget, &indices);

				if let Some(name) = ir.name.as_deref() {
					llvalue.set_name(LLVMString::from(name));
				}

				fstate.stack.push(Value::source(llvalue, llty, ir_idx, ty_key))
			}

			IrData::Load => {
				// dbg!("load");

				let Value { lltype, llvalue: lltarget, .. } = fstate.stack.pop().unwrap();
				assert!(!lltype.get_element_type().is_function_kind()); // TODO: more robust unloadable type check?

				let llvalue = self.ll.load(lltarget);
				let ty_key = self.ir_ty(fstate, ir_idx);

				if let Some(name) = ir.name.as_deref() {
					llvalue.set_name(LLVMString::from(name));
				}

				fstate.stack.push(Value::source(llvalue, lltype.get_element_type(), ir_idx, ty_key))
			}

			IrData::Store => {
				// dbg!("stor");

				let Value { lltype: llptr_ty, llvalue: llptr, .. } = fstate.stack.pop().unwrap();
				let Value { lltype: llval_ty, llvalue: llval, .. } = fstate.stack.pop().unwrap();
				assert_eq!(llptr_ty.get_element_type(), llval_ty);

				self.ll.store(llval, llptr);
			}



			IrData::Call => {
				// dbg!("call");

				if let Some((llval, llty)) = self.emit_call(fstate) {
					let ty_key = self.ir_ty(fstate, ir_idx);

					if let Some(name) = ir.name.as_deref() {
						llval.set_name(LLVMString::from(name));
					}

					fstate.stack.push(Value::source(llval, llty, ir_idx, ty_key))
				}
			}

			IrData::Duplicate(duplicate_idx) => {
				// dbg!(duplicate_idx);

				assert!(fstate.stack.duplicate(*duplicate_idx as usize))
			}

			IrData::Discard(discard_idx) => {
				// dbg!(discard_idx);

				assert!(fstate.stack.discard(*discard_idx as usize))
			}

			IrData::Swap(swap_idx) => {
				// dbg!(swap_idx);

				assert!(fstate.stack.swap(*swap_idx as usize))
			}


			| IrData::Branch { .. }
			| IrData::CondBranch { .. }
			| IrData::Switch { .. }
			| IrData::ComputedBranch { .. }
			| IrData::Ret
			| IrData::Unreachable
			=> unreachable!()
		}

		None
	}

	pub fn emit_terminator_node (&mut self, fstate: &mut EmitterFunctionState, in_val_map: &HashMap<BlockKey, Stack<Value>>, mut out_vals: Stack<Value>) {
		let block = fstate.func.block_data.get(fstate.block_key).unwrap();
		self.position_at_end(fstate.llblock);

		let term = block.ir.last().unwrap();

		let fixup_phis = |dest, out_vals: &Stack<Value>| {
			let in_vals = in_val_map.get(dest).unwrap();
			assert_eq!(out_vals.len(), in_vals.len());

			for (
				&Value { llvalue: llphi, lltype: llin_ty, .. },
				&Value { llvalue: llterm, lltype: llout_ty, .. },
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

				let Value { llvalue, .. } = out_vals.pop().unwrap();

				let lla = *fstate.blocks.get(then_branch).unwrap();
				let llb = *fstate.blocks.get(else_branch).unwrap();
				self.ll.cond_branch(llvalue, lla, llb);

				fixup_phis(then_branch, &out_vals);
				fixup_phis(else_branch, &out_vals);
			}

			IrData::Switch(switch_branches, default_block) => {
				// dbg!(switch_branches, default_block);

				let lldefault = *fstate.blocks.get(default_block).unwrap();
				let Value { llvalue, lltype, .. } = out_vals.pop().unwrap();
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

				let Value { llvalue, lltype, .. } = out_vals.pop().unwrap();

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
			| IrData::SetElement { .. }
			| IrData::GetElement { .. }
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
			| IrData::Duplicate { .. }
			| IrData::Discard { .. }
			| IrData::Swap { .. }
			=> unreachable!()
		}
	}


	pub fn emit_entry (&mut self, fstate: &mut EmitterFunctionState) -> LLVMBlock {
		let lltype = self.emit_ty(fstate.func.ty);
		let abi = self.abi_info(lltype);

		let entry = self.ll.append_basic_block(fstate.llfunc, llvm_str!("abi"));
		self.ll.position_at_end(entry);

		let mut llparams = fstate.llfunc.get_params().into_iter();


		if abi.result.kind == ArgKind::Indirect {
			let sret_param = llparams.next().unwrap();
			sret_param.set_name(llvm_str!("sret_val"));
			fstate.sret = Some(sret_param);
		}


	 	for (abi_arg, param_key) in abi.args.iter().zip(fstate.func.param_order.iter()) {
			let param = match abi_arg.kind {
				ArgKind::Direct => {
					let alloca = self.ll.alloca(abi_arg.base_type);
					let mut abi_ptr = alloca;

					let llvalue = if let Some(ArgAttr::ZExt) = abi_arg.attribute {
						debug_assert!(abi_arg.base_type == LLVMType::int8(self.ll.ctx));
						self.ll.itrunc(llparams.next().unwrap(), LLVMType::int1(self.ll.ctx))
					} else if abi_arg.cast_types.is_empty() {
						llparams.next().unwrap()
					} else {
						let cast_ty = LLVMType::anonymous_structure(self.ll.ctx, &abi_arg.cast_types, false);
						let mut agg = LLVMValue::zero(cast_ty);
						for i in 0..abi_arg.cast_types.len() as u32 {
							let llparam = llparams.next().unwrap();

							agg = self.ll.insert_value(agg, llparam, i);
						}

						abi_ptr = self.ll.bitcast(abi_ptr, cast_ty.as_pointer(0));

						agg
					};

					self.ll.store(llvalue, abi_ptr);

					alloca
				},

				ArgKind::Indirect => {
					llparams.next().unwrap()
				}
			};

			if let Some(name) = fstate.func.param_data.get(*param_key).unwrap().name.as_deref() {
				param.set_name(LLVMString::from(name))
			}

			fstate.params.insert(*param_key, param);
		}


		for (&local_key, local) in fstate.func.locals.iter() {
			let lltype = self.emit_ty(local.ty);
			let lllocal = self.alloca(lltype);

			if let Some(name) = local.name.as_deref() {
				lllocal.set_name(LLVMString::from(name))
			}

			fstate.locals.insert(local_key, lllocal);
		}


		entry
	}


	pub fn emit_return (&mut self, fstate: &mut EmitterFunctionState, mut stack: Stack<Value>) -> LLVMValue {
		let lltype = self.emit_ty(fstate.func.ty);
		let abi = self.abi_info(lltype);

		let val = match abi.result.kind {
			ArgKind::Direct => {
				if abi.result.base_type == LLVMType::void(self.ll.ctx) {
					self.ll.ret_void()
				} else {
					let Value { llvalue: base_llvalue, .. } = stack.pop().unwrap();

					let llvalue = if abi.result.attribute == Some(ArgAttr::ZExt) {
						debug_assert!(abi.result.base_type == LLVMType::int1(self.ll.ctx));
						self.ll.zext(base_llvalue, LLVMType::int8(self.ll.ctx))
					} else if abi.result.cast_types.is_empty() {
						base_llvalue
					} else {
						let arg_ty =
							if abi.result.cast_types.len() == 1 {
								*abi.result.cast_types.first().unwrap()
							} else {
								LLVMType::anonymous_structure(self.ll.ctx, &abi.result.cast_types, false)
							};

						let alloca = self.ll.alloca(arg_ty);
						let cast = self.ll.bitcast(alloca, abi.result.base_type.as_pointer(0));

						self.ll.store(base_llvalue, cast);

						self.ll.load(alloca)
					};

					self.ll.ret(llvalue)
				}
			}

			ArgKind::Indirect => {
				let Value { llvalue: base_llvalue, .. } = stack.pop().unwrap();
				self.store(base_llvalue, fstate.sret.unwrap());

				self.ll.ret_void()
			}
		};

		assert!(stack.is_empty());

		val
	}



	pub fn emit_call (&mut self, fstate: &mut EmitterFunctionState<'a>) -> Option<(LLVMValue, LLVMType)> {
		let Value { llvalue, mut lltype, .. } = fstate.stack.pop().unwrap();

		if lltype.is_pointer_kind() { lltype = lltype.get_element_type() }

		assert!(lltype.is_function_kind());

		let abi = self.abi_info(lltype);
		debug_assert_eq!(lltype, abi.lltype);
		debug_assert_eq!(lltype.count_param_types() as usize, abi.args.len());



		let mut llargs: Vec<LLVMValue> = vec![];

		for abi_arg in abi.args.iter().rev() {
			let Value { lltype: base_lltype, llvalue: base_llvalue, .. }
				= fstate.stack.pop().unwrap();

			assert_eq!(base_lltype, abi_arg.base_type);

			let value = match abi_arg.kind {
				ArgKind::Direct => {
					if let Some(ArgAttr::ZExt) = abi_arg.attribute {
						debug_assert!(abi_arg.base_type == LLVMType::int1(self.ll.ctx));
						self.ll.zext(base_llvalue, LLVMType::int8(self.ll.ctx))
					} else if abi_arg.cast_types.is_empty() {
						base_llvalue
					} else {
						let arg_struct = LLVMType::anonymous_structure(self.ll.ctx, &abi_arg.cast_types, false);

						self.ll.bitcast(base_llvalue, arg_struct)
					}
				}

				ArgKind::Indirect => {
					let llslot = self.ll.alloca(abi_arg.base_type.as_pointer(0));

					self.ll.store(llslot, base_llvalue)
				}
			};

			if abi_arg.cast_types.len() > 1 {
				for i in 0..abi_arg.cast_types.len() as u32 {
					llargs.push(self.ll.extract_value(value, i))
				}
			} else {
				llargs.push(value);
			}
		}



		if abi.result.kind == ArgKind::Indirect {
			let llvalue = self.ll.alloca(abi.result.base_type);

			llargs.push(llvalue);
		}



		llargs.reverse();
		let result = self.ll.call(abi.lltype, llvalue, llargs.as_slice());

		if abi.result.base_type.is_void_kind() { return None }

		let (llvalue, lltype) = match abi.result.kind {
			ArgKind::Indirect => {
				let load = self.ll.load(result);
				(load, abi.result.base_type)
			}

			ArgKind::Direct => {
				(if abi.result.cast_types.is_empty() {
					result
				} else {
					self.ll.bitcast(result, abi.result.base_type)
				}, abi.result.base_type)
			}
		};

		Some((llvalue, lltype))
	}



	pub fn emit_bin_op (&self, bin_op: BinaryOp, a: Value, b: Value, ty: &'a Ty) -> (LLVMValue, LLVMType) {
		use BinaryOp::*;

		let int1 = LLVMType::int1(self.ll.ctx);

		match bin_op {
			Add if ty.is_int()
			=> (self.ll.iadd(a.llvalue, b.llvalue), a.lltype),
			Sub if ty.is_int()
			=> (self.ll.isub(a.llvalue, b.llvalue), a.lltype),
			Mul if ty.is_int()
			=> (self.ll.imul(a.llvalue, b.llvalue), a.lltype),
			Div if ty.is_int()
			=> (self.ll.idiv(ty.is_signed(), a.llvalue, b.llvalue), a.lltype),
			Rem if ty.is_int()
			=> (self.ll.irem(ty.is_signed(), a.llvalue, b.llvalue), a.lltype),



			Add if ty.is_real()
			=> (self.ll.fadd(a.llvalue, b.llvalue), a.lltype),
			Sub if ty.is_real()
			=> (self.ll.fsub(a.llvalue, b.llvalue), a.lltype),
			Mul if ty.is_real()
			=> (self.ll.fmul(a.llvalue, b.llvalue), a.lltype),
			Div if ty.is_real()
			=> (self.ll.fdiv(a.llvalue, b.llvalue), a.lltype),
			Rem if ty.is_real()
			=> (self.ll.frem(a.llvalue, b.llvalue), a.lltype),




			Eq if ty.is_bool() || ty.is_int()
			=> (self.ll.icmp(LLVMIntEQ, a.llvalue, b.llvalue), int1),
			Ne if ty.is_bool() || ty.is_int()
			=> (self.ll.icmp(LLVMIntNE, a.llvalue, b.llvalue), int1),

			Eq if ty.is_real()
			=> (self.ll.fcmp(LLVMRealUEQ, a.llvalue, b.llvalue), int1),
			Ne if ty.is_real()
			=> (self.ll.fcmp(LLVMRealUNE, a.llvalue, b.llvalue), int1),

			Eq if ty.is_pointer() => {
				let intptr = self.abi.llvm_pointer_int(self.ll.ctx);
				let lla = self.ll.i2p(a.llvalue, intptr);
				let llb = self.ll.i2p(b.llvalue, intptr);
				(self.ll.icmp(LLVMIntEQ, lla, llb), int1)
			}
			Ne if ty.is_pointer() => {
				let intptr = self.abi.llvm_pointer_int(self.ll.ctx);
				let lla = self.ll.i2p(a.llvalue, intptr);
				let llb = self.ll.i2p(b.llvalue, intptr);
				(self.ll.icmp(LLVMIntNE, lla, llb), int1)
			}

			Eq if ty.is_function() => { todo!() } // TODO: function comparison
			Ne if ty.is_function() => { todo!() }



			Lt if ty.is_int()
			=> (self.ll.icmp(if ty.is_signed() { LLVMIntSLT } else { LLVMIntULT }, a.llvalue, b.llvalue), int1),
			Gt if ty.is_int()
			=> (self.ll.icmp(if ty.is_signed() { LLVMIntSGT } else { LLVMIntUGT }, a.llvalue, b.llvalue), int1),
			Le if ty.is_int()
			=> (self.ll.icmp(if ty.is_signed() { LLVMIntSLE } else { LLVMIntULE }, a.llvalue, b.llvalue), int1),
			Ge if ty.is_int()
			=> (self.ll.icmp(if ty.is_signed() { LLVMIntSGE } else { LLVMIntUGE }, a.llvalue, b.llvalue), int1),

			Lt if ty.is_real()
			=> (self.ll.fcmp(LLVMRealOLT, a.llvalue, b.llvalue), int1),
			Gt if ty.is_real()
			=> (self.ll.fcmp(LLVMRealOGT, a.llvalue, b.llvalue), int1),
			Le if ty.is_real()
			=> (self.ll.fcmp(LLVMRealOLE, a.llvalue, b.llvalue), int1),
			Ge if ty.is_real()
			=> (self.ll.fcmp(LLVMRealOGE, a.llvalue, b.llvalue), int1),


			LAnd if ty.is_bool()
			=> (self.ll.and(a.llvalue, b.llvalue), a.lltype),
			LOr if ty.is_bool()
			=> (self.ll.or(a.llvalue, b.llvalue), a.lltype),


			BAnd if ty.is_int()
			=> (self.ll.and(a.llvalue, b.llvalue), a.lltype),
			BOr if ty.is_int()
			=> (self.ll.or(a.llvalue, b.llvalue), a.lltype),
			BXor
			=> (self.ll.xor(a.llvalue, b.llvalue), a.lltype),

			LSh
			=> (self.ll.l_shift(a.llvalue, b.llvalue), a.lltype),
			RShA
			=> (self.ll.arithmetic_r_shift(a.llvalue, b.llvalue), a.lltype),
			RShL
			=> (self.ll.logical_r_shift(a.llvalue, b.llvalue), a.lltype),

			_ => unreachable!()
		}
	}


	pub fn emit_un_op (&self, un_op: UnaryOp, e: Value, ty: &'a Ty) -> (LLVMValue, LLVMType) {
		use UnaryOp::*;

		match un_op {
			Neg if ty.is_sint()
			=> (self.ll.ineg(e.llvalue), e.lltype),

			Neg if ty.is_real()
			=> (self.ll.fneg(e.llvalue), e.lltype),

			LNot if ty.is_bool()
			=> (self.ll.not(e.llvalue), e.lltype),

			BNot if ty.is_int()
			=> (self.ll.not(e.llvalue), e.lltype),


			_ => unreachable!()
		}
	}

	pub fn emit_cast_op (&self, cast_op: CastOp, e: Value, ty: &'a Ty, target_ty: &'a Ty, lltgt_ty: LLVMType) -> LLVMValue {
		use CastOp::*;

		match cast_op {
			IntToReal if ty.is_int() && target_ty.is_real()
			=> self.ll.i2f(ty.is_signed(), e.llvalue, lltgt_ty),

			RealToInt if ty.is_real() && target_ty.is_int()
			=> self.ll.f2i(target_ty.is_signed(), e.llvalue, lltgt_ty),

			ZeroExtend if ty.is_int() && target_ty.is_int()
			=> self.ll.zext(e.llvalue, lltgt_ty),

			SignExtend if ty.is_int() && target_ty.is_int()
			=> self.ll.sext(e.llvalue, lltgt_ty),

			RealExtend if ty.is_real() && target_ty.is_real()
			=> self.ll.fext(e.llvalue, lltgt_ty),

			Truncate if ty.is_int() && target_ty.is_int()
			=> self.ll.itrunc(e.llvalue, lltgt_ty),

			RealTruncate if ty.is_real() && target_ty.is_real()
			=> self.ll.ftrunc(e.llvalue, lltgt_ty),

			Bitcast if ty.is_primitive() || ty.is_pointer()
			=> self.ll.bitcast(e.llvalue, lltgt_ty),

			Bitcast if ty.is_aggregate()
			=> {
				let alloca = self.ll.alloca(e.lltype.as_pointer(0));
				self.ll.store(e.llvalue, alloca);
				let cast = self.ll.bitcast(alloca, lltgt_ty.as_pointer(0));
				self.ll.load(cast)
			}

			_ => unreachable!()
		}
	}
}