use std::{collections::HashMap, mem};

use support::{
	slotmap::{ AsKey, Keyed },
	stack::Stack,
	utils::assert,
};


use super::{
	ir::*,
	cfg::*,
	ty::*,
	builder::*,
};



#[derive(Debug, Default)]
pub struct OpStack {
	entries: Stack<(TyKey, Option<Constant>)>
}

impl OpStack {
	pub fn len (&self) -> usize {
		self.entries.len()
	}

	pub fn is_empty (&self) -> bool {
		self.entries.is_empty()
	}

	pub fn push<K: AsKey<TyKey>> (&mut self, ty: K) {
		self.entries.push((ty.as_key(), None))
	}

	pub fn push_constant<K: AsKey<TyKey>> (&mut self, ty: K, c: Constant) {
		self.entries.push((ty.as_key(), Some(c)))
	}

	pub fn pop (&mut self) -> IrDataResult<TyKey> {
		Ok(
			self.entries
				.pop()
				.map(|(ty, _)| ty)
				.ok_or(TyErr::StackUnderflow)?
		)
	}

	pub fn pop_constant (&mut self) -> IrDataResult<(TyKey, Constant)> {
		Ok(
			self.entries
				.pop()
				.ok_or(TyErr::StackUnderflow)
				.and_then(|(ty, c)|
					c
						.ok_or(TyErr::ExpectedConstant)
						.map(|c| (ty, c))
				)?
		)
	}

	pub fn peek_at (&mut self, at: usize) -> IrDataResult<TyKey> {
		Ok(
			self.entries
				.peek_at(at)
				.map(|(ty, _)| *ty)
				.ok_or(TyErr::StackUnderflow)?
		)
	}

	pub fn peek_constant_at (&mut self, at: usize) -> IrDataResult<(TyKey, &Constant)> {
		Ok(
			self.entries
				.peek_at(at)
				.ok_or(TyErr::StackUnderflow)
				.and_then(|(ty, c)|
					c
						.as_ref()
						.ok_or(TyErr::ExpectedConstant)
						.map(|c| (*ty, c))
				)?
		)
	}

	pub fn pop_n (&mut self, n: usize) -> bool {
		self.entries.pop_n(n)
	}

	pub fn pop_n_to (&mut self, n: usize) -> IrDataResult<OpStack> {
		Ok(Self { entries: self.entries.pop_n_to(n).ok_or(TyErr::StackUnderflow)? })
	}

	pub fn nth_is_constant (&mut self, at: usize) -> bool {
		self.entries
			.peek_at(at)
			.and_then(|(_, c)| c.as_ref())
			.is_some()
	}

	pub fn duplicate (&mut self, at: usize) -> IrDataResult {
		if self.entries.duplicate(at) {
			Ok(())
		} else {
			Err(TyErr::StackUnderflow.into())
		}
	}

	pub fn swap (&mut self, at: usize) -> IrDataResult {
		if self.entries.swap(at) {
			Ok(())
		} else {
			Err(TyErr::StackUnderflow.into())
		}
	}

	pub fn discard (&mut self, at: usize) -> IrDataResult {
		if self.entries.discard(at) {
			Ok(())
		} else {
			Err(TyErr::StackUnderflow.into())
		}
	}

	pub fn top_is_constant (&mut self) -> bool {
		self.entries
			.peek()
			.and_then(|(_, c)| c.as_ref())
			.is_some()
	}


	pub fn take (&mut self) -> Vec<TyKey> {
		mem::take(&mut self.entries)
			.into_inner()
			.into_iter()
			.map(|(ty, _)| ty)
			.collect()
	}

	pub fn reverse (&mut self) {
		self.entries.reverse()
	}

	pub fn reversed (mut self) -> Self {
		self.reverse();
		self
	}
}



#[derive(Debug, Clone, Default)]
pub struct TyMap {
	data: HashMap<(BlockKey, usize), TyKey>,
}

impl TyMap {
	#[cfg_attr(debug_assertions, track_caller)]
	pub(crate) fn set (&mut self, block_key: impl AsKey<BlockKey>, index: usize, ty_key: impl AsKey<TyKey>) {
		assert!(self.data.insert((block_key.as_key(), index), ty_key.as_key()).is_none());
	}

	#[cfg_attr(debug_assertions, track_caller)]
	pub fn get (&self, block_key: BlockKey, index: usize) -> TyKey {
		let x = self.data.get(&(block_key, index)).copied();

		if cfg!(debug_assertions) {
			match x {
				Some(tk) => tk,
				None => {
					panic!("Cannot get validator type for {:?} : {}\n from {:#?}", block_key, index, self.data);
				}
			}
		} else {
			x.unwrap()
		}
	}
}


#[derive(Debug)]
pub struct TyChecker<'r, 'b, 'f> {
	pub builder: &'r mut Builder<'b>,
	pub cfg: Cfg,
	pub function: Option<&'f Function>,
	pub stack: OpStack,
	pub ty_map: TyMap,
}


impl<'r, 'b, 'f> TyChecker<'r, 'b, 'f> {
	pub fn for_function (builder: &'r mut Builder<'b>, cfg: Cfg, function: &'f Function) -> Self {
		Self {
			builder,
			cfg,
			function: Some(function),
			stack: OpStack::default(),
			ty_map: TyMap::default(),
		}
	}


	pub fn for_global (builder: &'r mut Builder<'b>) -> Self {
		Self {
			builder,
			cfg: Cfg::default(),
			function: None,
			stack: OpStack::default(),
			ty_map: TyMap::default(),
		}
	}



	pub fn get_block<K: AsKey<BlockKey>> (&self, block_key: K) -> IrDataResult<Keyed<'f, Block>> {
		let block_key = block_key.as_key();
		let block = self.function.unwrap().block_data.get_keyed(block_key).ok_or(IrErrData::InvalidBlockKey(block_key))?;

		Ok(block)
	}

	pub fn get_param<K: AsKey<ParamKey>> (&self, param_key: K) -> IrDataResult<Keyed<'f, Param>> {
		let param_key = param_key.as_key();
		let param = self.function.unwrap().param_data.get_keyed(param_key).ok_or(IrErrData::InvalidParamKey(param_key))?;

		Ok(param)
	}

	pub fn get_local<K: AsKey<LocalKey>> (&self, local_key: K) -> IrDataResult<Keyed<'f, Local>> {
		let local_key = local_key.as_key();
		let local = self.function.unwrap().locals.get_keyed(local_key).ok_or(IrErrData::InvalidLocalKey(local_key))?;

		Ok(local)
	}



	pub fn ty_ck<KA: AsKey<TyKey>, KB: AsKey<TyKey>> (&self, expected: KA, found: KB) -> bool {
		let expected = self.builder.get_ty(expected).unwrap();
		let found = self.builder.get_ty(found).unwrap();

		expected.equivalent(found.as_ref())
	}


	pub fn validate_aggregate_index (&self, ty: Keyed<Ty>, idx: u32) -> TyResult<TyKey> {
		match &ty.data {
			TyData::Array { length, element_ty } => if idx < *length { Some(*element_ty) } else { None },
			TyData::Structure { field_tys } => field_tys.get(idx as usize).copied(),
			_ => return Err(TyErr::ExpectedAggregateTy(ty.as_key()))
		}.ok_or_else(|| TyErr::InvalidAggregateIndex(ty.as_key(), idx))
	}

	pub fn validate_aggregate_element<K: AsKey<TyKey>> (&self, ty: Keyed<Ty>, idx: u32, ty_key: K) -> TyResult {
		let ty_key = ty_key.as_key();

		match &ty.data {
			&TyData::Array { length, element_ty } => {
				assert(idx < length, TyErr::InvalidAggregateIndex(ty.as_key(), idx))?;
				assert(self.ty_ck(element_ty, ty_key), TyErr::ExpectedAggregateElementTy(ty.as_key(), idx, element_ty, ty_key))?;
			}


			TyData::Structure { field_tys } => {
				let field_ty = *field_tys.get(idx as usize).ok_or_else(|| TyErr::InvalidAggregateIndex(ty.as_key(), idx))?;
				assert(self.ty_ck(field_ty, ty_key), TyErr::ExpectedAggregateElementTy(ty.as_key(), idx, field_ty, ty_key))?;
			}

			_ => return Err(TyErr::ExpectedAggregateTy(ty.as_key())),
		}

		Ok(())
	}

	pub fn extract_pointer_target (&self, ty: Keyed<Ty>) -> IrDataResult<TyKey> {
		if let TyData::Pointer { target_ty } = &ty.data  {
			Ok(self.builder.get_finalized_ty(target_ty)?.as_key())
		} else {
			Err(TyErr::ExpectedPointer(ty.as_key()).into())
		}
	}


	pub fn check_bin_op<'x> (&'x self, op: BinaryOp, ty: Keyed<'x, Ty>) -> IrDataResult<Keyed<'x, Ty>> {
		let ty_key = ty.as_key();

		let invalid_operand_err = TyErr::BinaryOpInvalidOperandTy(op, ty_key);

		assert(ty.is_scalar(), invalid_operand_err)?;

		use BinaryOp::*;

		Ok(match op {
			Add | Sub | Mul | Div | Rem
			=> {
				assert(ty.is_arithmetic(), invalid_operand_err)?;
				ty
			}

			Lt | Gt | Le | Ge
			=> {
				assert(ty.is_arithmetic(), invalid_operand_err)?;
				self.builder.bool_ty()
			}

			Eq | Ne
			=> {
				assert(ty.has_equality(), invalid_operand_err)?;
				self.builder.bool_ty()
			}

			LAnd | LOr
			=> {
				assert(ty.is_bool(), invalid_operand_err)?;
				ty
			}

			BAnd | BOr | BXor | LSh | RShA | RShL
			=> {
				assert(ty.is_int(), invalid_operand_err)?;
				ty
			}
		})
	}

	pub fn check_un_op<'x> (&'x self, op: UnaryOp, ty: Keyed<'x, Ty>) -> IrDataResult<Keyed<'x, Ty>> {
		let ty_key = ty.as_key();

		let invalid_operand_err = TyErr::UnaryOpInvalidOperandTy(op, ty_key);

		assert(ty.is_scalar(), invalid_operand_err)?;

		use UnaryOp::*;

		Ok(match op {
			Neg
			=> {
				assert(ty.is_signed(), invalid_operand_err)?;
				ty
			}

			LNot
			=> {
				assert(ty.is_bool(), invalid_operand_err)?;
				ty
			}

			BNot
			=> {
				assert(ty.is_int(), invalid_operand_err)?;
				ty
			}
		})
	}

	pub fn check_cast_op (&self, op: CastOp, curr_ty: Keyed<Ty>, new_ty: Keyed<Ty>) -> IrDataResult {
		let curr_ty_key = curr_ty.as_key();
		let new_ty_key = new_ty.as_key();

		use CastOp::*;

		assert(match op {
			IntToReal
			=> curr_ty.is_int()
			&& new_ty.is_real(),

			RealToInt
			=> curr_ty.is_real()
			&& new_ty.is_int(),

			ZeroExtend
			=> curr_ty.is_int()
			&& new_ty.is_int()
			&& self.builder.size_of(new_ty)? > self.builder.size_of(curr_ty)?,

			SignExtend
			=> self.builder.size_of(new_ty)? > self.builder.size_of(curr_ty)?
			&& (
					 (curr_ty.is_int() && new_ty.is_int())
				|| (curr_ty.is_real() && new_ty.is_real())
			),

			RealExtend
			=> curr_ty.is_real()
			&& new_ty.is_real()
			&& self.builder.size_of(new_ty)? > self.builder.size_of(curr_ty)?,

			Truncate
			=> self.builder.size_of(curr_ty)? > self.builder.size_of(new_ty)?
			&& (
					 (curr_ty.is_int()  && new_ty.is_int())
				|| (curr_ty.is_real() && new_ty.is_real())
			),

			RealTruncate
			=> curr_ty.is_real()
			&& new_ty.is_real()
			&& self.builder.size_of(curr_ty)? > self.builder.size_of(new_ty)?,

			Bitcast
			=> (curr_ty.is_primitive() || curr_ty.is_pointer() || curr_ty.is_aggregate())
			&& (new_ty.is_primitive() || new_ty.is_pointer() || new_ty.is_aggregate())
			&& self.builder.size_of(curr_ty)? == self.builder.size_of(new_ty)?
		}, TyErr::InvalidCast(op, curr_ty_key, new_ty_key).into())
	}



	pub fn get_constant_ty (&self, constant: &Constant) -> IrDataResult<Keyed<Ty>> {
		use Constant::*;

		Ok(match constant {
			Null(ty_key)
			=> {
				let ty = self.builder.get_finalized_ty(ty_key)?;

				if !ty.is_pointer() {
					return Err(TyErr::ExpectedPointer(ty.as_key()).into())
				}

				ty
			}

			Bool(_)
			=> { self.builder.bool_ty() }

			SInt8(_)
			=> { self.builder.sint8_ty() }

			SInt16(_)
			=> { self.builder.sint16_ty() }

			SInt32(_)
			=> { self.builder.sint32_ty() }

			SInt64(_)
			=> { self.builder.sint64_ty() }

			SInt128(_)
			=> { self.builder.sint128_ty() }

			UInt8(_)
			=> { self.builder.uint8_ty() }

			UInt16(_)
			=> { self.builder.uint16_ty() }

			UInt32(_)
			=> { self.builder.uint32_ty() }

			UInt64(_)
			=> { self.builder.uint64_ty() }

			UInt128(_)
			=> { self.builder.uint128_ty() }

			Real32(_)
			=> { self.builder.real32_ty() }

			Real64(_)
			=> { self.builder.real64_ty() }

			Aggregate(ty_key, agg_data)
			=> {
				let ty = self.builder.get_finalized_ty(ty_key)?;

				assert(ty.is_aggregate(), TyErr::ExpectedAggregateTy(ty.as_key()))?;

				match agg_data {
					| ConstantAggregateData::Zeroed
					| ConstantAggregateData::Uninitialized
					=> { }

					ConstantAggregateData::CopyFill(operand)
					=> {
						let operand_ty = self.get_constant_ty(operand)?;

						match &ty.data {
							TyData::Array { element_ty, .. } => {
								assert(self.ty_ck(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(*ty_key, 0, *element_ty, operand_ty.as_key()))?;
							}

							TyData::Structure { field_tys } => {
								for (i, field_ty) in field_tys.iter().enumerate() {
									assert(self.ty_ck(field_ty, operand_ty), TyErr::ExpectedAggregateElementTy(*ty_key, i as _, *field_ty, operand_ty.as_key()))?;
								}
							}

							_ => return Err(TyErr::ExpectedArray(ty.as_key()).into())
						}
					}

					ConstantAggregateData::Complete(elements)
					=> {
						match &ty.data {
							&TyData::Array { length, element_ty } => {
								for i in 0..length {
									let operand = elements.get(i as usize).ok_or(TyErr::MissingAggregateElement(*ty_key, i))?;
									let operand_ty = self.get_constant_ty(operand)?;

									assert(self.ty_ck(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(*ty_key, i, element_ty, operand_ty.as_key()))?;
								}
							},

							TyData::Structure { field_tys } => {
								for (i, &field_ty) in field_tys.iter().enumerate() {
									let operand = elements.get(i).ok_or(TyErr::MissingAggregateElement(*ty_key, i as u32))?;
									let operand_ty = self.get_constant_ty(operand)?;

									assert(self.ty_ck(field_ty, operand_ty), TyErr::ExpectedAggregateElementTy(*ty_key, i as u32, field_ty, operand_ty.as_key()))?;
								}
							}

							_ => unreachable!()
						}
					}

					ConstantAggregateData::Indexed(indexed_elements)
					=> {
						for (x, &(i, _)) in indexed_elements.iter().enumerate() {
							for (y, &(j, _)) in indexed_elements.iter().enumerate() {
								if x == y { continue }
								assert(i != j, TyErr::DuplicateAggregateIndex(x, y, i))?;
							}
						}

						match &ty.data {
							&TyData::Array { length, element_ty } => {
								for &(i, ref operand) in indexed_elements.iter() {
									assert(i < length, TyErr::InvalidAggregateIndex(*ty_key, i))?;

									let operand_ty = self.get_constant_ty(operand)?;

									assert(self.ty_ck(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(*ty_key, i, element_ty, operand_ty.as_key()))?;
								}
							},

							TyData::Structure { field_tys } => {
								for &(i, ref operand) in indexed_elements.iter() {
									let field_ty = *field_tys.get(i as usize).ok_or(TyErr::InvalidAggregateIndex(*ty_key, i))?;
									let operand_ty = self.get_constant_ty(operand)?;

									assert(self.ty_ck(field_ty, operand_ty), TyErr::ExpectedAggregateElementTy(*ty_key, i, field_ty, operand_ty.as_key()))?;
								}
							}

							_ => unreachable!()
						}
					}
				}

				ty
			}
		})
	}

	pub fn check_node (&mut self, parent: Keyed<Block>, node: &Ir, node_idx: usize) -> IrDataResult {
		use IrData::*;

		match &node.data {
			Constant(constant)
			=> {
				let ty = self.get_constant_ty(constant)?.as_key();
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.stack.push_constant(ty, constant.clone())
			}

			BuildAggregate(ty_key, agg_data)
			=> {
				let ty = self.builder.get_finalized_ty(ty_key)?;
				self.ty_map.set(parent.as_key(), node_idx, ty);


				assert(ty.is_aggregate(), TyErr::ExpectedAggregateTy(ty.as_key()))?;

				match agg_data {
					| AggregateData::Zeroed
					| AggregateData::Uninitialized
					=> { }

					AggregateData::CopyFill
					=> {
						let operand_ty = self.stack.pop()?;

						if let TyData::Array { element_ty, .. } = ty.data {
							assert(self.ty_ck(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(*ty_key, 0, element_ty, operand_ty.as_key()))?;
						} else {
							return Err(TyErr::ExpectedArray(ty.as_key()).into())
						}
					}

					AggregateData::Complete
					=> {
						match &ty.data {
							&TyData::Array { length, element_ty } => {
								for i in 0..length {
									let operand_ty = self.stack.pop()?;

									assert(self.ty_ck(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(*ty_key, i, element_ty, operand_ty))?;
								}
							},

							TyData::Structure { field_tys } => {
								for (i, &field_ty) in field_tys.iter().enumerate() {
									let operand_ty = self.stack.pop()?;

									assert(self.ty_ck(field_ty, operand_ty), TyErr::ExpectedAggregateElementTy(*ty_key, i as u32, field_ty, operand_ty))?;
								}
							}

							_ => unreachable!()
						}
					}

					AggregateData::Indexed(indices)
					=> {
						for (x, &i) in indices.iter().enumerate() {
							for (y, &j) in indices.iter().enumerate() {
								if x == y { continue }
								assert(i != j, TyErr::DuplicateAggregateIndex(x, y, i))?;
							}
						}

						match &ty.data {
							&TyData::Array { length, element_ty } => {
								for &i in indices.iter() {
									assert(i < length, TyErr::InvalidAggregateIndex(*ty_key, i))?;

									let operand_ty = self.stack.pop()?;

									assert(self.ty_ck(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(*ty_key, i, element_ty, operand_ty))?;
								}
							},

							TyData::Structure { field_tys } => {
								for &i in indices.iter() {
									let field_ty = *field_tys.get(i as usize).ok_or(TyErr::InvalidAggregateIndex(*ty_key, i))?;
									let operand_ty = self.stack.pop()?;

									assert(self.ty_ck(field_ty, operand_ty), TyErr::ExpectedAggregateElementTy(*ty_key, i as u32, field_ty, operand_ty))?;
								}
							}

							_ => unreachable!()
						}
					}
				}

				self.stack.push(ty)
			}

			SetElement(index) => {
				let elem = self.stack.pop()?;

				let agg = self.stack.pop()?;
				let agg_ty = self.builder.get_ty(agg)?;

				self.validate_aggregate_element(agg_ty, *index, elem)?;

				self.ty_map.set(parent.as_key(), node_idx, agg_ty);

				self.stack.push(agg)
			}

			GetElement(index) => {
				let agg = self.stack.pop()?;
				let agg_ty = self.builder.get_ty(agg)?;

				let elem = self.validate_aggregate_index(agg_ty, *index)?;

				self.ty_map.set(parent.as_key(), node_idx, elem);

				self.stack.push(elem)
			}

			GlobalRef(global_key)
			=> {
				let global = self.builder.get_global(global_key)?;
				let ty = self.builder.get_finalized_ty(global.ty)?.as_key();
				let ty = self.builder.pointer_ty(ty)?.as_key();
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.stack.push(ty)
			}

			FunctionRef(function_key)
			=> {
				let function = self.builder.get_function(function_key)?;
				let ty = self.builder.get_finalized_ty(function.ty)?;
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.stack.push(ty)
			}

			BlockRef(block_key)
			=> {
				let ty = self.builder.block_ty();
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.get_block(block_key)?;

				self.stack.push(ty)
			}

			ParamRef(param_key)
			=> {
				let param = self.get_param(param_key)?;
				let ty = self.builder.get_finalized_ty(param.ty)?.as_key();
				let ty = self.builder.pointer_ty(ty)?.as_key();
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.stack.push(ty)
			}

			LocalRef(local_key)
			=> {
				let local = self.get_local(local_key)?;
				let ty = self.builder.get_finalized_ty(local.ty)?.as_key();
				let ty = self.builder.pointer_ty(ty)?.as_key();
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.stack.push(ty)
			}

			Phi(ty_key)
			=> {
				let ty = self.builder.get_finalized_ty(ty_key)?.as_key();
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.cfg.add_in_value(parent, ty).unwrap();

				self.stack.push(ty)
			}

			BinaryOp(op)
			=> {
				let left = self.builder.get_ty(self.stack.pop()?)?;
				let right = self.stack.pop()?;

				assert(self.ty_ck(left, right), TyErr::BinaryOpTypeMismatch(left.as_key(), right))?;
				let ty = self.check_bin_op(*op, left)?.as_key();
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.stack.push(ty)
			}

			UnaryOp(op)
			=> {
				let operand = self.builder.get_ty(self.stack.pop()?)?;
				let ty = self.check_un_op(*op, operand)?.as_key();
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.stack.push(ty)
			}

			CastOp(op, ty_key)
			=> {
				let operand = self.builder.get_ty(self.stack.pop()?)?;
				let ty = self.builder.get_finalized_ty(ty_key)?;
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.check_cast_op(*op, operand, ty)?;

				self.stack.push(ty)
			}

			Gep(num_indices)
			=> {
				assert(*num_indices > 0, TyErr::GepNoIndices)?;

				let mut gep_stack = self.stack.pop_n_to(*num_indices as usize + 1)?.reversed();

				let target = self.builder.get_ty(gep_stack.pop()?)?;
				assert(target.is_pointer(), TyErr::GepTargetNotPointer(target.as_key()))?;

				let ptr_index = self.builder.get_ty(gep_stack.pop()?)?;
				assert(ptr_index.is_int(), TyErr::GepInvalidIndex(0, ptr_index.as_key()))?;


				let mut target = self.builder.get_ty(self.extract_pointer_target(target)?)?;


				for n in 1..*num_indices as usize {
					match &target.data {
						TyData::Array { length, element_ty } => {
							if self.stack.top_is_constant() {
								let (ty, constant) = gep_stack.pop_constant()?;

								let index = constant.as_index().ok_or(TyErr::ExpectedInteger(ty))?;

								assert(index <= *length, TyErr::GepOutOfBounds(n, target.as_key(), *length, index))?
							} else {
								let index = self.builder.get_ty(gep_stack.pop()?)?;

								assert(index.is_int(), TyErr::GepInvalidIndex(n, index.as_key()))?;
							}

							target = self.builder.get_finalized_ty(element_ty)?
						}

						TyData::Structure { field_tys } => {
							let (ty, constant) = gep_stack.pop_constant()?;

							let index = constant.as_index().ok_or(TyErr::ExpectedInteger(ty))?;

							let field_ty = field_tys.get(index as usize).ok_or_else(|| TyErr::GepOutOfBounds(n, target.as_key(), field_tys.len() as u32, index))?;

							target = self.builder.get_finalized_ty(field_ty)?
						}

						TyData::Pointer { .. } => return Err(TyErr::GepImplicitLoad(n, target.as_key()).into()),

						_ => return Err(TyErr::GepInvalidSubElement(n, target.as_key()).into())
					}
				}


				let target = target.as_key();
				let ty = self.builder.pointer_ty(target)?.as_key();
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.stack.push(ty)
			}

			Load
			=> {
				let target = self.builder.get_ty(self.stack.pop()?)?;
				let ty = self.extract_pointer_target(target)?;
				self.ty_map.set(parent.as_key(), node_idx, ty);

				self.stack.push(ty)
			}

			Store
			=> {
				let target = self.builder.get_ty(self.stack.pop()?)?;
				let target_ty = self.extract_pointer_target(target)?;

				let ty = self.builder.get_ty(self.stack.pop()?)?;
				self.ty_map.set(parent.as_key(), node_idx, ty);

				assert(self.ty_ck(target_ty, ty), TyErr::ExpectedTy(target_ty, ty.as_key()))?;

				self.stack.push(ty)
			}

			Branch(_)
			=> {
				self.set_out_values(parent)
			}


			CondBranch(_, _)
			=> {
				let pred = self.builder.get_ty(self.stack.pop()?)?;
				let bool_ty = self.builder.bool_ty();

				assert(self.ty_ck(bool_ty, pred), TyErr::ExpectedTy(bool_ty.as_key(), pred.as_key()))?;

				self.set_out_values(parent)
			}

			Switch(edges, _default)
			=> {
				let pred = self.builder.get_ty(self.stack.pop()?)?;

				assert(pred.has_equality(), TyErr::InvalidSwitchTy(pred.as_key()))?;

				for (constant, _) in edges.iter() {
					let const_ty = self.get_constant_ty(constant)?;

					assert(self.ty_ck(pred, const_ty), TyErr::ExpectedTy(pred.as_key(), const_ty.as_key()))?;
				}

				self.set_out_values(parent)
			}

			ComputedBranch(_)
			=> {
				// TODO: do these have to be constants?

				let dest = self.builder.get_ty(self.stack.pop()?)?;

				assert(dest.is_block(), TyErr::ExpectedBlock(dest.as_key()))?;

				self.set_out_values(parent)
			}


			Call
			=> {
				let callee = self.builder.get_ty(self.stack.pop()?)?;

				if let TyData::Function { parameter_tys, result_ty } = &callee.data {
					let peek_base = parameter_tys.len();

					for i in 0..peek_base {
						let j = peek_base - (i + 1);
						let parameter = self.builder.get_finalized_ty(unsafe { parameter_tys.get_unchecked(i) })?;
						let argument = self.builder.get_ty(self.stack.peek_at(j)?)?;

						assert(self.ty_ck(parameter, argument), TyErr::ExpectedTy(parameter.as_key(), argument.as_key()))?;
					}

					self.stack.pop_n(peek_base);

					if let Some(result) = result_ty {
						let ty = self.builder.get_finalized_ty(result)?;
						self.ty_map.set(parent.as_key(), node_idx, ty);

						self.stack.push(ty)
					}
				} else {
					return Err(TyErr::ExpectedFunction(callee.as_key()).into())
				}
			}

			Ret
			=> {
				if let Some(expected) = self.function.unwrap().result {
					let expected = self.builder.get_finalized_ty(expected)?;

					let result = self.builder.get_ty(self.stack.pop()?)?;

					assert(self.ty_ck(expected, result), TyErr::ExpectedTy(expected.as_key(), result.as_key()))?;
				}

				assert(self.stack.is_empty(), TyErr::UnusedValuesNoSuccessor(parent.as_key(), self.stack.len()))?
			}


			Duplicate(idx)
			=> {
				self.stack.duplicate(*idx as usize)?;
				if let Ok(cur) = self.stack.peek_at(0) { self.ty_map.set(parent.as_key(), node_idx, cur); }
			}

			Discard(idx)
			=> {
				self.stack.discard(*idx as usize)?;
				if let Ok(cur) = self.stack.peek_at(0) { self.ty_map.set(parent.as_key(), node_idx, cur); }
			}

			Swap(idx)
			=> {
				self.stack.swap(*idx as usize)?;
				if let Ok(cur) = self.stack.peek_at(0) { self.ty_map.set(parent.as_key(), node_idx, cur); }
			}

			Unreachable
			=> {
				self.stack.take();
			}
		}

		Ok(())
	}

	pub fn set_out_values<K: AsKey<BlockKey>> (&mut self, block_key: K) {
		let out_values = self.stack.take();

		assert!(self.cfg.set_out_values(block_key, out_values).unwrap().is_empty());
	}

	pub fn check_ir (&mut self, block_key: BlockKey) -> FunctionResult {
		// let block_key = block_key.as_key();
		let block = self.function.unwrap().block_data.get_keyed(block_key).ok_or(IrErrData::InvalidBlockKey(block_key)).at(FunctionErrLocation::Root)?;

		for (i, node) in block.ir.iter().enumerate() {
			self.check_node(block, node, i).at(FunctionErrLocation::Node(block_key, i))?;
		}

		Ok(())
	}


	pub fn check_in_edge_values (&mut self, block_key: BlockKey) -> FunctionResult {
		let in_values = match self.cfg.get_in_values(block_key) {
			Ok(x) if !x.is_empty() => x,
			_ => return Ok(())
		};

		let preds = match self.cfg.get_predecessors(block_key) {
			Ok(x) if !x.is_empty() => x,
			_ => return Err(TyErr::PhiNoPredecessors(block_key).at(FunctionErrLocation::Node(block_key, 0)))
		};

		for (i, &in_val) in in_values.iter().enumerate() {
			for &pred in preds.iter() {
				let out_val = {
					self.cfg
						.get_out_values(pred)
						.map_err(|_| TyErr::PhiMissingInPredecessor(pred))
						.and_then(|out_values| {
							let top = out_values.len();

							if top <= i { return Err(TyErr::PhiMissingInPredecessor(pred)) }

							let j = top - (i + 1);

							Ok(
								out_values
									.get(j)
									.copied()
									.unwrap()
							)
						})
						.at(FunctionErrLocation::Node(block_key, i))?
				};

				assert(
					self.ty_ck(in_val, out_val),
					IrErrData::from(TyErr::PhiTypeMismatch(pred, in_val, out_val))
						.at(FunctionErrLocation::Node(block_key, i))
				)?;
			}
		}

		Ok(())
	}

	pub fn check_out_edge_values (&mut self, block_key: BlockKey) -> FunctionResult {
		let out_values = match self.cfg.get_out_values(block_key) {
			Ok(x) if !x.is_empty() => x,
			_ => return Ok(())
		};

		let succs = match self.cfg.get_successors(block_key) {
			Ok(x) if !x.is_empty() => x,
			_ => return Err(
				TyErr::UnusedValuesNoSuccessor(block_key, out_values.len())
					.at(FunctionErrLocation::Block(block_key))
			)
		};

		for &succ in succs.iter() {
			self.cfg
				.get_in_values(succ)
				.map_err(|_| TyErr::UnusedValues(block_key, out_values.len()))
				.and_then(|in_values| {
					if in_values.len() < out_values.len() { Err(TyErr::UnusedValues(block_key, out_values.len() - in_values.len())) }
					else { Ok(()) }
				})
				.at(FunctionErrLocation::Block(block_key))?;
		}

		Ok(())
	}


	pub fn check_function (&mut self) -> FunctionResult {
		for &block_key in self.function.unwrap().block_order.iter() {
			self.check_ir(block_key)?;
		}

		for &block_key in self.function.unwrap().block_order.iter() {
			self.check_in_edge_values(block_key)?;
			self.check_out_edge_values(block_key)?;
		}

		Ok(())
	}
}




pub fn check_function (builder: &mut Builder<'_>, cfg: Cfg, function_key: FunctionKey) -> IrResult<(Cfg, TyMap)> {
	// SAFETY:
	// MIRI may not like this but it is safe;

	// whats going on here is that the ty checker needs mutable access to builder,
	// and it needs access to the function.
	// Its really not possible to just pass the function_key down and take references where needed,
	// because the process here is deeply recursive while traversing the function's parts, and at any depth it
	// can perform a mutation in the type system

	// This is safe because the `functions` slotmap field of the builder's context is never mutated during typechecking

	// The following simply gets a reference to the function without borrowing the builder
	let function = unsafe {
		&*(
			builder
				.get_function(function_key)
				.unwrap()
				.into_ref()
			as *const _
		)
	};

	let mut state = TyChecker::for_function(builder, cfg, function);

	state.check_function().at(function_key)?;

	Ok((state.cfg, state.ty_map))
}


pub fn check_global (builder: &mut Builder<'_>, global_key: GlobalKey) -> IrResult {
	// SAFETY:
	// see check_function
	let global: &Global = unsafe {
		&*(
			builder
				.get_global(global_key)
				.unwrap()
				.into_ref()
			as *const _
		)
	};

	let state = TyChecker::for_global(builder);

	let loc = IrErrLocation::Global(global_key);

	let ty = state.builder.get_finalized_ty(global.ty).at(loc)?;

	if let Some(init) = global.init.as_ref() {
		let init_ty = state.get_constant_ty(init).at(loc)?;

		assert(state.ty_ck(ty, init_ty), TyErr::ExpectedTy(ty.as_key(), init_ty.as_key()).at(loc))?;
	}

	Ok(())
}