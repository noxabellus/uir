use std::mem;

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




#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TyCkErr {
	TyErr(TyErr),
	IrErr(IrErr),
}

impl From<TyErr> for TyCkErr {
	fn from (e: TyErr) -> TyCkErr { TyCkErr::TyErr(e) }
}

impl From<IrErr> for TyCkErr {
	fn from (e: IrErr) -> TyCkErr { TyCkErr::IrErr(e) }
}

pub type TyCkResult<T = ()> = Result<T, TyCkErr>;

#[derive(Debug, Default)]
pub struct OpStack {
	entries: Stack<(TyKey, Option<Constant>)>
}

impl OpStack {
	fn len (&self) -> usize {
		self.entries.len()
	}

	fn is_empty (&self) -> bool {
		self.entries.is_empty()
	}

	fn push<K: AsKey<TyKey>> (&mut self, ty: K) {
		self.entries.push((ty.as_key(), None))
	}

	fn push_constant<K: AsKey<TyKey>> (&mut self, ty: K, c: Constant) {
		self.entries.push((ty.as_key(), Some(c)))
	}

	fn pop (&mut self) -> TyCkResult<TyKey> {
		Ok(
			self.entries
				.pop()
				.map(|(ty, _)| ty)
				.ok_or(TyErr::StackUnderflow)?
		)
	}

	// fn pop_constant (&mut self) -> TyCkResult<(TyKey, Constant)> {
	// 	Ok(
	// 		self.entries
	// 			.pop()
	// 			.ok_or(TyErr::StackUnderflow)
	// 			.and_then(|(ty, c)|
	// 				c
	// 					.ok_or(TyErr::ExpectedConstant)
	// 					.map(|c| (ty, c))
	// 			)?
	// 	)
	// }

	fn peek_at (&mut self, at: usize) -> TyCkResult<TyKey> {
		Ok(
			self.entries
				.peek_at(at)
				.map(|(ty, _)| *ty)
				.ok_or(TyErr::StackUnderflow)?
		)
	}

	fn peek_constant_at (&mut self, at: usize) -> TyCkResult<(TyKey, &Constant)> {
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

	fn pop_n (&mut self, n: usize) -> bool {
		self.entries.pop_n(n)
	}

	fn nth_is_constant (&mut self, at: usize) -> bool {
		self.entries
			.peek_at(at)
			.and_then(|(_, c)| c.as_ref())
			.is_some()
	}

	fn duplicate (&mut self) -> TyCkResult {
		if self.entries.duplicate() {
			Ok(())
		} else {
			Err(TyErr::StackUnderflow.into())
		}
	}

	// fn top_is_constant (&mut self) -> bool {
	// 	self.entries
	// 		.peek()
	// 		.and_then(|(_, c)| *c)
	// 		.is_some()
	// }


	fn take (&mut self) -> Vec<TyKey> {
		mem::take(&mut self.entries)
			.into_inner()
			.into_iter()
			.map(|(ty, _)| ty)
			.collect()
	}
}


#[derive(Debug)]
pub struct TyChecker<'r, 'b, 'f> {
	pub builder: &'r mut Builder<'b>,
	pub cfg: Cfg,
	pub function: &'f Function,
	pub stack: OpStack,
}


impl<'r, 'b, 'f> TyChecker<'r, 'b, 'f> {
	pub fn new (builder: &'r mut Builder<'b>, cfg: Cfg, function: &'f Function) -> Self {
		Self {
			builder,
			cfg,
			function,
			stack: OpStack::default()
		}
	}



	pub fn get_block<K: AsKey<BlockKey>> (&self, block_key: K) -> TyCkResult<Keyed<'f, Block>> {
		let block_key = block_key.as_key();
		let block = self.function.block_data.get_keyed(block_key).ok_or(IrErr::InvalidBlockKey(block_key))?;

		Ok(block)
	}

	pub fn get_param<K: AsKey<ParamKey>> (&self, param_key: K) -> TyCkResult<Keyed<'f, Param>> {
		let param_key = param_key.as_key();
		let param = self.function.param_data.get_keyed(param_key).ok_or(IrErr::InvalidParamKey(param_key))?;

		Ok(param)
	}

	pub fn get_local<K: AsKey<LocalKey>> (&self, local_key: K) -> TyCkResult<Keyed<'f, Local>> {
		let local_key = local_key.as_key();
		let local = self.function.locals.get_keyed(local_key).ok_or(IrErr::InvalidLocalKey(local_key))?;

		Ok(local)
	}



	// TODO better type equality
	pub fn ty_eq<KA: AsKey<TyKey>, KB: AsKey<TyKey>> (&self, a: KA, b: KB) -> bool {
		a.as_key() == b.as_key()
	}


	pub fn validate_aggregate_index (&self, ty: Keyed<Ty>, idx: u64) -> TyResult {
		if match &ty.data {
			TyData::Array { length, .. } => idx < *length,
			TyData::Structure { field_tys } => field_tys.get(idx as usize).is_some(),
			_ => return Err(TyErr::ExpectedAggregateTy(ty.as_key()))
		} {
			Ok(())
		} else {
			Err(TyErr::InvalidAggregateIndex(idx))
		}
	}

	pub fn validate_aggregate_element<K: AsKey<TyKey>> (&self, ty: Keyed<Ty>, idx: u64, ty_key: K) -> TyResult {
		let ty_key = ty_key.as_key();

		match &ty.data {
			&TyData::Array { length, element_ty } => {
				assert(idx < length, TyErr::InvalidAggregateIndex(idx))?;
				assert(self.ty_eq(element_ty, ty_key), TyErr::ExpectedAggregateElementTy(idx, element_ty, ty_key))?;
			}


			TyData::Structure { field_tys } => {
				let field_ty = *field_tys.get(idx as usize).ok_or(TyErr::InvalidAggregateIndex(idx))?;
				assert(self.ty_eq(field_ty, ty_key), TyErr::ExpectedAggregateElementTy(idx, field_ty, ty_key))?;
			}

			_ => return Err(TyErr::ExpectedAggregateTy(ty.as_key())),
		}

		Ok(())
	}

	pub fn extract_pointer_target (&self, ty: Keyed<Ty>) -> TyCkResult<TyKey> {
		if let TyData::Pointer { target_ty } = &ty.data  {
			Ok(self.builder.get_finalized_ty(target_ty)?.as_key())
		} else {
			Err(TyErr::ExpectedPointer(ty.as_key()).into())
		}
	}


	pub fn check_bin_op<'x> (&'x self, op: BinaryOp, ty: Keyed<'x, Ty>) -> TyCkResult<Keyed<'x, Ty>> {
		let ty_key = ty.as_key();

		let invalid_operand_err = TyErr::BinaryOpInvalidOperandTy(op, ty_key);

		assert(ty.is_scalar(), invalid_operand_err)?;

		use BinaryOp::*;

		Ok(match op {
			Add | Sub | Mul | Div | Rem | Lt | Gt | Le | Ge
			=> {
				assert(ty.is_arithmetic(), invalid_operand_err)?;
				ty
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

	pub fn check_un_op<'x> (&'x self, op: UnaryOp, ty: Keyed<'x, Ty>) -> TyCkResult<Keyed<'x, Ty>> {
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

	pub fn check_cast_op (&self, op: CastOp, curr_ty: Keyed<Ty>, new_ty: Keyed<Ty>) -> TyCkResult {
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

			SIntToUInt
			=> curr_ty.is_sint()
			&& new_ty.is_uint()
			&& self.builder.size_of(new_ty)? == self.builder.size_of(curr_ty)?,

			UIntToSInt
			=> curr_ty.is_uint()
			&& new_ty.is_sint()
			&& self.builder.size_of(new_ty)? == self.builder.size_of(curr_ty)?,

			ZeroExtend
			=> curr_ty.is_int()
			&& new_ty.is_int()
			&& self.builder.size_of(new_ty)? >= self.builder.size_of(curr_ty)?,

			SignExtend
			=> self.builder.size_of(new_ty)? >= self.builder.size_of(curr_ty)?
			&& (
					 (curr_ty.is_int() && new_ty.is_int())
				|| (curr_ty.is_real() && new_ty.is_real())
			),

			Truncate
			=> self.builder.size_of(curr_ty)? >= self.builder.size_of(new_ty)?
			&& (
					 (curr_ty.is_int()  && new_ty.is_int())
				|| (curr_ty.is_real() && new_ty.is_real())
			),

			Bitcast
			=> self.builder.size_of(curr_ty)? == self.builder.size_of(new_ty)?
		}, TyErr::InvalidCast(op, curr_ty_key, new_ty_key).into())
	}



	pub fn get_constant_ty (&self, constant: &Constant) -> TyCkResult<Keyed<Ty>> {
		use Constant::*;

		Ok(match constant {
			Null(ty_key)
			=> {
				let ty = self.builder.get_finalized_ty(ty_key)?;

				if !ty.is_pointer() {
					return Err(TyErr::InvalidNull(ty.as_key()).into())
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

						if let TyData::Array { element_ty, .. } = ty.data {
							assert(self.ty_eq(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(0, element_ty, operand_ty.as_key()))?;
						} else {
							return Err(TyErr::ExpectedArray(ty.as_key()).into())
						}
					}

					ConstantAggregateData::Complete(elements)
					=> {
						match &ty.data {
							&TyData::Array { length, element_ty } => {
								for i in 0..length {
									let operand = elements.get(i as usize).ok_or(TyErr::MissingAggregateElement(*ty_key, i))?;
									let operand_ty = self.get_constant_ty(operand)?;

									assert(self.ty_eq(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(i, element_ty, operand_ty.as_key()))?;
								}
							},

							TyData::Structure { field_tys } => {
								for (i, &field_ty) in field_tys.iter().enumerate() {
									let operand = elements.get(i).ok_or(TyErr::MissingAggregateElement(*ty_key, i as u64))?;
									let operand_ty = self.get_constant_ty(operand)?;

									assert(self.ty_eq(field_ty, operand_ty), TyErr::ExpectedAggregateElementTy(i as u64, field_ty, operand_ty.as_key()))?;
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
									assert(i < length, TyErr::InvalidAggregateIndex(i))?;

									let operand_ty = self.get_constant_ty(operand)?;

									assert(self.ty_eq(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(i, element_ty, operand_ty.as_key()))?;
								}
							},

							TyData::Structure { field_tys } => {
								for &(i, ref operand) in indexed_elements.iter() {
									let field_ty = *field_tys.get(i as usize).ok_or(TyErr::InvalidAggregateIndex(i))?;
									let operand_ty = self.get_constant_ty(operand)?;

									assert(self.ty_eq(field_ty, operand_ty), TyErr::ExpectedAggregateElementTy(i as u64, field_ty, operand_ty.as_key()))?;
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

	pub fn check_node (&mut self, parent: Keyed<Block>, node: &Ir) -> TyCkResult {
		use IrData::*;

		match &node.data {
			Constant(constant)
			=> {
				self.stack.push_constant(self.get_constant_ty(constant)?.as_key(), constant.clone())
			}

			BuildAggregate(ty_key, agg_data)
			=> {
				let ty = self.builder.get_finalized_ty(ty_key)?;

				assert(ty.is_aggregate(), TyErr::ExpectedAggregateTy(ty.as_key()))?;

				match agg_data {
					| AggregateData::Zeroed
					| AggregateData::Uninitialized
					=> { }

					AggregateData::CopyFill
					=> {
						let operand_ty = self.stack.pop()?;

						if let TyData::Array { element_ty, .. } = ty.data {
							assert(self.ty_eq(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(0, element_ty, operand_ty.as_key()))?;
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

									assert(self.ty_eq(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(i, element_ty, operand_ty))?;
								}
							},

							TyData::Structure { field_tys } => {
								for (i, &field_ty) in field_tys.iter().enumerate() {
									let operand_ty = self.stack.pop()?;

									assert(self.ty_eq(field_ty, operand_ty), TyErr::ExpectedAggregateElementTy(i as u64, field_ty, operand_ty))?;
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
									assert(i < length, TyErr::InvalidAggregateIndex(i))?;

									let operand_ty = self.stack.pop()?;

									assert(self.ty_eq(element_ty, operand_ty), TyErr::ExpectedAggregateElementTy(i, element_ty, operand_ty))?;
								}
							},

							TyData::Structure { field_tys } => {
								for &i in indices.iter() {
									let field_ty = *field_tys.get(i as usize).ok_or(TyErr::InvalidAggregateIndex(i))?;
									let operand_ty = self.stack.pop()?;

									assert(self.ty_eq(field_ty, operand_ty), TyErr::ExpectedAggregateElementTy(i as u64, field_ty, operand_ty))?;
								}
							}

							_ => unreachable!()
						}
					}
				}

				self.stack.push(ty)
			}

			GlobalRef(global_key)
			=> {
				let global = self.builder.get_global(global_key)?;
				let ty_key = self.builder.get_finalized_ty(global.ty)?.as_key();

				self.stack.push(self.builder.pointer_ty(ty_key)?)
			}

			FunctionRef(function_key)
			=> {
				let function = self.builder.get_function(function_key)?;

				self.stack.push(self.builder.get_finalized_ty(function.ty)?)
			}

			BlockRef(block_key)
			=> {
				self.get_block(block_key)?;

				self.stack.push(self.builder.block_ty())
			}

			ParamRef(param_key)
			=> {
				let param = self.get_param(param_key)?;
				let ty_key = self.builder.get_finalized_ty(param.ty)?.as_key();

				self.stack.push(self.builder.pointer_ty(ty_key)?)
			}

			LocalRef(local_key)
			=> {
				let local = self.get_local(local_key)?;
				let ty_key = self.builder.get_finalized_ty(local.ty)?.as_key();

				self.stack.push(self.builder.pointer_ty(ty_key)?)
			}

			Phi(ty_key)
			=> {
				let ty_key = self.builder.get_finalized_ty(ty_key)?.as_key();

				self.cfg.add_in_value(parent, ty_key).unwrap();

				self.stack.push(ty_key)
			}

			BinaryOp(op)
			=> {
				let left = self.builder.get_ty(self.stack.pop()?)?;
				let right = self.stack.pop()?;

				assert(self.ty_eq(left, right), TyErr::BinaryOpTypeMismatch(left.as_key(), right))?;

				self.stack.push(self.check_bin_op(*op, left)?.as_key())
			}

			UnaryOp(op)
			=> {
				let operand = self.builder.get_ty(self.stack.pop()?)?;

				self.stack.push(self.check_un_op(*op, operand)?.as_key())
			}

			CastOp(op, ty_key)
			=> {
				let operand = self.builder.get_ty(self.stack.pop()?)?;
				let new_ty = self.builder.get_finalized_ty(ty_key)?;

				self.check_cast_op(*op, operand, new_ty)?;

				self.stack.push(new_ty)
			}

			Gep(num_indices)
			=> {
				assert(*num_indices > 0, TyErr::GepNoIndices)?;

				let peek_base = *num_indices as usize + 1;
				let target = self.builder.get_ty(self.stack.peek_at(peek_base)?)?;
				assert(target.is_pointer(), TyErr::GepTargetNotPointer(target.as_key()))?;

				let ptr_index = self.builder.get_ty(self.stack.peek_at(peek_base - 1)?)?;
				assert(ptr_index.is_int(), TyErr::GepInvalidIndex(ptr_index.as_key()))?;


				let mut target = self.builder.get_ty(self.extract_pointer_target(target)?)?;

				for n in 1..*num_indices as usize {
					let i = peek_base - (n + 1);

					match &target.data {
						TyData::Array { length, element_ty } => {
							if self.stack.nth_is_constant(i) {
								let (ty, constant) = self.stack.peek_constant_at(i).unwrap();

								let index = constant.as_index().ok_or(TyErr::ExpectedInteger(ty))?;

								assert(index <= *length, TyErr::GepOutOfBounds(target.as_key(), *length, index))?
							} else {
								let index = self.builder.get_ty(self.stack.pop()?)?;

								assert(index.is_int(), TyErr::GepInvalidIndex(index.as_key()))?;
							}

							target = self.builder.get_finalized_ty(element_ty)?
						}

						TyData::Structure { field_tys } => {
							let (ty, constant) = self.stack.peek_constant_at(i)?;

							let index = constant.as_index().ok_or(TyErr::ExpectedInteger(ty))?;

							let field_ty = field_tys.get(index as usize).ok_or_else(|| TyErr::GepOutOfBounds(target.as_key(), field_tys.len() as u64, index))?;

							target = self.builder.get_finalized_ty(field_ty)?
						}

						TyData::Pointer { .. } => return Err(TyErr::GepImplicitLoad(target.as_key()).into()),

						_ => return Err(TyErr::GepInvalidSubElement(target.as_key()).into())
					}
				}


				let target = target.as_key();

				self.stack.pop_n(peek_base);
				self.stack.push(self.builder.pointer_ty(target)?)
			}

			Load
			=> {
				let target = self.builder.get_ty(self.stack.pop()?)?;

				self.stack.push(self.extract_pointer_target(target)?)
			}

			Store
			=> {
				let target = self.builder.get_ty(self.stack.pop()?)?;
				let target_value = self.extract_pointer_target(target)?;

				let value = self.builder.get_ty(self.stack.pop()?)?;

				assert(self.ty_eq(target_value, value), TyErr::ExpectedTy(target_value, value.as_key()))?;

				self.stack.push(value)
			}

			| Branch(_)
			| CondBranch(_, _)
			| Switch(_)
			| ComputedBranch(_)
			=> {
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

						assert(self.ty_eq(parameter, argument), TyErr::ExpectedTy(parameter.as_key(), argument.as_key()))?;
					}

					self.stack.pop_n(peek_base);

					if let Some(result) = result_ty {
						let result = self.builder.get_finalized_ty(result)?;

						self.stack.push(result)
					}
				} else {
					return Err(TyErr::ExpectedFunction(callee.as_key()).into())
				}
			}

			Ret
			=> {
				if let Some(expected) = self.function.result {
					let expected = self.builder.get_finalized_ty(expected)?;

					let result = self.builder.get_ty(self.stack.pop()?)?;

					assert(self.ty_eq(expected, result), TyErr::ExpectedTy(expected.as_key(), result.as_key()))?;
				}

				assert(self.stack.is_empty(), TyErr::UnusedValues(parent.as_key(), self.stack.len()))?
			}


			Duplicate
			=> {
				self.stack.duplicate()?
			}

			Discard
			=> {
				self.stack.pop()?;
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

	pub fn check_ir (&mut self, block_key: BlockKey) -> TyCkResult {
		// let block_key = block_key.as_key();
		let block = self.function.block_data.get_keyed(block_key).ok_or(IrErr::InvalidBlockKey(block_key))?;

		for node in block.ir.iter() {
			self.check_node(block, node)?;
		}

		Ok(())
	}


	pub fn check_edge_values (&mut self, block_key: BlockKey) -> TyCkResult {
		let x = {
			self.cfg
				.get_predecessors(block_key)
				.and_then(|preds|
					self.cfg
						.get_in_values(block_key)
						.map(|in_values| (preds, in_values))
				)
		};

		let (preds, in_values) = if let Ok(x) = x { x } else { return Ok(()) };

		for (i, &in_val) in in_values.iter().enumerate() {
			for &pred in preds.iter() {
				let out_val = {
					self.cfg
						.get_out_values(pred)
						.map_err(|_| TyErr::PhiMissingInPredecessor)
						.and_then(|out_values| {
							let top = out_values.len();

							if top <= i { return Err(TyErr::PhiMissingInPredecessor) }

							let j = top - (i + 1);

							Ok(
								out_values
									.get(j)
									.copied()
									.unwrap()
							)
						})?
				};

				assert(self.ty_eq(in_val, out_val), TyErr::ExpectedTy(in_val, out_val))?;
			}
		}

		Ok(())
	}


	pub fn check_function (&mut self) -> TyCkResult {
		for &block_ref in self.function.block_order.iter() {
			self.check_ir(block_ref)?;
		}

		for &block_ref in self.function.block_order.iter() {
			self.check_edge_values(block_ref)?;
		}

		Ok(())
	}
}




pub fn check (builder: &mut Builder<'_>, cfg: Cfg, function: &Function) -> TyCkResult<Cfg> {
	let mut state = TyChecker::new(builder, cfg, function);

	state.check_function()?;

	Ok(state.cfg)
}