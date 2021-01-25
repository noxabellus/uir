use support::{
	slotmap::{ AsKey, Keyed, KeyedMut },
};

use super::{
	src::*,
	ty::*,
	ir::*,
	cfg::*,
	ty_checker::{ self, * },
};


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IrErr {
	NoActiveBlock,
	InvalidParamKey(ParamKey),
	InvalidParamIndex(usize),
	InvalidLocalKey(LocalKey),
	ExpectedAggregateTy(TyKey),
	InvalidAggregateIndex(TyKey, u64),
	InvalidBlockKey(BlockKey),
	InvalidBlockIndex(usize),
	InvalidTyKey(TyKey),
	InvalidNodeIndex(usize),
	CfgErr(CfgErr),
	TyErr(TyErr),
	NodeAfterTerminator(BlockKey, usize),
	CannotFinalize
}

impl From<CfgErr> for IrErr {
	fn from (e: CfgErr) -> IrErr { IrErr::CfgErr(e) }
}

impl From<TyCkErr> for IrErr {
	fn from (e: TyCkErr) -> IrErr {
		match e {
			TyCkErr::TyErr(e) => IrErr::TyErr(e),
			TyCkErr::IrErr(e) => e
		}
	}
}

pub type IrResult<T = ()> = Result<T, IrErr>;


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum InsertionCursor {
	Start,
	Index(usize),
	End
}

impl Default for InsertionCursor { fn default () -> Self { Self::End } }

impl InsertionCursor {
	pub fn take (&mut self) -> Self { let out = *self; *self = Self::default(); out }
}


#[derive(Debug)]
pub struct Builder<'c> {
	pub ctx: &'c mut Context,
}



#[derive(Debug)]
pub struct FunctionBuilder<'b> {
	pub builder: &'b mut Builder<'b>,

	pub function_key: FunctionKey,
	pub function: Function,

	pub active_block: Option<BlockKey>,
	pub insertion_cursor: InsertionCursor,
	pub active_src: Option<SrcAttribution>,
}



impl<'b> FunctionBuilder<'b> {
	pub fn new<K: AsKey<TyKey>> (builder: &'b mut Builder<'b>) -> Self {
		let function_key = builder.ctx.functions.reserve();

		Self {
			builder,

			function_key,
			function: Function::default(),

			active_block: None,
			insertion_cursor: InsertionCursor::default(),
			active_src: None,
		}
	}




	pub fn finalize (mut self) -> IrResult<KeyedMut<'b, Function>> {
		self.clear_active_block();

		self.generate_own_ty()?;

		let mut cfg = Cfg::default();

		self.generate_cfg(&mut cfg)?;
		self.type_check(&mut cfg)?;

		self.function.cfg = cfg;

		self.builder.ctx.functions
			.define(self.function_key, self.function)
			.ok_or(IrErr::CannotFinalize)
	}



	pub fn generate_own_ty (&mut self) -> IrResult<KeyedMut<Ty>> {
		let result_ty = if let Some(result_ty) = self.function.result {
			self.get_ty(result_ty)?;
			Some(result_ty)
		} else {
			None
		};

		let mut parameter_tys = vec![];

		for &param_key in self.function.param_order.iter() {
			let param = self.get_param(param_key)?;

			self.get_ty(param.ty)?;

			parameter_tys.push(param.ty);
		}

		let ty = self.builder.ctx.add_ty(TyData::Function { parameter_tys, result_ty }.into());

		self.function.ty = ty.as_key();

		Ok(ty)
	}



	fn walk_block (&self, cfg: &mut Cfg, block_key: BlockKey) -> IrResult {
		let block = self.get_block(block_key)?;

		let mut iter = block.ir.iter().enumerate();

		while let Some((i, node)) = iter.next() {
			if node.is_terminator() {
				node.for_each_edge(|to| {
					cfg.add_edge(block_key, to)?;
					self.walk_block(cfg, to)
				})?;

				if iter.next().is_some() {
					return Err(IrErr::NodeAfterTerminator(block_key, i))
				}
			}
		}

		Ok(())
	}


	pub fn generate_cfg (&self, cfg: &mut Cfg) -> IrResult {
		for &block_ref in self.function.block_order.iter() {
			self.walk_block(cfg, block_ref)?;
		}

		Ok(())
	}



	pub fn type_check (&self, cfg: &mut Cfg) -> IrResult {
		ty_checker::check(self, cfg)?;
		Ok(())
	}



	pub fn set_return_ty<K: AsKey<TyKey>> (&mut self, ty_key: K) {
		let ty = ty_key.as_key();

		self.function.result = Some(ty)
	}

	pub fn set_no_return_ty (&mut self) {
		self.function.result = None
	}



	pub fn make_local<K: AsKey<TyKey>> (&mut self, ty_key: K) -> KeyedMut<Local> {
		let ty = ty_key.as_key();

		self.function.locals.insert(Local { ty, .. Local::default() })
	}

	pub fn get_local<K: AsKey<LocalKey>> (&self, local_key: K) -> IrResult<Keyed<Local>> {
		let local_key = local_key.as_key();

		self.function.locals.get_keyed(local_key).ok_or(IrErr::InvalidLocalKey(local_key))
	}

	pub fn get_local_mut<K: AsKey<LocalKey>> (&mut self, local_key: K) -> IrResult<KeyedMut<Local>> {
		let local_key = local_key.as_key();

		self.function.locals.get_keyed_mut(local_key).ok_or(IrErr::InvalidLocalKey(local_key))
	}




	pub fn append_param<K: AsKey<TyKey>> (&mut self, ty_key: K) -> KeyedMut<Param> {
		let ty = ty_key.as_key();

		let param = self.function.param_data.insert(Param { ty, .. Param::default() });

		self.function.param_order.push(param.as_key());

		param
	}

	pub fn insert_param<K: AsKey<TyKey>> (&mut self, idx: usize, ty_key: K) -> IrResult<KeyedMut<Param>> {
		let ty = ty_key.as_key();

		if idx > self.function.param_order.len() { return Err(IrErr::InvalidParamIndex(idx)) }

		let param = self.function.param_data.insert(Param { ty, .. Param::default() });

		self.function.param_order.insert(idx, param.as_key());

		Ok(param)
	}

	pub fn remove_param<K: AsKey<ParamKey>> (&mut self, param_key: K) -> IrResult<Param> {
		let param_key = param_key.as_key();

		let idx = self.get_param_index(param_key)?;

		let param = self.function.param_data.remove(param_key).unwrap();
		self.function.param_order.remove(idx);

		Ok(param)
	}


	pub fn move_param_to_start<K: AsKey<ParamKey>> (&mut self, param_key: K) -> IrResult {
		let param_key = param_key.as_key();

		let idx = self.get_param_index(param_key)?;

		self.function.param_order.remove(idx);
		self.function.param_order.insert(0, param_key);

		Ok(())
	}

	pub fn move_param_to_end<K: AsKey<ParamKey>> (&mut self, param_key: K) -> IrResult {
		let param_key = param_key.as_key();

		let idx = self.get_param_index(param_key)?;

		self.function.param_order.remove(idx);
		self.function.param_order.push(param_key);

		Ok(())
	}

	pub fn move_param_before<KA: AsKey<ParamKey>, KB: AsKey<ParamKey>> (&mut self, param_to_move: KA, destination_param: KB) -> IrResult {
		let param_to_move = param_to_move.as_key();
		let destination_param = destination_param.as_key();

		let idx_to_move = self.get_param_index(param_to_move)?;
		let destination_idx = self.get_param_index(destination_param)?;

		self.function.param_order.remove(idx_to_move);
		self.function.param_order.insert(destination_idx, param_to_move);

		Ok(())
	}

	pub fn move_param_after<KA: AsKey<ParamKey>, KB: AsKey<ParamKey>> (&mut self, param_to_move: KA, destination_param: KB) -> IrResult {
		let param_to_move = param_to_move.as_key();
		let destination_param = destination_param.as_key();

		let idx_to_move = self.get_param_index(param_to_move)?;
		let destination_idx = self.get_param_index(destination_param)?;

		self.function.param_order.remove(idx_to_move);
		self.function.param_order.insert(destination_idx + 1, param_to_move);

		Ok(())
	}

	pub fn swap_params<KA: AsKey<ParamKey>, KB: AsKey<ParamKey>> (&mut self, a: KA, b: KB) -> IrResult {
		let a = self.get_param_index(a)?;
		let b = self.get_param_index(b)?;

		self.function.param_order.swap(a, b);

		Ok(())
	}


	pub fn get_param_index<K: AsKey<ParamKey>> (&self, param_key: K) -> IrResult<usize> {
		let param_key = param_key.as_key();

		self.function.param_order
			.iter()
			.enumerate()
			.find(|&(_, &pk)| pk == param_key)
			.map(|(i, _)| i)
			.ok_or(IrErr::InvalidParamKey(param_key))
	}

	pub fn get_param<K: AsKey<ParamKey>> (&self, param_key: K) -> IrResult<Keyed<Param>> {
		let param_key = param_key.as_key();

		self.function.param_data.get_keyed(param_key).ok_or(IrErr::InvalidParamKey(param_key))
	}

	pub fn get_param_mut<K: AsKey<ParamKey>> (&mut self, param_key: K) -> IrResult<KeyedMut<Param>> {
		let param_key = param_key.as_key();

		self.function.param_data.get_keyed_mut(param_key).ok_or(IrErr::InvalidParamKey(param_key))
	}




	pub fn get_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<&Ty> {
		let ty_key = ty_key.as_key();
		self.builder.ctx.tys.get(ty_key).ok_or(IrErr::InvalidTyKey(ty_key))
	}

	pub fn get_ty_mut<K: AsKey<TyKey>> (&mut self, ty_key: K) -> IrResult<&mut Ty> {
		let ty_key = ty_key.as_key();
		self.builder.ctx.tys.get_mut(ty_key).ok_or(IrErr::InvalidTyKey(ty_key))
	}



	pub fn append_block (&mut self, block: Block) -> KeyedMut<Block> {
		let block = self.function.block_data.insert(block);
		self.function.block_order.push(block.as_key());
		block
	}

	pub fn insert_block (&mut self, idx: usize, block: Block) -> IrResult<KeyedMut<Block>> {
		if idx > self.function.block_order.len() { return Err(IrErr::InvalidBlockIndex(idx)) }

		let block = self.function.block_data.insert(block);

		self.function.block_order.insert(idx, block.as_key());

		Ok(block)
	}

	pub fn append_new_block (&mut self) -> KeyedMut<Block> {
		self.append_block(Block::default())
	}

	pub fn insert_new_block (&mut self, idx: usize) -> IrResult<KeyedMut<Block>> {
		self.insert_block(idx, Block::default())
	}

	pub fn remove_block<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrResult<Block> {
		let block_key = block_key.as_key();

		let idx = self.get_block_index(block_key)?;

		self.function.block_order.remove(idx);
		let block = self.function.block_data.remove(block_key).unwrap();

		if self.active_block == Some(block_key) {
			self.insertion_cursor.take();
			self.active_block.take();
		}

		Ok(block)
	}


	pub fn move_block_to_start<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrResult {
		let block_key = block_key.as_key();

		let idx = self.get_block_index(block_key)?;

		self.function.block_order.remove(idx);
		self.function.block_order.insert(0, block_key);

		Ok(())
	}

	pub fn move_block_to_end<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrResult {
		let block_key = block_key.as_key();

		let idx = self.get_block_index(block_key)?;

		self.function.block_order.remove(idx);
		self.function.block_order.push(block_key);

		Ok(())
	}

	pub fn move_block_before<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, block_to_move: KA, destination_block: KB) -> IrResult {
		let block_to_move = block_to_move.as_key();
		let destination_block = destination_block.as_key();

		let idx_to_move = self.get_block_index(block_to_move)?;
		let destination_idx = self.get_block_index(destination_block)?;

		self.function.block_order.remove(idx_to_move);
		self.function.block_order.insert(destination_idx, block_to_move);

		Ok(())
	}

	pub fn move_block_after<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, block_to_move: KA, destination_block: KB) -> IrResult {
		let block_to_move = block_to_move.as_key();
		let destination_block = destination_block.as_key();

		let idx_to_move = self.get_block_index(block_to_move)?;
		let destination_idx = self.get_block_index(destination_block)?;

		self.function.block_order.remove(idx_to_move);
		self.function.block_order.insert(destination_idx + 1, block_to_move);

		Ok(())
	}

	pub fn swap_blocks<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, a: KA, b: KB) -> IrResult {
		let a = self.get_block_index(a)?;
		let b = self.get_block_index(b)?;

		self.function.block_order.swap(a, b);

		Ok(())
	}


	pub fn get_block_index<K: AsKey<BlockKey>> (&self, block_key: K) -> IrResult<usize> {
		let block_key = block_key.as_key();

		self.function.block_order
			.iter()
			.enumerate()
			.find(|&(_, &br)| br == block_key)
			.map(|(i, _)| i)
			.ok_or(IrErr::InvalidBlockKey(block_key))
	}

	pub fn get_block<K: AsKey<BlockKey>> (&self, block_key: K) -> IrResult<Keyed<Block>> {
		let block_key = block_key.as_key();
		self.function.block_data.get_keyed(block_key).ok_or(IrErr::InvalidBlockKey(block_key))
	}

	pub fn get_block_mut<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrResult<KeyedMut<Block>> {
		let block_key = block_key.as_key();
		self.function.block_data.get_keyed_mut(block_key).ok_or(IrErr::InvalidBlockKey(block_key))
	}

	pub fn get_active_block_key (&self) -> IrResult<BlockKey> {
		self.active_block.ok_or(IrErr::NoActiveBlock)
	}

	pub fn get_active_block (&self) -> IrResult<Keyed<Block>> {
		self.get_block(self.get_active_block_key()?)
	}

	pub fn get_active_block_mut (&mut self) -> IrResult<KeyedMut<Block>> {
		self.get_block_mut(self.get_active_block_key()?)
	}


	pub fn set_active_block<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrResult<Option<(BlockKey, InsertionCursor)>> {
		let block_key = block_key.as_key();

		self.get_block(block_key)?;

		let prev_loc = self.clear_active_block();

		self.active_block = Some(block_key);

		Ok(prev_loc)
	}

	pub fn clear_active_block (&mut self) -> Option<(BlockKey, InsertionCursor)> {
		let block = self.active_block.take();
		let cursor = self.insertion_cursor.take();

		block.map(|block| (block, cursor))
	}




	pub fn get_cursor (&self) -> IrResult<InsertionCursor> {
		self.get_active_block()?;

		Ok(self.insertion_cursor)
	}

	pub fn set_cursor (&mut self, idx: usize) -> IrResult {
		if idx > self.get_active_block()?.ir.len() {
			return Err(IrErr::InvalidNodeIndex(idx))
		}

		self.insertion_cursor = InsertionCursor::Index(idx);

		Ok(())
	}

	pub fn move_cursor_to_end (&mut self) -> IrResult {
		self.get_active_block()?;
		self.insertion_cursor = InsertionCursor::End;
		Ok(())
	}

	pub fn move_cursor_to_start (&mut self) -> IrResult {
		self.get_active_block()?;
		self.insertion_cursor = InsertionCursor::Start;
		Ok(())
	}


	pub fn append_node<I: Into<Ir>> (&mut self, i: I) -> IrResult<&mut Ir> {
		let mut node = i.into();

		if node.src.is_none() {
			node.src = self.active_src;
		}

		if let InsertionCursor::Index(cursor) = self.get_cursor()? {
			if cursor == self.get_active_block()?.ir.len() - 1 {
				self.set_cursor(cursor + 1)?;
			}
		}

		let mut block = self.get_active_block_mut()?;

		let idx = block.ir.len();

		block.ir.push(node);

		Ok(unsafe { block.into_mut().ir.get_unchecked_mut(idx) })
	}

	pub fn insert_node<I: Into<Ir>> (&mut self, idx: usize, i: I) -> IrResult<&mut Ir> {
		if idx > self.get_active_block()?.ir.len() {
			return Err(IrErr::InvalidNodeIndex(idx))
		}

		if let InsertionCursor::Index(cursor) = self.get_cursor()? {
			if cursor >= idx {
				self.set_cursor(cursor + 1)?;
			}
		}

		let mut node = i.into();

		if node.src.is_none() {
			node.src = self.active_src;
		}

		let mut block = self.get_active_block_mut()?;

		block.ir.insert(idx, node);

		Ok(unsafe { block.into_mut().ir.get_unchecked_mut(idx) })
	}

	pub fn write_node<I: Into<Ir>> (&mut self, i: I) -> IrResult<&mut Ir> {
		let mut node = i.into();

		if node.src.is_none() {
			node.src = self.active_src;
		}

		let idx = match self.get_cursor()? {
			InsertionCursor::Start => 0,
			InsertionCursor::Index(idx) => {
				self.set_cursor(idx + 1)?;
				idx
			},
			InsertionCursor::End => self.get_active_block()?.ir.len(),
		};

		let mut block = self.get_active_block_mut()?;

		block.ir.insert(idx, node);

		Ok(unsafe { block.into_mut().ir.get_unchecked_mut(idx) })
	}

	pub fn remove_node (&mut self, idx: usize) -> IrResult<Ir> {
		if idx >= self.get_active_block()?.ir.len() {
			return Err(IrErr::InvalidNodeIndex(idx))
		}

		if let InsertionCursor::Index(cursor) = self.get_cursor()? {
			if cursor >= idx {
				self.set_cursor(cursor.saturating_sub(1))?;
			}
		}

		let mut block = self.get_active_block_mut()?;

		Ok(block.ir.remove(idx))
	}


	pub fn move_node_to_start (&mut self, idx: usize) -> IrResult {
		let mut block = self.get_active_block_mut()?;

		block.ir.get(idx).ok_or(IrErr::InvalidNodeIndex(idx))?;

		let node = block.ir.remove(idx);
		block.ir.insert(0, node);

		Ok(())
	}

	pub fn move_node_to_end (&mut self, idx: usize) -> IrResult {
		let mut block = self.get_active_block_mut()?;

		block.ir.get(idx).ok_or(IrErr::InvalidNodeIndex(idx))?;

		let node = block.ir.remove(idx);
		block.ir.push(node);

		Ok(())
	}

	pub fn move_node_before (&mut self, idx_to_move: usize, destination_idx: usize) -> IrResult {
		let mut block = self.get_active_block_mut()?;

		block.ir.get(idx_to_move).ok_or(IrErr::InvalidNodeIndex(idx_to_move))?;
		block.ir.get(destination_idx).ok_or(IrErr::InvalidNodeIndex(destination_idx))?;

		let node = block.ir.remove(idx_to_move);
		block.ir.insert(destination_idx, node);

		Ok(())
	}

	pub fn move_node_after (&mut self, idx_to_move: usize, destination_idx: usize) -> IrResult {
		let mut block = self.get_active_block_mut()?;

		block.ir.get(idx_to_move).ok_or(IrErr::InvalidNodeIndex(idx_to_move))?;
		block.ir.get(destination_idx).ok_or(IrErr::InvalidNodeIndex(destination_idx))?;

		let node = block.ir.remove(idx_to_move);
		block.ir.insert(destination_idx + 1, node);

		Ok(())
	}

	pub fn swap_nodes (&mut self, a_idx: usize, b_idx: usize) -> IrResult {
		let mut block = self.get_active_block_mut()?;

		block.ir.get(a_idx).ok_or(IrErr::InvalidNodeIndex(a_idx))?;
		block.ir.get(b_idx).ok_or(IrErr::InvalidNodeIndex(b_idx))?;

		block.ir.swap(a_idx, b_idx);

		Ok(())
	}


	pub fn get_node (&self, idx: usize) -> IrResult<&Ir> {
		self.get_active_block()?.into_ref().ir.get(idx).ok_or(IrErr::InvalidNodeIndex(idx))
	}

	pub fn get_node_mut (&mut self, idx: usize) -> IrResult<&mut Ir> {
		self.get_active_block_mut()?.into_mut().ir.get_mut(idx).ok_or(IrErr::InvalidNodeIndex(idx))
	}


	pub fn constant (&mut self, constant: Constant) -> IrResult<&mut Ir> { self.write_node(IrData::Constant(constant)) }

	pub fn const_null (&mut self) -> IrResult<&mut Ir> { self.constant(Constant::Null) }
	pub fn const_bool (&mut self, value: bool) -> IrResult<&mut Ir> { self.constant(Constant::Bool(value)) }
	pub fn const_sint8 (&mut self, value: i8) -> IrResult<&mut Ir> { self.constant(Constant::SInt8(value)) }
	pub fn const_sint16 (&mut self, value: i16) -> IrResult<&mut Ir> { self.constant(Constant::SInt16(value)) }
	pub fn const_sint32 (&mut self, value: i32) -> IrResult<&mut Ir> { self.constant(Constant::SInt32(value)) }
	pub fn const_sint64 (&mut self, value: i64) -> IrResult<&mut Ir> { self.constant(Constant::SInt64(value)) }
	pub fn const_sint128 (&mut self, value: i128) -> IrResult<&mut Ir> { self.constant(Constant::SInt128(value)) }
	pub fn const_uint8 (&mut self, value: u8) -> IrResult<&mut Ir> { self.constant(Constant::UInt8(value)) }
	pub fn const_uint16 (&mut self, value: u16) -> IrResult<&mut Ir> { self.constant(Constant::UInt16(value)) }
	pub fn const_uint32 (&mut self, value: u32) -> IrResult<&mut Ir> { self.constant(Constant::UInt32(value)) }
	pub fn const_uint64 (&mut self, value: u64) -> IrResult<&mut Ir> { self.constant(Constant::UInt64(value)) }
	pub fn const_uint128 (&mut self, value: u128) -> IrResult<&mut Ir> { self.constant(Constant::UInt128(value)) }
	pub fn const_real32 (&mut self, value: f32) -> IrResult<&mut Ir> { self.constant(Constant::Real32(value)) }
	pub fn const_real64 (&mut self, value: f64) -> IrResult<&mut Ir> { self.constant(Constant::Real64(value)) }

	pub fn const_aggregate<K: AsKey<TyKey>> (&mut self, ty_key: K, indices: Vec<u64>, values: Vec<Constant>) -> IrResult<&mut Ir> {
		let ty_key = ty_key.as_key();

		self.constant(Constant::Aggregate(ty_key, indices, values))
	}

	pub fn build_aggregate<K: AsKey<TyKey>> (&mut self, ty_key: K, indices: Vec<u64>) -> IrResult<&mut Ir> {
		let ty_key = ty_key.as_key();

		self.write_node(IrData::BuildAggregate(ty_key, indices))
	}

	pub fn global_key<K: AsKey<GlobalKey>> (&mut self, key: K) -> IrResult<&mut Ir> {
		let key = key.as_key();

		self.write_node(IrData::GlobalKey(key))
	}

	pub fn function_key<K: AsKey<FunctionKey>> (&mut self, key: K) -> IrResult<&mut Ir> {
		let key = key.as_key();

		self.write_node(IrData::FunctionKey(key))
	}

	pub fn block_key<K: AsKey<BlockKey>> (&mut self, key: K) -> IrResult<&mut Ir> {
		let key = key.as_key();

		self.write_node(IrData::BlockKey(key))
	}

	pub fn arg_key<K: AsKey<ParamKey>> (&mut self, key: K) -> IrResult<&mut Ir> {
		let key = key.as_key();

		self.write_node(IrData::ParamKey(key))
	}

	pub fn local_key<K: AsKey<LocalKey>> (&mut self, key: K) -> IrResult<&mut Ir> {
		let key = key.as_key();

		self.write_node(IrData::LocalKey(key))
	}


	pub fn phi<K: AsKey<TyKey>> (&mut self, key: K) -> IrResult<&mut Ir> {
		let key = key.as_key();

		self.write_node(IrData::Phi(key))
	}


	pub fn binary_op (&mut self, op: BinaryOp) -> IrResult<&mut Ir> {
		self.write_node(IrData::BinaryOp(op))
	}

	pub fn unary_op (&mut self, op: UnaryOp) -> IrResult<&mut Ir> {
		self.write_node(IrData::UnaryOp(op))
	}

	pub fn cast_op<K: AsKey<TyKey>> (&mut self, op: CastOp, ty_key: K) -> IrResult<&mut Ir> {
		let ty_key = ty_key.as_key();

		self.write_node(IrData::CastOp(op, ty_key))
	}


	pub fn gep (&mut self) -> IrResult<&mut Ir> {
		self.write_node(IrData::Gep)
	}

	pub fn static_gep (&mut self, indices: Vec<u64>) -> IrResult<&mut Ir> {
		self.write_node(IrData::StaticGep(indices))
	}

	pub fn load (&mut self) -> IrResult<&mut Ir> {
		self.write_node(IrData::Load)
	}

	pub fn store (&mut self) -> IrResult<&mut Ir> {
		self.write_node(IrData::Store)
	}


	pub fn branch<K: AsKey<BlockKey>> (&mut self,	destination: K) -> IrResult<&mut Ir> {
		let destination = destination.as_key();

		self.write_node(IrData::Branch(destination))
	}

	pub fn cond_branch<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, then_block: KA, else_block: KB) -> IrResult<&mut Ir> {
		let then_block = then_block.as_key();
		let else_block = else_block.as_key();

		self.write_node(IrData::CondBranch(then_block, else_block))
	}

	pub fn switch (&mut self, case_blocks: Vec<(ConstIr, BlockKey)>) -> IrResult<&mut Ir> {
		self.write_node(IrData::Switch(case_blocks))
	}

	pub fn computed_branch (&mut self, destinations: Vec<BlockKey>) -> IrResult<&mut Ir> {
		self.write_node(IrData::ComputedBranch(destinations))
	}


	pub fn call (&mut self) -> IrResult<&mut Ir> {
		self.write_node(IrData::Call)
	}

	pub fn ret (&mut self) -> IrResult<&mut Ir> {
		self.write_node(IrData::Ret)
	}


	pub fn duplicate (&mut self) -> IrResult<&mut Ir> {
		self.write_node(IrData::Duplicate)
	}

	pub fn discard (&mut self) -> IrResult<&mut Ir> {
		self.write_node(IrData::Discard)
	}


	pub fn unreachable (&mut self) -> IrResult<&mut Ir> {
		self.write_node(IrData::Unreachable)
	}
}