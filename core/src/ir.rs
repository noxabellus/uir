use std::ops;

use crate::slotmap::{ Keyed, KeyedMut, AsKey, Slotmap };

use super::{
	src::{ SrcAttribution, Src, SrcKey, },
	ty::{ Ty, TyKey, TyMeta, TyMetaKey, },
};


crate::slotmap_keyable! {
	ConstIrMeta,
	IrMeta,
	Block,
	Global,
	GlobalMeta,
	Function,
	FunctionMeta,
	Arg,
	ArgMeta,
	Local,
	LocalMeta,
}



#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinaryOp {
	Add, Sub, Mul, Div, Rem,
	Eq, Ne, Lt, Gt, Le, Ge,
	LAnd, LOr,
	BAnd, BOr, BXor,
	LSh, RShA, RShL
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnaryOp {
	Neg, LNot, BNot
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CastOp {
	IntToReal,
	RealToInt,
	ZeroExtend,
	SignExtend,
	Truncate,
	Bitcast,
}


#[derive(Debug)]
pub enum Constant {
	Null,
	Bool(bool),
	SInt8(i8),
	SInt16(i16),
	SInt32(i32),
	SInt64(i64),
	SInt128(i128),
	UInt8(u8),
	UInt16(u16),
	UInt32(u32),
	UInt64(u64),
	UInt128(u128),
	Real32(f32),
	Real64(f64),
	Aggregate(TyKey, Vec<u64>, Vec<Constant>),
}

#[derive(Debug)]
pub enum ConstIrData {
	Constant(Constant),
	BinaryOp(BinaryOp, Box<Constant>),
	UnaryOp(UnaryOp, Box<Constant>),
	CastOp(CastOp, TyKey, Box<Constant>),
}

impl Default for ConstIrData { fn default () -> Self { Self::Constant(Constant::Null) } }

#[derive(Debug, Default)]
pub struct ConstIr {
	pub name: Option<String>,
	pub data: ConstIrData,
	pub meta: Vec<ConstIrMetaKey>,
	pub src: Option<SrcAttribution>,
}

impl From<ConstIrData> for ConstIr {
	fn from (data: ConstIrData) -> ConstIr { ConstIr { data, .. Self::default() } }
}

impl ops::Deref for ConstIr {
	type Target = ConstIrData;
	fn deref (&self) -> &ConstIrData { &self.data }
}

impl ops::DerefMut for ConstIr {
	fn deref_mut (&mut self) -> &mut ConstIrData { &mut self.data }
}

#[derive(Debug)]
pub enum ConstIrMeta {
	User(String)
}

#[derive(Debug)]
pub enum IrData {
	Constant(Constant),

	BuildAggregate(TyKey, Vec<u64>),

	GlobalKey(GlobalKey),
	FunctionKey(FunctionKey),
	BlockKey(BlockKey),
	ArgKey(ArgKey),
	LocalKey(LocalKey),

	BinaryOp(BinaryOp),
	UnaryOp(UnaryOp),
	CastOp(CastOp, TyKey),

	Gep,
	StaticGep(Vec<u64>),
	Load,
	Store,

	Branch(BlockKey),
	CondBranch(BlockKey, BlockKey),
	Switch(Vec<(ConstIr, BlockKey)>),
	ComputedBranch(Vec<BlockKey>),

	Call,
	Ret,

	Duplicate,
	Discard,

	Unreachable,
}

impl Default for IrData { fn default () -> Self { Self::Constant(Constant::Null) } }


#[derive(Debug, Default)]
pub struct Ir {
	pub name: Option<String>,
	pub data: IrData,
	pub meta: Vec<IrMetaKey>,
	pub src: Option<SrcAttribution>,
}

impl From<IrData> for Ir {
	fn from (data: IrData) -> Ir { Ir { data, .. Self::default() } }
}

impl ops::Deref for Ir {
	type Target = IrData;
	fn deref (&self) -> &IrData { &self.data }
}

impl ops::DerefMut for Ir {
	fn deref_mut (&mut self) -> &mut IrData { &mut self.data }
}

#[derive(Debug)]
pub enum IrMeta {
	User(String)
}


#[derive(Debug, Default)]
pub struct Arg {
	pub name: Option<String>,
	pub ty: TyKey,
	pub src: Option<SrcAttribution>,
	pub meta: Vec<ArgMetaKey>,
}

#[derive(Debug)]
pub enum ArgMeta {
	User(String)
}


#[derive(Debug, Default)]
pub struct Local {
	pub name: Option<String>,
	pub ty: TyKey,
	pub src: Option<SrcAttribution>,
	pub meta: Vec<LocalMetaKey>,
}

#[derive(Debug)]
pub enum LocalMeta {
	User(String)
}

#[derive(Debug, Default)]
pub struct Block {
	pub name: Option<String>,
	pub ir: Vec<Ir>,
}

#[derive(Debug, Default)]
pub struct Function {
	pub name: Option<String>,
	pub ty: TyKey,
	pub blocks: Slotmap<BlockKey, Block>,
	pub ir: Vec<BlockKey>,
	pub src: Option<SrcAttribution>,
	pub meta: Vec<FunctionMetaKey>,
	pub args: Slotmap<ArgKey, Arg>,
	pub locals: Slotmap<LocalKey, Local>,
}

#[derive(Debug)]
pub enum FunctionMeta {
	User(String)
}


#[derive(Debug)]
pub struct Global {
	pub name: Option<String>,
	pub ty: Ty,
	pub ir: Vec<Ir>,
	pub src: Option<SrcAttribution>,
	pub meta: Vec<GlobalMetaKey>,
}

#[derive(Debug)]
pub enum GlobalMeta {
	User(String)
}



#[derive(Debug)]
pub struct Meta {
	pub ty: Slotmap<TyMetaKey, TyMeta>,
	pub function: Slotmap<FunctionMetaKey, FunctionMeta>,
	pub arg: Slotmap<ArgMetaKey, ArgMeta>,
	pub local: Slotmap<LocalMetaKey, LocalMeta>,
	pub global: Slotmap<GlobalMetaKey, GlobalMeta>,
	pub ir: Slotmap<IrMetaKey, IrMeta>,
}

#[derive(Debug)]
pub struct Context {
	pub srcs: Slotmap<SrcKey, Src>,

	pub tys: Slotmap<TyKey, Ty>,
	pub functions: Slotmap<FunctionKey, Function>,
	pub globals: Slotmap<GlobalKey, Global>,

	pub meta: Meta,
}


#[derive(Debug)]
pub enum IrErr {
	NoActiveBlock,
	ExpectedAggregateTy(TyKey),
	InvalidAggregateIndex(TyKey, u64),
	InvalidBlockKey(BlockKey),
	InvalidTyKey(TyKey),
	InvalidNodeIndex(usize),
}

pub type IrResult<T = ()> = Result<T, IrErr>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
pub struct FunctionBuilder<'c> {
	pub ctx: &'c mut Context,

	pub function_key: FunctionKey,
	pub function: Function,

	pub active_block: Option<BlockKey>,
	pub insertion_cursor: InsertionCursor,
	pub active_src: Option<SrcAttribution>,
}

impl<'c> FunctionBuilder<'c> {
	pub fn new<K: AsKey<TyKey>> (ctx: &'c mut Context, ty_key: K) -> Self {
		let ty = ty_key.as_key();

		let function_key = ctx.functions.reserve();

		let function = Function { ty, ..Function::default() };

		Self {
			ctx,

			function_key,
			function,

			active_block: None,
			insertion_cursor: InsertionCursor::End,
			active_src: None
		}
	}






	pub fn get_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<&Ty> {
		let ty_key = ty_key.as_key();
		self.ctx.tys.get(ty_key).ok_or(IrErr::InvalidTyKey(ty_key))
	}

	pub fn get_ty_mut<K: AsKey<TyKey>> (&mut self, ty_key: K) -> IrResult<&mut Ty> {
		let ty_key = ty_key.as_key();
		self.ctx.tys.get_mut(ty_key).ok_or(IrErr::InvalidTyKey(ty_key))
	}




	pub fn make_local<K: AsKey<TyKey>> (&mut self, ty_key: K) -> KeyedMut<Local> {
		let ty = ty_key.as_key();

		self.function.locals.insert(Local { ty, .. Local::default() })
	}




	pub fn make_arg<K: AsKey<TyKey>> (&mut self, ty_key: K) -> KeyedMut<Arg> {
		let ty = ty_key.as_key();

		self.function.args.insert(Arg { ty, .. Arg::default() })
	}




	pub fn append_block (&mut self, block: Block) -> KeyedMut<Block> {
		let block = self.function.blocks.insert(block);
		self.function.ir.push(block.as_key());
		block
	}

	pub fn insert_block (&mut self, idx: usize, block: Block) -> KeyedMut<Block> {
		let block = self.function.blocks.insert(block);
		self.function.ir.insert(idx, block.as_key());
		block
	}

	pub fn append_new_block (&mut self) -> KeyedMut<Block> {
		self.append_block(Block::default())
	}

	pub fn insert_new_block (&mut self, idx: usize) -> KeyedMut<Block> {
		self.insert_block(idx, Block::default())
	}

	pub fn remove_block<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrResult<Block> {
		let block_key = block_key.as_key();

		let idx = self.get_block_index(block_key)?;

		self.function.ir.remove(idx);
		let block = self.function.blocks.remove(block_key).unwrap();

		if self.active_block == Some(block_key) {
			self.insertion_cursor.take();
			self.active_block.take();
		}

		Ok(block)
	}


	pub fn move_block_to_start<K: AsKey<BlockKey>> (&mut self, block_to_move: K) -> IrResult {
		let block_to_move = block_to_move.as_key();

		let idx_to_move = self.get_block_index(block_to_move)?;

		self.function.ir.remove(idx_to_move);
		self.function.ir.insert(0, block_to_move);

		Ok(())
	}

	pub fn move_block_to_end<K: AsKey<BlockKey>> (&mut self, block_to_move: K) -> IrResult {
		let block_to_move = block_to_move.as_key();

		let idx_to_move = self.get_block_index(block_to_move)?;

		self.function.ir.remove(idx_to_move);
		self.function.ir.push(block_to_move);

		Ok(())
	}

	pub fn move_block_before<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, block_to_move: KA, destination_block: KB) -> IrResult {
		let block_to_move = block_to_move.as_key();
		let destination_block = destination_block.as_key();

		let idx_to_move = self.get_block_index(block_to_move)?;
		let destination_idx = self.get_block_index(destination_block)?;

		self.function.ir.remove(idx_to_move);
		self.function.ir.insert(destination_idx, block_to_move);

		Ok(())
	}

	pub fn move_block_after<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, block_to_move: KA, destination_block: KB) -> IrResult {
		let block_to_move = block_to_move.as_key();
		let destination_block = destination_block.as_key();

		let idx_to_move = self.get_block_index(block_to_move)?;
		let destination_idx = self.get_block_index(destination_block)?;

		self.function.ir.remove(idx_to_move);
		self.function.ir.insert(destination_idx + 1, block_to_move);

		Ok(())
	}

	pub fn swap_blocks<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, a: KA, b: KB) -> IrResult {
		let a = self.get_block_index(a)?;
		let b = self.get_block_index(b)?;

		self.function.ir.swap(a, b);

		Ok(())
	}


	pub fn get_block_index<K: AsKey<BlockKey>> (&self, block_key: K) -> IrResult<usize> {
		let block_key = block_key.as_key();

		self.function.ir
			.iter()
			.enumerate()
			.find(|&(_, &br)| br == block_key)
			.map(|(i, _)| i)
			.ok_or(IrErr::InvalidBlockKey(block_key))
	}

	pub fn get_block<K: AsKey<BlockKey>> (&self, block_key: K) -> IrResult<Keyed<Block>> {
		let block_key = block_key.as_key();
		self.function.blocks.get_keyed(block_key).ok_or(IrErr::InvalidBlockKey(block_key))
	}

	pub fn get_block_mut<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrResult<KeyedMut<Block>> {
		let block_key = block_key.as_key();
		self.function.blocks.get_keyed_mut(block_key).ok_or(IrErr::InvalidBlockKey(block_key))
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

	pub fn arg_key<K: AsKey<ArgKey>> (&mut self, key: K) -> IrResult<&mut Ir> {
		let key = key.as_key();

		self.write_node(IrData::ArgKey(key))
	}

	pub fn local_key<K: AsKey<LocalKey>> (&mut self, key: K) -> IrResult<&mut Ir> {
		let key = key.as_key();

		self.write_node(IrData::LocalKey(key))
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