use std::{fmt, ops};

use support::slotmap::{ Slotmap, KeyedMut,  };

use super::{
	src::{ SrcAttribution, Src, SrcKey, },
	ty::{ Ty, TyKey, TyMeta, TyMetaKey, },
	cfg::Cfg,
	target::Target,
};


support::slotmap_keyable! {
	ConstIrMeta,
	IrMeta,
	Block,
	Global,
	GlobalMeta,
	Function,
	FunctionMeta,
	Param,
	ParamMeta,
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
	SIntToUInt,
	UIntToSInt,
	ZeroExtend,
	SignExtend,
	Truncate,
	Bitcast,
}


#[derive(Debug, Clone, Copy)]
pub enum Constant {
	Null(TyKey),
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
}

impl Constant {
	pub fn into_index (self) -> Option<u64> {
		use Constant::*;

		Some(match self {
			SInt8(x) if x >= 0 => { x as u64 }
			SInt16(x) if x >= 0 => { x as u64 }
			SInt32(x) if x >= 0 => { x as u64 }
			SInt64(x) if x >= 0 => { x as u64 }
			SInt128(x) if x >= 0 && x <= u64::MAX as i128 => { x as u64 }
			UInt8(x) => { x as u64 }
			UInt16(x) => { x as u64 }
			UInt32(x) => { x as u64 }
			UInt64(x) => { x as u64 }
			UInt128(x) if x < u64::MAX as u128 => { x as u64 }
			_ => return None
		})
	}
}

#[derive(Debug, Clone)]
pub enum ConstIrData {
	Constant(Constant),
	BinaryOp(BinaryOp, Box<Constant>, Box<Constant>),
	UnaryOp(UnaryOp, Box<Constant>),
	CastOp(CastOp, TyKey, Box<Constant>),
}

impl Default for ConstIrData { fn default () -> Self { Self::Constant(Constant::Null(TyKey::default())) } }

#[derive(Debug, Clone, Default)]
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

#[derive(Debug, Clone)]
pub enum IrData {
	Constant(Constant),

	BuildAggregate(TyKey, Vec<u64>),

	GlobalKey(GlobalKey),
	FunctionKey(FunctionKey),
	BlockKey(BlockKey),
	ParamKey(ParamKey),
	LocalKey(LocalKey),

	Phi(TyKey),

	BinaryOp(BinaryOp),
	UnaryOp(UnaryOp),
	CastOp(CastOp, TyKey),

	Gep(u64),
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

impl Default for IrData { fn default () -> Self { Self::Constant(Constant::Null(TyKey::default())) } }


impl IrData {
	pub fn is_terminator (&self) -> bool {
		use IrData::*;

		matches!(self,
			  Branch { .. }
			| CondBranch { .. }
			| Switch { .. }
			| ComputedBranch { .. }
			| Ret
			| Unreachable
		)
	}

	pub fn for_each_edge<E: fmt::Debug, F: FnMut (BlockKey) -> Result<(), E>>  (&self, mut f: F) -> Result<(), E> {
		use IrData::*;

		match self {
			Branch(dest) => {
				f(*dest)?;
			}

			CondBranch(then_dest, else_dest) => {
				f(*then_dest)?;
				f(*else_dest)?;
			}

			Switch(cases) => {
				for (_, dest) in cases.iter() {
					f(*dest)?;
				}
			}

			ComputedBranch(dests) => {
				for dest in dests.iter() {
					f(*dest)?;
				}
			}

			_ => { }
		}

		Ok(())
	}
}


#[derive(Debug, Clone, Default)]
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


#[derive(Debug, Clone, Default)]
pub struct Param {
	pub name: Option<String>,
	pub ty: TyKey,
	pub src: Option<SrcAttribution>,
	pub meta: Vec<ParamMetaKey>,
}

#[derive(Debug)]
pub enum ParamMeta {
	User(String)
}


#[derive(Debug, Clone, Default)]
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

#[derive(Debug, Clone, Default)]
pub struct Block {
	pub name: Option<String>,
	pub ir: Vec<Ir>,
}





#[derive(Debug, Clone, Default)]
pub struct Function {
	pub name: Option<String>,
	pub ty: TyKey,
	pub block_data: Slotmap<BlockKey, Block>,
	pub block_order: Vec<BlockKey>,
	pub result: Option<TyKey>,
	pub param_data: Slotmap<ParamKey, Param>,
	pub param_order: Vec<ParamKey>,
	pub locals: Slotmap<LocalKey, Local>,
	pub src: Option<SrcAttribution>,
	pub meta: Vec<FunctionMetaKey>,
	pub cfg: Cfg
}

#[derive(Debug)]
pub enum FunctionMeta {
	User(String)
}


#[derive(Debug)]
pub struct Global {
	pub name: Option<String>,
	pub ty: TyKey,
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
	pub arg: Slotmap<ParamMetaKey, ParamMeta>,
	pub local: Slotmap<LocalMetaKey, LocalMeta>,
	pub global: Slotmap<GlobalMetaKey, GlobalMeta>,
	pub ir: Slotmap<IrMetaKey, IrMeta>,
}

#[derive(Debug)]
pub struct Context {
	pub target: Box<dyn Target>,

	pub srcs: Slotmap<SrcKey, Src>,

	pub tys: Slotmap<TyKey, Ty>,
	pub functions: Slotmap<FunctionKey, Function>,
	pub globals: Slotmap<GlobalKey, Global>,

	pub meta: Meta,
}

impl Context {
	pub fn add_ty (&mut self, ty: Ty) -> KeyedMut<Ty> {
		for (&key, existing_ty) in self.tys.iter_mut() {
			if ty.equivalent(existing_ty) {
				*existing_ty = ty; // handle populating meta data
				return self.tys.get_keyed_mut(key).unwrap()
			}
		}

		self.tys.insert(ty)
	}
}