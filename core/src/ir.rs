use std::{fmt, hint::unreachable_unchecked, ops};

use support::slotmap::{KeyedMut, Slotmap, SlotmapCollapsePredictor};

use super::{
	cfg::Cfg,
	src::{Src, SrcAttribution, SrcKey},
	target::Target,
	ty::{Ty, TyKey, TyMeta, TyMetaKey},
};

support::slotmap_keyable! {
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
	Add,
	Sub,
	Mul,
	Div,
	Rem,
	Eq,
	Ne,
	Lt,
	Gt,
	Le,
	Ge,
	LAnd,
	LOr,
	BAnd,
	BOr,
	BXor,
	LSh,
	RShA,
	RShL,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnaryOp {
	Neg,
	LNot,
	BNot,
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

impl fmt::Display for BinaryOp {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			BinaryOp::Add => write!(f, "add"),
			BinaryOp::Sub => write!(f, "sub"),
			BinaryOp::Mul => write!(f, "mul"),
			BinaryOp::Div => write!(f, "div"),
			BinaryOp::Rem => write!(f, "rem"),
			BinaryOp::Eq => write!(f, "eq"),
			BinaryOp::Ne => write!(f, "ne"),
			BinaryOp::Lt => write!(f, "lt"),
			BinaryOp::Gt => write!(f, "gt"),
			BinaryOp::Le => write!(f, "le"),
			BinaryOp::Ge => write!(f, "ge"),
			BinaryOp::LAnd => write!(f, "land"),
			BinaryOp::LOr => write!(f, "lor"),
			BinaryOp::BAnd => write!(f, "band"),
			BinaryOp::BOr => write!(f, "bor"),
			BinaryOp::BXor => write!(f, "bxor"),
			BinaryOp::LSh => write!(f, "lsh"),
			BinaryOp::RShA => write!(f, "rsha"),
			BinaryOp::RShL => write!(f, "rshl"),
		}
	}
}

impl fmt::Display for UnaryOp {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			UnaryOp::Neg => write!(f, "neg"),
			UnaryOp::LNot => write!(f, "lnot"),
			UnaryOp::BNot => write!(f, "bnot"),
		}
	}
}

impl fmt::Display for CastOp {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			CastOp::IntToReal => write!(f, "int_to_real"),
			CastOp::RealToInt => write!(f, "real_to_int"),
			CastOp::ZeroExtend => write!(f, "zero_extend"),
			CastOp::SignExtend => write!(f, "sign_extend"),
			CastOp::Truncate => write!(f, "truncate"),
			CastOp::Bitcast => write!(f, "bitcast"),
		}
	}
}

#[derive(Debug, Clone)]
pub enum ConstantAggregateData {
	Uninitialized,
	Zeroed,
	CopyFill(Box<Constant>),
	Indexed(Vec<(u64, Constant)>),
	Complete(Vec<Constant>),
}

#[derive(Debug, Clone)]
pub enum AggregateData {
	Uninitialized,
	Zeroed,
	CopyFill,
	Indexed(Vec<u64>),
	Complete,
}

#[derive(Debug, Clone)]
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
	Aggregate(TyKey, ConstantAggregateData),
}

impl Constant {
	pub fn as_index(&self) -> Option<u64> {
		use Constant::*;

		Some(match *self {
			SInt8(x) if x >= 0 => x as u64,
			SInt16(x) if x >= 0 => x as u64,
			SInt32(x) if x >= 0 => x as u64,
			SInt64(x) if x >= 0 => x as u64,
			SInt128(x) if x >= 0 && x <= u64::MAX as i128 => x as u64,
			UInt8(x) => x as u64,
			UInt16(x) => x as u64,
			UInt32(x) => x as u64,
			UInt64(x) => x,
			UInt128(x) if x < u64::MAX as u128 => x as u64,
			_ => return None,
		})
	}
}

#[derive(Debug, Clone)]
pub enum IrData {
	Constant(Constant),

	BuildAggregate(TyKey, AggregateData),

	GlobalRef(GlobalKey),
	FunctionRef(FunctionKey),
	BlockRef(BlockKey),
	ParamRef(ParamKey),
	LocalRef(LocalKey),

	Phi(TyKey),

	BinaryOp(BinaryOp),
	UnaryOp(UnaryOp),
	CastOp(CastOp, TyKey),

	Gep(u64),
	Load,
	Store,

	Branch(BlockKey),
	CondBranch(BlockKey, BlockKey),
	Switch(Vec<(Constant, BlockKey)>),
	ComputedBranch(Vec<BlockKey>),

	Call,
	Ret,

	Duplicate,
	Discard,
	Swap,

	Unreachable,
}

impl Default for IrData {
	fn default() -> Self {
		Self::Constant(Constant::Null(TyKey::default()))
	}
}

impl IrData {
	pub fn is_phi (&self) -> bool {
		matches!(self, IrData::Phi(_))
	}

	pub fn is_terminator (&self) -> bool {
		use IrData::*;

		matches!(
			self,
			  Branch { .. }
			| CondBranch { .. }
			| Switch { .. }
			| ComputedBranch { .. }
			| Ret
			| Unreachable
		)
	}

	pub fn for_each_edge<E: fmt::Debug, F: FnMut(BlockKey) -> Result<(), E>>(
		&self,
		mut f: F,
	) -> Result<(), E> {
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

			_ => {}
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
	fn from(data: IrData) -> Ir {
		Ir {
			data,
			..Self::default()
		}
	}
}

impl ops::Deref for Ir {
	type Target = IrData;
	fn deref(&self) -> &IrData {
		&self.data
	}
}

impl ops::DerefMut for Ir {
	fn deref_mut(&mut self) -> &mut IrData {
		&mut self.data
	}
}

#[derive(Debug)]
pub enum IrMeta {
	User(String),
}

impl fmt::Display for IrMeta {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			IrMeta::User(str) => write!(f, "{}", str.escape_debug())
		}
	}
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
	User(String),
}

impl fmt::Display for ParamMeta {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			ParamMeta::User(str) => write!(f, "{}", str.escape_debug())
		}
	}
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
	User(String),
}

impl fmt::Display for LocalMeta {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			LocalMeta::User(str) => write!(f, "{}", str.escape_debug())
		}
	}
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
	pub cfg: Cfg,
}

#[derive(Debug)]
pub enum FunctionMeta {
	User(String),
}

impl fmt::Display for FunctionMeta {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			FunctionMeta::User(str) => write!(f, "{}", str.escape_debug())
		}
	}
}

#[derive(Debug, Default)]
pub struct Global {
	pub name: Option<String>,
	pub ty: TyKey,
	pub init: Option<Constant>,
	pub src: Option<SrcAttribution>,
	pub meta: Vec<GlobalMetaKey>,
}

#[derive(Debug)]
pub enum GlobalMeta {
	User(String),
}

impl fmt::Display for GlobalMeta {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			GlobalMeta::User(str) => write!(f, "{}", str.escape_debug())
		}
	}
}

#[derive(Debug, Default)]
pub struct Meta {
	pub ty: Slotmap<TyMetaKey, TyMeta>,
	pub function: Slotmap<FunctionMetaKey, FunctionMeta>,
	pub param: Slotmap<ParamMetaKey, ParamMeta>,
	pub local: Slotmap<LocalMetaKey, LocalMeta>,
	pub global: Slotmap<GlobalMetaKey, GlobalMeta>,
	pub ir: Slotmap<IrMetaKey, IrMeta>,
}

impl Meta {
	pub fn predict_collapse (&self) -> MetaCollapsePredictor<'_> {
		MetaCollapsePredictor {
			ty: self.ty.predict_collapse(),
			function: self.function.predict_collapse(),
			param: self.param.predict_collapse(),
			local: self.local.predict_collapse(),
			global: self.global.predict_collapse(),
			ir: self.ir.predict_collapse(),
		}
	}
}



#[derive(Debug, Default)]
pub struct Context {
	pub target: Box<dyn Target>,

	pub srcs: Slotmap<SrcKey, Src>,

	pub tys: Slotmap<TyKey, Ty>,
	pub functions: Slotmap<FunctionKey, Function>,
	pub globals: Slotmap<GlobalKey, Global>,

	pub meta: Meta,
}

impl Context {
	pub fn new() -> Self {
		Self::default()
	}

	pub fn with_target<T: 'static + Target>(target: T) -> Self {
		Self {
			target: Box::new(target),
			..Self::default()
		}
	}

	pub(crate) fn add_ty(&mut self, ty: Ty) -> KeyedMut<Ty> {
		self.tys.insert(ty)
	}

	pub fn predict_collapse (&self) -> ContextCollapsePredictor<'_> {
		ContextCollapsePredictor {
			context: self,

			srcs: self.srcs.predict_collapse(),

			tys: self.tys.predict_collapse(),
			functions: self.functions.predict_collapse(),
			globals: self.globals.predict_collapse(),

			meta: self.meta.predict_collapse(),
		}
	}
}



#[derive(Debug)]
pub struct MetaCollapsePredictor<'c> {
	pub ty: SlotmapCollapsePredictor<'c, TyMetaKey, TyMeta>,
	pub function: SlotmapCollapsePredictor<'c, FunctionMetaKey, FunctionMeta>,
	pub param: SlotmapCollapsePredictor<'c, ParamMetaKey, ParamMeta>,
	pub local: SlotmapCollapsePredictor<'c, LocalMetaKey, LocalMeta>,
	pub global: SlotmapCollapsePredictor<'c, GlobalMetaKey, GlobalMeta>,
	pub ir: SlotmapCollapsePredictor<'c, IrMetaKey, IrMeta>,
}

impl<'c> MetaCollapsePredictor<'c> {
	pub fn is_empty (&self) -> bool {
		   self.ty.is_empty()
		&& self.function.is_empty()
		&& self.param.is_empty()
		&& self.local.is_empty()
		&& self.global.is_empty()
		&& self.ir.is_empty()
	}
}


#[derive(Debug)]
pub struct ContextCollapsePredictor<'c> {
	pub context: &'c Context,

	pub srcs: SlotmapCollapsePredictor<'c, SrcKey, Src>,

	pub tys: SlotmapCollapsePredictor<'c, TyKey, Ty>,
	pub functions: SlotmapCollapsePredictor<'c, FunctionKey, Function>,
	pub globals: SlotmapCollapsePredictor<'c, GlobalKey, Global>,

	pub meta: MetaCollapsePredictor<'c>
}

impl<'c> ContextCollapsePredictor<'c> {
	pub fn function_predictor (&self, key: FunctionKey) -> Option<FunctionCollapsePredictor<'c>> {
		if let Some(index) = self.functions.get_index(key) {
			if let Some(value) = self.context.functions.get(key) {
				return Some(value.predict_collapse(index, key))
			} else {
				// SAFETY: if there is an index there must be a value
				unsafe { unreachable_unchecked() }
			}
		} else {
			None
		}
	}
}


#[derive(Debug)]
pub struct FunctionCollapsePredictor<'c> {
	pub function: &'c Function,
	pub own_index: usize,
	pub own_key: FunctionKey,
	pub locals: SlotmapCollapsePredictor<'c, LocalKey, Local>,
}

impl<'c> ops::Deref for FunctionCollapsePredictor<'c> {
	type Target = Function;
	fn deref (&self) -> &Self::Target {
		&self.function
	}
}

impl Function {
	pub fn predict_collapse (&self, own_index: usize, own_key: FunctionKey,) -> FunctionCollapsePredictor<'_> {
		FunctionCollapsePredictor {
			function: self,
			own_index,
			own_key,
			locals: self.locals.predict_collapse()
		}
	}
}