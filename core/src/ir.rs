use std::{fmt, ops};

use support::slotmap::{KeyedMut, Slotmap, AsKey};

use super::{
	cfg::Cfg,
	src::{Src, SrcAttribution, SrcKey},
	target::Target,
	ty::*,
	ty_checker::TyMap,
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
	RealExtend,
	RealTruncate,
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
			CastOp::RealExtend => write!(f, "real_extend"),
			CastOp::Truncate => write!(f, "truncate"),
			CastOp::RealTruncate => write!(f, "real_truncate"),
			CastOp::Bitcast => write!(f, "bitcast"),
		}
	}
}

#[derive(Debug, Clone)]
pub enum ConstantAggregateData {
	Uninitialized,
	Zeroed,
	CopyFill(Box<Constant>),
	Indexed(Vec<(u32, Constant)>),
	Complete(Vec<Constant>),
}

#[derive(Debug, Clone)]
pub enum AggregateData {
	Uninitialized,
	Zeroed,
	CopyFill,
	Indexed(Vec<u32>),
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

impl From<bool> for Constant { fn from (v: bool) -> Constant { Constant::Bool(v)    } }

impl From<i8>   for Constant { fn from (v: i8) -> Constant   { Constant::SInt8(v)   } }
impl From<i16>  for Constant { fn from (v: i16) -> Constant  { Constant::SInt16(v)  } }
impl From<i32>  for Constant { fn from (v: i32) -> Constant  { Constant::SInt32(v)  } }
impl From<i64>  for Constant { fn from (v: i64) -> Constant  { Constant::SInt64(v)  } }
impl From<i128> for Constant { fn from (v: i128) -> Constant { Constant::SInt128(v) } }

impl From<u8>   for Constant { fn from (v: u8) -> Constant   { Constant::UInt8(v)   } }
impl From<u16>  for Constant { fn from (v: u16) -> Constant  { Constant::UInt16(v)  } }
impl From<u32>  for Constant { fn from (v: u32) -> Constant  { Constant::UInt32(v)  } }
impl From<u64>  for Constant { fn from (v: u64) -> Constant  { Constant::UInt64(v)  } }
impl From<u128> for Constant { fn from (v: u128) -> Constant { Constant::UInt128(v) } }

impl From<f32>  for Constant { fn from (v: f32) -> Constant  { Constant::Real32(v)  } }
impl From<f64>  for Constant { fn from (v: f64) -> Constant  { Constant::Real64(v)  } }



impl Constant {
	pub fn as_index(&self) -> Option<u32> {
		use Constant::*;

		Some(match *self {
			SInt8(x) if x >= 0 => x as u32,
			SInt16(x) if x >= 0 => x as u32,
			SInt32(x) if x >= 0 => x as u32,
			SInt64(x) if x >= 0 && (x <= u32::MAX as i64) => x as u32,
			SInt128(x) if x >= 0 && x <= u32::MAX as i128 => x as u32,
			UInt8(x) => x as u32,
			UInt16(x) => x as u32,
			UInt32(x) => x as u32,
			UInt64(x) if x <= u32::MAX as u64 => x as u32,
			UInt128(x) if x < u32::MAX as u128 => x as u32,
			_ => return None,
		})
	}
}

#[derive(Debug, Clone)]
pub enum IrData {
	Constant(Constant),

	BuildAggregate(TyKey, AggregateData),
	SetElement(u32),
	GetElement(u32),

	GlobalRef(GlobalKey),
	FunctionRef(FunctionKey),
	BlockRef(BlockKey),
	ParamRef(ParamKey),
	LocalRef(LocalKey),

	Phi(TyKey),

	BinaryOp(BinaryOp),
	UnaryOp(UnaryOp),
	CastOp(CastOp, TyKey),

	Gep(u32),
	Load,
	Store,

	Branch(BlockKey),
	CondBranch(BlockKey, BlockKey),
	Switch(Vec<(Constant, BlockKey)>, BlockKey),
	ComputedBranch(Vec<BlockKey>),

	Call,
	Ret,

	Duplicate(u32),
	Discard(u32),
	Swap(u32),

	Unreachable,
}

impl Default for IrData {
	fn default() -> Self {
		Self::Constant(Constant::Null(TyKey::default()))
	}
}

impl IrData {
	pub fn is_init (&self) -> bool {
		matches!(self, IrData::Phi(_))
	}

	pub fn as_init_ty_key (&self) -> Option<TyKey> {
		match self {
			IrData::Phi(ty_key) => Some(*ty_key),
			_ => None
		}
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

			Switch(cases, default) => {
				for (_, dest) in cases.iter() {
					f(*dest)?;
				}

				f(*default)?;
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
	pub ty_map: TyMap,
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
	pub fn is_empty (&self) -> bool {
		   self.ty.is_empty()
		&& self.function.is_empty()
		&& self.param.is_empty()
		&& self.local.is_empty()
		&& self.global.is_empty()
		&& self.ir.is_empty()
	}
}




#[derive(Debug, Default)]
pub struct TyDict {
	pub void: TyKey,
	pub block: TyKey,
	pub bool: TyKey,
	pub sint8: TyKey, pub sint16: TyKey, pub sint32: TyKey, pub sint64: TyKey, pub sint128: TyKey,
	pub uint8: TyKey, pub uint16: TyKey, pub uint32: TyKey, pub uint64: TyKey, pub uint128: TyKey,
	pub real32: TyKey, pub real64: TyKey,
}


#[derive(Debug)]
pub struct Context {
	pub target: Box<dyn Target>,

	pub srcs: Slotmap<SrcKey, Src>,

	pub tys: Slotmap<TyKey, Ty>,
	pub ty_dict: TyDict,
	pub functions: Slotmap<FunctionKey, Function>,
	pub globals: Slotmap<GlobalKey, Global>,

	pub meta: Meta,
}

impl Default for Context { fn default () -> Self { Self::new() } }

impl Context {
	pub fn new () -> Self {
		let mut ctx = Self {
			target: Box::default(),
			srcs: Slotmap::default(),
			tys: Slotmap::default(),
			ty_dict: TyDict::default(),
			functions: Slotmap::default(),
			globals: Slotmap::default(),
			meta: Meta::default(),
		};

		macro_rules! prims {
			($(
				($name:ident : $($tt:tt)+)
			),+ $(,)?) => {
				TyDict {
					$(
						$name: prims!(#ELEM# $name : $($tt)+)
					),+
				}
			};

			(#ELEM# $name:ident : $ty:ident) => {
				ctx.add_ty(Ty {
					data: TyData::Primitive(PrimitiveTy::$ty),
					name: Some(stringify!($name).to_owned()),
					.. Ty::default()
				}).as_key()
			};


			(#ELEM# $name:ident : $expr:expr) => {
				ctx.add_ty(Ty {
					data: $expr,
					name: Some(stringify!($name).to_owned()),
					.. Ty::default()
				}).as_key()
			};
		}


		ctx.ty_dict = prims! [
			(void: TyData::Void),
			(block: TyData::Block),
			(bool: Bool),
			(sint8: SInt8), (sint16: SInt16), (sint32: SInt32), (sint64: SInt64), (sint128: SInt128),
			(uint8: UInt8), (uint16: UInt16), (uint32: UInt32), (uint64: UInt64), (uint128: UInt128),
			(real32: Real32), (real64: Real64),
		];

		ctx
	}

	pub fn with_target<T: 'static + Target> (target: T) -> Self {
		Self {
			target: Box::new(target),
			..Self::default()
		}
	}

	pub(crate) fn add_ty (&mut self, ty: Ty) -> KeyedMut<Ty> {
		self.tys.insert(ty)
	}
}