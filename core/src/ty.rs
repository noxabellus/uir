use std::{ fmt, cell::RefCell, ops };

use super::{
	src::SrcAttribution,
	ir::{ UnaryOp, BinaryOp, CastOp, BlockKey, Constant, },
};


support::slotmap_keyable! { Ty, TyMeta }


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TyErr {
	StackUnderflow,
	ExpectedConstant,
	GepNoIndices,
	TypeHasNoNull(TyKey),
	PhiMissingInPredecessor(BlockKey),
	PhiTypeMismatch(BlockKey, TyKey, TyKey),
	PhiNoPredecessors(BlockKey),
	UnusedValues(BlockKey, usize),
	UnusedValuesNoSuccessor(BlockKey, usize),
	GepTargetNotPointer(TyKey),
	GepInvalidSubElement(usize, TyKey),
	GepImplicitLoad(usize, TyKey),
	GepInvalidIndex(usize, TyKey),
	GepOutOfBounds(usize, TyKey, u32, u32),
	ExpectedTy(TyKey, TyKey),
	ExpectedArray(TyKey),
	ExpectedStructure(TyKey),
	ExpectedEmptyStructure(TyKey),
	ExpectedFunction(TyKey),
	ExpectedBlock(TyKey),
	ExpectedPointer(TyKey),
	ExpectedAggregateTy(TyKey),
	ExpectedInteger(TyKey),
	InvalidSwitchTy(TyKey),
	DuplicateAggregateIndex(usize, usize, u32),
	InvalidAggregateIndex(TyKey, u32),
	MissingAggregateElement(TyKey, u32),
	ExpectedAggregateElementTy(TyKey, u32, TyKey, TyKey),
	BinaryOpTypeMismatch(TyKey, TyKey),
	BinaryOpInvalidOperandTy(BinaryOp, TyKey),
	UnaryOpInvalidOperandTy(UnaryOp, TyKey),
	InvalidCast(CastOp, TyKey, TyKey)
}

pub type TyResult<T = ()> = Result<T, TyErr>;


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveTy {
	Bool,
	SInt8, SInt16, SInt32, SInt64, SInt128,
	UInt8, UInt16, UInt32, UInt64, UInt128,
	Real32, Real64,
}

impl PrimitiveTy {
	pub fn const_from_int (self, int: usize) -> Constant {
		match self {
			PrimitiveTy::Bool => Constant::Bool(int != 0),

			PrimitiveTy::SInt8   => Constant::SInt8(int as _),
			PrimitiveTy::SInt16  => Constant::SInt16(int as _),
			PrimitiveTy::SInt32  => Constant::SInt32(int as _),
			PrimitiveTy::SInt64  => Constant::SInt64(int as _),
			PrimitiveTy::SInt128 => Constant::SInt128(int as _),

			PrimitiveTy::UInt8   => Constant::UInt8(int as _),
			PrimitiveTy::UInt16  => Constant::UInt16(int as _),
			PrimitiveTy::UInt32  => Constant::UInt32(int as _),
			PrimitiveTy::UInt64  => Constant::UInt64(int as _),
			PrimitiveTy::UInt128 => Constant::UInt128(int as _),

			PrimitiveTy::Real32 => Constant::Real32(int as _),
			PrimitiveTy::Real64 => Constant::Real64(int as _),
		}
	}

	pub fn const_zero (self) -> Constant {
		match self {
			PrimitiveTy::Bool => Constant::Bool(false),

			PrimitiveTy::SInt8   => Constant::SInt8(0),
			PrimitiveTy::SInt16  => Constant::SInt16(0),
			PrimitiveTy::SInt32  => Constant::SInt32(0),
			PrimitiveTy::SInt64  => Constant::SInt64(0),
			PrimitiveTy::SInt128 => Constant::SInt128(0),

			PrimitiveTy::UInt8   => Constant::UInt8(0),
			PrimitiveTy::UInt16  => Constant::UInt16(0),
			PrimitiveTy::UInt32  => Constant::UInt32(0),
			PrimitiveTy::UInt64  => Constant::UInt64(0),
			PrimitiveTy::UInt128 => Constant::UInt128(0),

			PrimitiveTy::Real32 => Constant::Real32(0.),
			PrimitiveTy::Real64 => Constant::Real64(0.),
		}
	}

	pub fn size (self) -> usize {
		use PrimitiveTy::*;
		match self {
			Bool | SInt8 | UInt8 => 1,
			SInt16 | UInt16 => 2,
			Real32 | SInt32 | UInt32 => 4,
			Real64 | SInt64 | UInt64 => 8,
			SInt128 | UInt128 => 16,
		}
	}

	pub fn as_str (self) -> &'static str {
		use PrimitiveTy::*;
		match self {
			Bool => "bool",
			SInt8 => "sint8",
			SInt16 => "sint16",
			SInt32 => "sint32",
			SInt64 => "sint64",
			SInt128 => "sint128",
			UInt8 => "uint8",
			UInt16 => "uint16",
			UInt32 => "uint32",
			UInt64 => "uint64",
			UInt128 => "uint128",
			Real32 => "real32",
			Real64 => "real64",
		}
	}
}

impl fmt::Display for PrimitiveTy {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", self.as_str())
	}
}


#[derive(Debug, PartialEq, Eq)]
pub enum TyData {
	Void,
	Block,
	Primitive(PrimitiveTy),
	Pointer { target_ty: TyKey },
	Array { length: u32, element_ty: TyKey },
	Structure { field_tys: Vec<TyKey> },
	Function { parameter_tys: Vec<TyKey>, result_ty: Option<TyKey> },
}

impl Default for TyData { fn default () -> Self { Self::Void } }

impl TyData {
	pub fn const_from_int (&self, int: usize) -> Option<Constant> {
		Some(match self {
			TyData::Primitive(prim) => prim.const_from_int(int),
			_ => return None
		})
	}

	pub fn is_block (&self) -> bool { matches!(self, Self::Block) }
	pub fn is_primitive (&self) -> bool { matches!(self, Self::Primitive(_)) }
	pub fn is_void (&self) -> bool { matches!(self, Self::Void) }
	pub fn is_bool (&self) -> bool { matches!(self, Self::Primitive(PrimitiveTy::Bool)) }
	pub fn is_sint (&self) -> bool { matches!(self, Self::Primitive(PrimitiveTy::SInt8) | Self::Primitive(PrimitiveTy::SInt16) | Self::Primitive(PrimitiveTy::SInt32) | Self::Primitive(PrimitiveTy::SInt64) | Self::Primitive(PrimitiveTy::SInt128)) }
	pub fn is_uint (&self) -> bool { matches!(self, Self::Primitive(PrimitiveTy::UInt8) | Self::Primitive(PrimitiveTy::UInt16) | Self::Primitive(PrimitiveTy::UInt32) | Self::Primitive(PrimitiveTy::UInt64) | Self::Primitive(PrimitiveTy::UInt128)) }
	pub fn is_int (&self) -> bool { self.is_sint() || self.is_uint() }
	pub fn is_real (&self) -> bool { matches!(self, Self::Primitive(PrimitiveTy::Real32) | Self::Primitive(PrimitiveTy::Real64)) }
	pub fn is_arithmetic (&self) -> bool { self.is_int() || self.is_real() }
	pub fn has_equality (&self) -> bool { self.is_pointer() || self.is_arithmetic() || self.is_bool() || self.is_function() }
	pub fn is_signed (&self) -> bool { self.is_sint() || self.is_real() }
	pub fn is_pointer (&self) -> bool { matches!(self, Self::Pointer { .. }) }
	pub fn is_array (&self) -> bool { matches!(self, Self::Array { .. }) }
	pub fn is_structure (&self) -> bool { matches!(self, Self::Structure { .. }) }
	pub fn is_function (&self) -> bool { matches!(self, Self::Function { .. }) }

	pub fn is_aggregate (&self) -> bool {
		matches!(self,
			  Self::Array { .. }
			| Self::Structure { .. }
		)
	}

	pub fn is_scalar (&self) -> bool {
		matches!(self,
			  Self::Primitive { .. }
			| Self::Pointer { .. }
			| Self::Function { .. }
			| Self::Block { .. }
		)
	}
}


#[derive(Debug)]
pub enum TyMeta {
	User(String)
}

impl fmt::Display for TyMeta {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			TyMeta::User(str) => write!(f, "{}", str.escape_debug())
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Layout {
	pub size: u32,
	pub align: u32,
	pub field_offsets: Vec<u32>,
}

impl Layout {
	pub fn custom_scalar (size: u32, align: u32) -> Self { Self { size, align, field_offsets: vec![] } }
	pub fn scalar (size: u32) -> Self { Self { size, align: size, field_offsets: vec![] } }
	pub fn structure (size: u32, align: u32, field_offsets: Vec<u32>) -> Self { Self { size, align, field_offsets } }
}

#[derive(Debug, Default)]
pub struct Ty {
	pub data: TyData,
	pub name: Option<String>,
	pub meta: Vec<TyMetaKey>,
	pub src: Option<SrcAttribution>,
	pub layout: RefCell<Option<Layout>>,
}

impl From<TyData> for Ty {
	fn from (data: TyData) -> Ty { Ty { data, .. Ty::default() } }
}

impl ops::Deref for Ty {
	type Target = TyData;
	fn deref (&self) -> &TyData { &self.data }
}

impl ops::DerefMut for Ty {
	fn deref_mut (&mut self) -> &mut TyData { &mut self.data }
}

impl Ty {
	pub fn equivalent	(&self, other: &Self) -> bool {
		    other.data == self.data
		&& (other.name.is_none()  || other.name == self.name)
		&& (other.meta.is_empty() || other.meta == self.meta)
		&& (other.src.is_none()   || other.src  == self.src )
		&& (other.layout.borrow().is_none() || other.layout == self.layout)
	}

	pub fn get_pure_intrinsic_name (&self) -> Option<&'static str> {
		let name = Some(match &self.data {
			TyData::Primitive(prim) => prim.as_str(),
			TyData::Void => "void",
			TyData::Block => "block",
			_ => return None
		});

		if self.src.is_none()
		&& self.meta.is_empty()
		&& (self.name.is_none() || self.name.as_deref() == name) {
			name
		} else {
			None
		}
	}

	pub fn is_pure_intrinsic (&self) -> bool {
		self.get_pure_intrinsic_name().is_some()
	}
}