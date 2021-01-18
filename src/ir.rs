use std::{collections::HashSet, fmt, path::PathBuf, u64};

use crate::{
	slotmap::Slotmap,
	slotmap_key_ty
};


slotmap_key_ty! {
	pub struct TyRef;
	pub struct InstrRef;
	pub struct BlockRef;
	pub struct GlobalRef;
	pub struct ArgRef;
	pub struct FunctionRef;
	pub struct SrcRef;
	pub struct TyMetaRef;
	pub struct InstrMetaRef;
	pub struct GlobalMetaRef;
	pub struct ArgMetaRef;
	pub struct FunctionMetaRef;
}




#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SrcAttribution {
	pub id: SrcRef,
	pub range: (u32, u32)
}


#[derive(Debug)]
pub struct Src {
	pub content: String,
	pub path: PathBuf,
	pub lines: Vec<u32>,
}



#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveTy {
	Bool,
	SInt8, SInt16, SInt32, SInt64, SInt128,
	UInt8, UInt16, UInt32, UInt64, UInt128,
	Real32, Real64,
}

#[derive(Debug, PartialEq, Eq)]
pub enum TyData {
	Void,
	Block,
	Primitive(PrimitiveTy),
	Pointer { target_ty: TyRef },
	Array { length: u64, element_ty: TyRef },
	Structure { field_tys: Vec<TyRef> },
	Function { parameter_tys: Vec<TyRef>, result_ty: Option<TyRef> },
}

impl TyData {
	pub fn is_block (&self) -> bool { matches!(self, Self::Block) }
	pub fn is_primitive (&self) -> bool { matches!(self, Self::Primitive(_)) }
	pub fn is_void (&self) -> bool { matches!(self, Self::Void) }
	pub fn is_bool (&self) -> bool { matches!(self, Self::Primitive(PrimitiveTy::Bool)) }
	pub fn is_sint (&self) -> bool { matches!(self, Self::Primitive(PrimitiveTy::SInt8) | Self::Primitive(PrimitiveTy::SInt16) | Self::Primitive(PrimitiveTy::SInt32) | Self::Primitive(PrimitiveTy::SInt64) | Self::Primitive(PrimitiveTy::SInt128)) }
	pub fn is_uint (&self) -> bool { matches!(self, Self::Primitive(PrimitiveTy::UInt8) | Self::Primitive(PrimitiveTy::UInt16) | Self::Primitive(PrimitiveTy::UInt32) | Self::Primitive(PrimitiveTy::UInt64) | Self::Primitive(PrimitiveTy::UInt128)) }
	pub fn is_int (&self) -> bool { self.is_sint() || self.is_uint() }
	pub fn is_real (&self) -> bool { matches!(self, Self::Primitive(PrimitiveTy::Real32) | Self::Primitive(PrimitiveTy::Real64)) }
	pub fn has_sign (&self) -> bool { self.is_sint() || self.is_real() }
	pub fn is_pointer (&self) -> bool { matches!(self, Self::Pointer { .. }) }
	pub fn is_array (&self) -> bool { matches!(self, Self::Array { .. }) }
	pub fn is_structure (&self) -> bool { matches!(self, Self::Structure { .. }) }
	pub fn is_function (&self) -> bool { matches!(self, Self::Function { .. }) }
	pub fn is_aggregate (&self) -> bool {
		match self {
			| Self::Array { .. }
			| Self::Structure { .. }
			=> true,

			| Self::Void { .. }
			| Self::Block { .. }
			| Self::Primitive { .. }
			| Self::Pointer { .. }
			| Self::Function { .. }
			=> false
		}
	}
	pub fn is_scalar (&self) -> bool {
		match self {
			| Self::Primitive { .. }
			| Self::Pointer { .. }
			| Self::Function { .. }
			=> true,

			| Self::Array { .. }
			| Self::Structure { .. }
			| Self::Void { .. }
			| Self::Block { .. }
			=> false
		}
	}
}


#[derive(Debug)]
pub enum TyMeta {
	// BuiltinA, BuiltinB, BuiltinC,
	User(String)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Layout {
	pub size: u64,
	pub align: u64,
	pub field_offsets: Vec<u64>,
}

impl Layout {
	pub fn custom_scalar (size: u64, align: u64) -> Self { Self { size, align, field_offsets: vec![] } }
	pub fn scalar (size: u64) -> Self { Self { size, align: size, field_offsets: vec![] } }
	pub fn structure (size: u64, align: u64, field_offsets: Vec<u64>) -> Self { Self { size, align, field_offsets } }
}

#[derive(Debug)]
pub struct Ty {
	pub data: TyData,
	pub name: Option<String>,
	pub meta: Vec<TyMetaRef>,
	pub src: Option<SrcAttribution>,
	pub layout: Option<Layout>,
}

impl From<TyData> for Ty {
	fn from (td: TyData) -> Ty { Ty { data: td, name: None, meta: vec![], src: None, layout: None } }
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
pub enum CastKind {
	IntToReal,
	RealToInt,
	ZeroExtend,
	SignExtend,
	Truncate,
	Bitcast,
}

#[derive(Debug)]
pub enum InstrData {
	Null,
	Int(i128),
	UInt(u128),
	Real(f64),
	String(String),
	BlockRef(BlockRef),
	GlobalRef(GlobalRef),
	FunctionRef(FunctionRef),
	ArgRef(ArgRef),
	MakeAggregate { elements: Vec<InstrRef> },

	Allocate { length: u64 },
	Load { source: InstrRef },
	Store { destination: InstrRef, value: InstrRef },
	GetElementPtr { ptr: InstrRef, indices: Vec<InstrRef> },
	Cast { kind: CastKind, castee: InstrRef },

	BinaryOp { op: BinaryOp, a: InstrRef, b: InstrRef },
	UnaryOp { op: UnaryOp, operand: InstrRef },
	Call { callee: InstrRef, arguments: Vec<InstrRef> },

	Phi { edges: Vec<(BlockRef, InstrRef)> },
	Branch { destination: BlockRef },
	ConditionalBranch { condition: InstrRef, then_destination: BlockRef, else_destination: BlockRef },
	Switch { condition: InstrRef, branches: Vec<(InstrRef, BlockRef)> },
	ComputedBranch { destination: InstrRef, branches: Vec<BlockRef> },
	Ret { value: Option<InstrRef> },
	Unreachable,
}

impl InstrData {
	pub fn is_const_eval (&self) -> bool {
		use InstrData::*;
		match self {
			| Null { .. }
			| Int { .. }
			| UInt { .. }
			| Real { .. }
			| String { .. }
			| GlobalRef { .. }
			| FunctionRef { .. }
			| MakeAggregate { .. }
			| Cast { .. }
			| BinaryOp { .. }
			| UnaryOp { .. }
			| GetElementPtr { .. }
			| Call { .. }
			=> true,

			| BlockRef { .. }
			| ArgRef { .. }
			| Allocate { .. }
			| Load { .. }
			| Store { .. }
			| Phi { .. }
			| Branch { .. }
			| ConditionalBranch { .. }
			| Switch { .. }
			| ComputedBranch { .. }
			| Ret { .. }
			| Unreachable { .. }
			=> false,
		}
	}

	pub fn can_have_predecessor (&self) -> bool {
		use InstrData::*;
		match self {
			| Null { .. }
			| Int { .. }
			| UInt { .. }
			| Real { .. }
			| String { .. }
			| GlobalRef { .. }
			| FunctionRef { .. }
			| MakeAggregate { .. }
			| Cast { .. }
			| BinaryOp { .. }
			| UnaryOp { .. }
			| GetElementPtr { .. }
			| Call { .. }
			| BlockRef { .. }
			| ArgRef { .. }
			| Allocate { .. }
			| Load { .. }
			| Store { .. }
			| Branch { .. }
			| ConditionalBranch { .. }
			| Switch { .. }
			| ComputedBranch { .. }
			| Ret { .. }
			| Unreachable { .. }
			=> true,

			| Phi { .. }
			=> false,
		}
	}

	pub fn is_terminator (&self) -> bool {
		use InstrData::*;
		match self {
			| Null { .. }
			| Int { .. }
			| UInt { .. }
			| Real { .. }
			| String { .. }
			| GlobalRef { .. }
			| FunctionRef { .. }
			| MakeAggregate { .. }
			| Cast { .. }
			| BinaryOp { .. }
			| UnaryOp { .. }
			| GetElementPtr { .. }
			| Call { .. }
			| BlockRef { .. }
			| ArgRef { .. }
			| Allocate { .. }
			| Load { .. }
			| Store { .. }
			| Phi { .. }
			=> false,

			| Branch { .. }
			| ConditionalBranch { .. }
			| Switch { .. }
			| ComputedBranch { .. }
			| Ret { .. }
			| Unreachable { .. }
			=> true,
		}
	}

	pub fn extract_const_int (&self) -> Option<i128> {
		use InstrData::*;
		match self {
			&Int(i) => Some(i),
			&UInt(u) => Some(u as i128),

			| Null { .. }
			| Real { .. }
			| String { .. }
			| BlockRef { .. }
			| GlobalRef { .. }
			| FunctionRef { .. }
			| ArgRef { .. }
			| MakeAggregate { .. }
			| Allocate { .. }
			| Load { .. }
			| Store { .. }
			| GetElementPtr { .. }
			| Cast { .. }
			| BinaryOp { .. }
			| UnaryOp { .. }
			| Call { .. }
			| Phi { .. }
			| Branch { .. }
			| ConditionalBranch { .. }
			| Switch { .. }
			| ComputedBranch { .. }
			| Ret { .. }
			| Unreachable { .. }
			=> None
		}
	}
}

#[derive(Debug)]
pub enum InstrMeta {
	// BuiltinA, BuiltinB, BuiltinC,
	User(String)
}

#[derive(Debug)]
pub struct Instr {
	pub data: InstrData,
	pub name: Option<String>,
	pub ty: Option<TyRef>,
	pub meta: Vec<InstrMetaRef>,
	pub src: Option<SrcAttribution>,
	pub block: Option<BlockRef>,
}



#[derive(Debug)]
pub struct Block {
	pub instrs: Vec<InstrRef>,
	pub in_edges: Vec<BlockRef>,
	pub out_edges: Vec<BlockRef>,
	pub function: FunctionRef,
}



#[derive(Debug)]
pub enum GlobalMeta {
	// BuiltinA, BuiltinB, BuiltinC,
	User(String)
}

#[derive(Debug)]
pub struct Global {
	pub name: Option<String>,
	pub ty: TyRef,
	pub src: SrcAttribution,
}



#[derive(Debug)]
pub enum ArgMeta {
	// BuiltinA, BuiltinB, BuiltinC,
	User(String)
}

#[derive(Debug)]
pub struct Arg {
	pub name: Option<String>,
	pub ty: TyRef,
	pub meta: Vec<ArgMetaRef>,
	pub src: SrcAttribution,
}

#[derive(Debug)]
pub enum FunctionMeta {
	// BuiltinA, BuiltinB, BuiltinC,
	User(String)
}

#[derive(Debug)]
pub struct Function {
	pub args: Vec<ArgRef>,
	pub blocks: Vec<BlockRef>,
	pub ty: TyRef,
	pub meta: Vec<FunctionMetaRef>,
	pub src: SrcAttribution,
}

#[derive(Debug)]
pub enum LayoutErr {
	TyErr(TyErr, TyRef),
	InvalidTyRef(TyRef),
}


pub trait Target: fmt::Debug {
	fn word_size (&self) -> u64;
	fn get_primitive_layout (&self, prim: PrimitiveTy) -> Layout;
}

#[derive(Debug)]
pub struct X64Linux;

impl Target for X64Linux {
	fn word_size (&self) -> u64 { 8 }

	fn get_primitive_layout (&self, prim: PrimitiveTy) -> Layout {
		use PrimitiveTy::*;
		match prim {
			Bool | SInt8 | UInt8 => Layout::scalar(1),
			SInt16 | UInt16 => Layout::scalar(2),
			SInt32 | UInt32 | Real32 => Layout::scalar(4),
			SInt64 | UInt64 | Real64 => Layout::scalar(8),
			SInt128 | UInt128 => Layout::scalar(16),
		}
	}
}

impl Default for Box<dyn Target> {
	fn default () -> Self { Box::new(X64Linux) }
}


#[derive(Debug, Default)]
pub struct Context {
	pub target: Box<dyn Target>,

	pub tys: Slotmap<TyRef, Ty>,
	pub instrs: Slotmap<InstrRef, Instr>,
	pub blocks: Slotmap<BlockRef, Block>,
	pub globals: Slotmap<GlobalRef, Global>,
	pub args: Slotmap<ArgRef, Arg>,
	pub functions: Slotmap<FunctionRef, Function>,

	pub ty_metas: Slotmap<TyMetaRef, TyMeta>,
	pub instr_metas: Slotmap<InstrMetaRef, InstrMeta>,
	pub arg_metas: Slotmap<ArgMetaRef, ArgMeta>,
	pub global_metas: Slotmap<GlobalMetaRef, GlobalMeta>,
	pub function_metas: Slotmap<FunctionMetaRef, FunctionMeta>,

	pub srcs: Slotmap<SrcRef, Src>,
}


pub struct TyInsertErr;

impl Context {
	pub fn new (target: Box<dyn Target>) -> Self {
		Self {
			target,
			.. Context::default()
		}
	}

	pub fn add_type (&mut self, ty: Ty) -> TyRef {
		for (key, existing_ty) in self.tys.iter_mut() {
			if  existing_ty.data == ty.data
			&& (existing_ty.name.is_none() || existing_ty.name == ty.name)
			&& (existing_ty.meta.is_empty() || existing_ty.meta == ty.meta)
			&& (existing_ty.src.is_none() || existing_ty.src == ty.src)
			&&  existing_ty.layout.is_none()
			{
				*existing_ty = ty;
				return *key
			}
		}

		self.tys.insert(ty)
	}


	pub fn finalize_ty (&mut self, ty_ref: TyRef) -> Result<&Layout, LayoutErr> {
		use TyData::*;

		let ty = self.tys.get(ty_ref).ok_or(LayoutErr::InvalidTyRef(ty_ref))?;

		if ty.layout.is_none() {
			let layout = match &ty.data {
				Void => Layout::custom_scalar(0, 1),

				Block => return Err(LayoutErr::TyErr(TyErr::BlockRefNotAllowed, ty_ref)),

				&Primitive(prim) => self.target.get_primitive_layout(prim),

				&Pointer { .. } | &Function { .. } => Layout::scalar(self.target.word_size()),

				&Array { length, element_ty } => {
					let &Layout { size: elem_size, align: elem_align, .. } = self.finalize_ty(element_ty)?;
					Layout::custom_scalar(length * elem_size, elem_align)
				},

				Structure { field_tys } => {
					let field_tys = field_tys.clone().into_iter();
					let mut size = 0;
					let mut align = 0;

					let mut field_offsets = vec![];

					for field_ty_ref in field_tys {
						let &Layout { size: field_size, align: field_align, .. } = self.finalize_ty(field_ty_ref)?;

						if field_align > align { align = field_align }

						let padding = (field_align - (size % field_align)) % field_align;

						size += padding;

						field_offsets.push(size);

						size += field_size;
					}

					size = if align < 2 { size } else { ((size + align - 1) / align) * align };

					Layout::structure(size, align, field_offsets)
				}
			};

			self.tys.get_mut(ty_ref).unwrap().layout.replace(layout);
		}

		Ok(self.tys.get(ty_ref).unwrap().layout.as_ref().unwrap())
	}

	pub fn size_of (&mut self, ty_ref: TyRef) -> Result<u64, LayoutErr> {
		Ok(self.finalize_ty(ty_ref)?.size)
	}

	pub fn align_of (&mut self, ty_ref: TyRef) -> Result<u64, LayoutErr> {
		Ok(self.finalize_ty(ty_ref)?.align)
	}

	pub fn field_offsets_of (&mut self, ty_ref: TyRef) -> Result<&Vec<u64>, LayoutErr> {
		if self.tys.get(ty_ref).ok_or(LayoutErr::InvalidTyRef(ty_ref))?.data.is_structure() {
			Ok(&self.finalize_ty(ty_ref)?.field_offsets)
		} else {
			Err(LayoutErr::TyErr(TyErr::ExpectedStructure, ty_ref))
		}
	}
}


#[derive(Debug)]
pub enum TyErr {
	ExpectedBlock,
	ExpectedBool,
	ExpectedInt,
	ExpectedSInt,
	ExpectedUInt,
	ExpectedReal,
	ExpectedArray,
	ExpectedPointer,
	ExpectedFunction,
	ExpectedStructure,
	ExpectedAggregate,
	ExpectedScalar,
	BlockRefNotAllowed,
	ExpectedTy(TyRef),
}

#[derive(Debug)]
pub enum CastErr {
	BitcastUnequalSizes,
	IntToRealInvalidCastee,
	IntToRealInvalidDestination,
	RealToIntInvalidCastee,
	RealToIntInvalidDestination,
	ExpectedNumericCastee,
	ExpectedNumericDestination,
	TruncateToLargerType,
	ExpectedIntegerCastee,
	ExpectedIntegerDestination,
	ExtendToSmallerType,
	InvalidTypeRepresentationChange,
}

#[derive(Debug)]
pub enum IrErr {
	NoActiveSrc,
	NoActiveBlock,
	NoActiveFunction,
	NoGepIndices,
	NonConstStructGepIndex(u64),
	ImplicitLoadInGep(u64),
	InvalidBlockRef(BlockRef),
	InvalidFunctionRef(FunctionRef),
	InvalidGlobalRef(GlobalRef),
	InvalidTyRef(TyRef),
	InvalidInstrRef(InstrRef),
	InvalidSrcRef(SrcRef),
	InvalidArgRef(ArgRef),
	InvalidBinaryOperand(BinaryOp, TyRef),
	InvalidUnaryOperand(UnaryOp, TyRef),
	ExpectedPhi(InstrRef),
	MissingParentBlock(InstrRef),
	PhiNodeEdgeNotPredecessor(InstrRef, BlockRef),
	PhiNodeDuplicateEdge(InstrRef, BlockRef),
	ArgRefNotFromActiveFunction(ArgRef, FunctionRef),
	WrongNumberOfCallArguments(u64, u64),
	MissingTerminator(BlockRef),
	EmptyBlock(BlockRef),
	EmptyFunction(FunctionRef),
	UnreachableBlock(BlockRef),
	ExpectedValue(InstrRef),
	UnexpectedValue(InstrRef),
	MissingReturnValue(TyRef),
	OutOfBounds(InstrRef, i128, u64),
	CannotHavePredecessor(InstrRef),
	CannotAddAfterTerminator(InstrRef, InstrRef),
	CannotInsertTerminatorMidstream(InstrRef),
	LayoutErr(LayoutErr),
	TyErr(TyErr, TyRef),
	CastErr(CastErr, TyRef, TyRef),
}

impl From<LayoutErr> for IrErr {
	fn from (le: LayoutErr) -> IrErr { Self::LayoutErr(le) }
}


pub type IrResult<T = ()> = Result<T, IrErr>;

// #[derive(Debug)]
// pub enum InsertionCursor {
// 	First,
// 	Last,
// 	Index(usize)
// }

#[derive(Debug)]
pub struct Builder<'c> {
	pub ctx: &'c mut Context,
	pub active_src: Option<SrcRef>,
	pub active_function: Option<FunctionRef>,
	pub active_block: Option<BlockRef>,
	pub insertion_cursor: Option<usize>,
}

impl<'c> Builder<'c> {
	pub fn new (ctx: &'c mut Context) -> Self {
		Self {
			ctx,
			active_src: None,
			active_function: None,
			active_block: None,
			insertion_cursor: None
		}
	}


	pub fn get_function (&self, f: FunctionRef) -> IrResult<&Function> {
		self.ctx.functions.get(f).ok_or(IrErr::InvalidFunctionRef(f))
	}

	fn get_function_mut (&mut self, f: FunctionRef) -> IrResult<&mut Function> {
		self.ctx.functions.get_mut(f).ok_or(IrErr::InvalidFunctionRef(f))
	}

	pub fn get_global (&self, g: GlobalRef) -> IrResult<&Global> {
		self.ctx.globals.get(g).ok_or(IrErr::InvalidGlobalRef(g))
	}

	// fn get_global_mut (&mut self, g: GlobalRef) -> IrResult<&mut Global> {
	// 	self.ctx.globals.get_mut(g).ok_or(IrErr::InvalidGlobalRef(g))
	// }

	pub fn get_block (&self, b: BlockRef) -> IrResult<&Block> {
		self.ctx.blocks.get(b).ok_or(IrErr::InvalidBlockRef(b))
	}

	fn get_block_mut (&mut self, b: BlockRef) -> IrResult<&mut Block> {
		self.ctx.blocks.get_mut(b).ok_or(IrErr::InvalidBlockRef(b))
	}

	pub fn get_instr (&self, i: InstrRef) -> IrResult<&Instr> {
		self.ctx.instrs.get(i).ok_or(IrErr::InvalidInstrRef(i))
	}

	fn get_instr_mut (&mut self, i: InstrRef) -> IrResult<&mut Instr> {
		self.ctx.instrs.get_mut(i).ok_or(IrErr::InvalidInstrRef(i))
	}

	pub fn get_ty (&self, t: TyRef) -> IrResult<&Ty> {
		self.ctx.tys.get(t).ok_or(IrErr::InvalidTyRef(t))
	}

	// fn get_ty_mut (&mut self, t: TyRef) -> IrResult<&mut Ty> {
	// 	self.ctx.tys.get_mut(t).ok_or(IrErr::InvalidTyRef(t))
	// }

	pub fn get_src (&self, s: SrcRef) -> IrResult<&Src> {
		self.ctx.srcs.get(s).ok_or(IrErr::InvalidSrcRef(s))
	}

	fn get_src_mut (&mut self, s: SrcRef) -> IrResult<&mut Src> {
		self.ctx.srcs.get_mut(s).ok_or(IrErr::InvalidSrcRef(s))
	}

	pub fn get_arg (&self, a: ArgRef) -> IrResult<&Arg> {
		self.ctx.args.get(a).ok_or(IrErr::InvalidArgRef(a))
	}

	// fn get_arg_mut (&mut self, a: ArgRef) -> IrResult<&mut Arg> {
	// 	self.ctx.args.get_mut(a).ok_or(IrErr::InvalidArgRef(a))
	// }


	pub fn get_active_src_ref (&self) -> IrResult<SrcRef> {
		self.active_src.ok_or(IrErr::NoActiveSrc)
	}

	pub fn get_active_block_ref (&self) -> IrResult<BlockRef> {
		self.active_block.ok_or(IrErr::NoActiveBlock)
	}

	pub fn get_active_function_ref (&self) -> IrResult<FunctionRef> {
		self.active_function.ok_or(IrErr::NoActiveFunction)
	}


	pub fn get_active_src (&self) -> IrResult<&Src> {
		self.get_src(self.get_active_src_ref()?)
	}

	pub fn get_active_block (&self) -> IrResult<&Block> {
		self.get_block(self.get_active_block_ref()?)
	}

	pub fn get_active_function (&self) -> IrResult<&Function> {
		self.get_function(self.get_active_function_ref()?)
	}



	pub fn get_active_src_mut (&mut self) -> IrResult<&mut Src> {
		self.get_src_mut(self.get_active_src_ref()?)
	}

	pub fn get_active_block_mut (&mut self) -> IrResult<&mut Block> {
		self.get_block_mut(self.get_active_block_ref()?)
	}

	pub fn get_active_function_mut (&mut self) -> IrResult<&mut Function> {
		self.get_function_mut(self.get_active_function_ref()?)
	}


	pub fn void_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Void.into()) }

	pub fn bool_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::Bool).into()) }

	pub fn sint8_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::SInt8).into()) }
	pub fn sint16_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::SInt16).into()) }
	pub fn sint32_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::SInt32).into()) }
	pub fn sint64_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::SInt64).into()) }
	pub fn sint128_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::SInt128).into()) }

	pub fn uint8_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::UInt8).into()) }
	pub fn uint16_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::UInt16).into()) }
	pub fn uint32_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::UInt32).into()) }
	pub fn uint64_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::UInt64).into()) }
	pub fn uint128_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::UInt128).into()) }

	pub fn real32_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::Real32).into()) }
	pub fn real64_ty (&mut self) -> TyRef { self.ctx.add_type(TyData::Primitive(PrimitiveTy::Real64).into()) }

	pub fn pointer_ty (&mut self, target_ty: TyRef) -> IrResult<TyRef> {
		self.get_ty(target_ty)?;
		Ok(self.ctx.add_type(TyData::Pointer { target_ty }.into()))
	}

	pub fn array_ty (&mut self, length: u64, element_ty: TyRef) -> IrResult<TyRef> {
		self.get_ty(element_ty)?;
		Ok(self.ctx.add_type(TyData::Array { length, element_ty }.into()))
	}

	pub fn structure_ty (&mut self, field_tys: Vec<TyRef>) -> IrResult<TyRef> {
		for &field_ty in field_tys.iter() {
			self.get_ty(field_ty)?;
		}

		Ok(self.ctx.add_type(TyData::Structure { field_tys }.into()))
	}

	pub fn function_ty (&mut self, parameter_tys: Vec<TyRef>, result_ty: Option<TyRef>) -> IrResult<TyRef> {
		for &parameter_ty in parameter_tys.iter() {
			self.get_ty(parameter_ty)?;
		}

		if let Some(result_ty) = result_ty {
			self.get_ty(result_ty)?;
		}

		Ok(self.ctx.add_type(TyData::Function { parameter_tys, result_ty }.into()))
	}

	pub fn string_ty (&mut self) -> TyRef {
		let char_ty = self.sint8_ty();
		self.pointer_ty(char_ty).unwrap()
	}

	pub fn block_ty (&mut self) -> TyRef {
		self.ctx.add_type(TyData::Block.into())
	}


	pub fn size_of (&mut self, ty_ref: TyRef) -> IrResult<u64> {
		Ok(self.ctx.size_of(ty_ref)?)
	}

	pub fn align_of (&mut self, ty_ref: TyRef) -> IrResult<u64> {
		Ok(self.ctx.align_of(ty_ref)?)
	}

	pub fn field_offsets_of (&mut self, ty_ref: TyRef) -> IrResult<&Vec<u64>> {
		Ok(self.ctx.field_offsets_of(ty_ref)?)
	}



	pub fn get_instr_ty_ref (&self, i: InstrRef) -> IrResult<TyRef> {
		self.ctx.instrs.get(i).ok_or(IrErr::InvalidInstrRef(i))?.ty.ok_or(IrErr::ExpectedValue(i))
	}

	pub fn get_validated_instr_ty_ref (&self, i: InstrRef) -> IrResult<TyRef> {
		let ty = self.get_instr_ty_ref(i)?;
		self.get_ty(ty)?;
		Ok(ty)
	}

	pub fn get_instr_ty (&self, i: InstrRef) -> IrResult<&Ty> {
		self.get_ty(self.get_instr_ty_ref(i)?)
	}

	pub fn get_instr_block_ref (&self, i: InstrRef) -> IrResult<BlockRef> {
		self.ctx.instrs.get(i).ok_or(IrErr::InvalidInstrRef(i))?.block.ok_or(IrErr::ExpectedValue(i))
	}

	pub fn get_validated_instr_block_ref (&self, i: InstrRef) -> IrResult<BlockRef> {
		let block = self.get_instr_block_ref(i)?;
		self.get_block(block)?;
		Ok(block)
	}

	pub fn get_instr_block (&self, i: InstrRef) -> IrResult<&Block> {
		self.get_block(self.get_instr_block_ref(i)?)
	}

	pub fn get_block_function_ref (&self, block: BlockRef) -> IrResult<FunctionRef> {
		Ok(self.get_block(block)?.function)
	}

	pub fn get_validated_block_function_ref (&self, block: BlockRef) -> IrResult<FunctionRef> {
		let func = self.get_block(block)?.function;
		self.get_function(func)?;
		Ok(func)
	}

	pub fn get_block_function (&self, block: BlockRef) -> IrResult<&Function> {
		self.get_function(self.get_block(block)?.function)
	}



	fn finalize_active_block (&mut self) -> IrResult {
		if let Some(active_block_ref) = self.active_block {
			let active_block = self.get_block(active_block_ref)?;

			if let Some(&last_instr) = active_block.instrs.last() {
				let last_instr = self.get_instr(last_instr)?;

				if !last_instr.data.is_terminator() {
					return Err(IrErr::MissingTerminator(active_block_ref))
				}
			} else {
				return Err(IrErr::EmptyBlock(active_block_ref))
			}
		}

		Ok(())
	}

	fn finalize_active_function (&mut self) -> IrResult {
		if let Some(active_function_ref) = self.active_function {
			let active_function = self.get_function(active_function_ref)?;

			for &block_ref in active_function.blocks.iter() {
				if self.get_block_in_edges(block_ref)?.is_empty() {
					return Err(IrErr::UnreachableBlock(block_ref))
				}

				let last_instr = self.get_instr(self.get_last_instr(block_ref)?)?;

				if !last_instr.data.is_terminator() {
					return Err(IrErr::MissingTerminator(block_ref))
				}
			}
		}

		Ok(())
	}


	pub fn set_active_block (&mut self, block: BlockRef) -> IrResult {
		self.get_block(block)?;

		self.finalize_active_block()?;

		self.active_block.replace(block);

		self.insertion_cursor.take();

		Ok(())
	}

	pub fn clear_active_block (&mut self) -> IrResult {
		self.finalize_active_block()?;
		self.insertion_cursor.take();
		Ok(())
	}



	pub fn set_active_function (&mut self, function: FunctionRef) -> IrResult {
		self.get_function(function)?;

		self.clear_active_block()?;

		self.finalize_active_function()?;

		self.active_function.replace(function);

		Ok(())
	}


	pub fn clear_active_function (&mut self) -> IrResult {
		self.clear_active_block()?;

		self.finalize_active_function()?;

		self.active_function.take();

		Ok(())
	}


	pub fn get_block_instrs (&self, block: BlockRef) -> IrResult<&[InstrRef]> {
		Ok(&self.get_block(block)?.instrs)
	}

	pub fn get_block_in_edges (&self, block: BlockRef) -> IrResult<&[BlockRef]> {
		Ok(&self.get_block(block)?.in_edges)
	}

	pub fn get_block_out_edges (&self, block: BlockRef) -> IrResult<&[BlockRef]> {
		Ok(&self.get_block(block)?.out_edges)
	}

	pub fn get_instr_index (&self, i: InstrRef) -> IrResult<usize> {
		self.get_active_block()?
			.instrs
			.iter()
			.enumerate()
			.find(|&(_, &bi)| i == bi)
			.map(|(idx, _)| idx)
			.ok_or(IrErr::InvalidInstrRef(i))
	}

	pub fn get_first_instr (&self, block: BlockRef) -> IrResult<InstrRef> {
		let instrs = self.get_block_instrs(block)?;

		instrs.first().copied().ok_or(IrErr::EmptyBlock(block))
	}

	pub fn get_last_instr (&self, block: BlockRef) -> IrResult<InstrRef> {
		let instrs = self.get_block_instrs(block)?;

		instrs.last().copied().ok_or(IrErr::EmptyBlock(block))
	}

	pub fn set_cursor_before (&mut self, i: InstrRef) -> IrResult {
		let idx = self.get_instr_index(i)?;

		self.insertion_cursor.replace(idx);

		Ok(())
	}

	pub fn set_cursor_after (&mut self, i: InstrRef) -> IrResult {
		let idx = self.get_instr_index(i)?;

		self.insertion_cursor.replace(idx + 1);

		Ok(())
	}

	pub fn cursor_to_start (&mut self) -> IrResult {
		self.get_active_block()?;

		self.insertion_cursor.replace(0);

		Ok(())
	}

	pub fn cursor_to_end (&mut self) -> IrResult {
		self.get_active_block()?;

		self.insertion_cursor.take();

		Ok(())
	}

	pub fn get_function_blocks (&self, func: FunctionRef) -> IrResult<&[BlockRef]> {
		Ok(&self.get_function(func)?.blocks)
	}

	pub fn get_block_index (&self, block: BlockRef) -> IrResult<usize> {
		self.get_active_function()?
			.blocks
			.iter()
			.enumerate()
			.find(|&(_, &fblock)| block == fblock)
			.map(|(idx, _)| idx)
			.ok_or(IrErr::InvalidBlockRef(block))
	}

	pub fn get_first_block (&self, function: FunctionRef) -> IrResult<BlockRef> {
		let blocks = self.get_function_blocks(function)?;

		blocks.first().copied().ok_or(IrErr::EmptyFunction(function))
	}

	pub fn get_last_block (&self, function: FunctionRef) -> IrResult<BlockRef> {
		let blocks = self.get_function_blocks(function)?;

		blocks.last().copied().ok_or(IrErr::EmptyFunction(function))
	}

	pub fn move_block_to_end (&mut self, block: BlockRef) -> IrResult {
		let index = self.get_block_index(block)?;
		let func = self.get_active_function_mut()?;

		func.blocks.remove(index);
		func.blocks.push(block);

		Ok(())
	}

	pub fn move_block_to_start (&mut self, block: BlockRef) -> IrResult {
		let index = self.get_block_index(block)?;
		let func = self.get_active_function_mut()?;

		func.blocks.remove(index);
		func.blocks.insert(0, block);

		Ok(())
	}

	pub fn move_block_before (&mut self, block_to_move: BlockRef, destination: BlockRef) -> IrResult {
		let index_to_move = self.get_block_index(block_to_move)?;
		let index_destination = self.get_block_index(destination)?;
		let func = self.get_active_function_mut()?;

		func.blocks.remove(index_to_move);
		func.blocks.insert(index_destination, block_to_move);

		Ok(())
	}

	pub fn move_block_after (&mut self, block_to_move: BlockRef, destination: BlockRef) -> IrResult {
		let index_to_move = self.get_block_index(block_to_move)?;
		let index_destination = self.get_block_index(destination)?;
		let func = self.get_active_function_mut()?;

		func.blocks.remove(index_to_move);
		func.blocks.insert(index_destination + 1, block_to_move);

		Ok(())
	}


	pub fn get_pointer_element_ty (&self, p: TyRef) -> IrResult<TyRef> {
		match &self.get_ty(p)?.data {
			TyData::Pointer { target_ty } => Ok(*target_ty),
			_ => Err(IrErr::TyErr(TyErr::ExpectedPointer, p))
		}
	}

	pub fn get_function_ty_data (&self, f: TyRef) -> IrResult<(&[TyRef], Option<TyRef>)> {
		if let TyData::Function { parameter_tys, result_ty } = &self.get_ty(f)?.data {
			Ok((parameter_tys, *result_ty))
		} else {
			Err(IrErr::TyErr(TyErr::ExpectedFunction, f))
		}
	}

	pub fn get_phi_edges (&self, phi: InstrRef) -> IrResult<&[(BlockRef, InstrRef)]> {
		if let InstrData::Phi { edges } = &self.get_instr(phi)?.data {
			Ok(edges)
		} else {
			Err(IrErr::ExpectedPhi(phi))
		}
	}

	fn get_phi_edges_mut (&mut self, phi: InstrRef) -> IrResult<&mut Vec<(BlockRef, InstrRef)>> {
		if let InstrData::Phi { edges } = &mut self.get_instr_mut(phi)?.data {
			Ok(edges)
		} else {
			Err(IrErr::ExpectedPhi(phi))
		}
	}


	fn add_instr (&mut self, data: InstrData, ty: Option<TyRef>) -> IrResult<InstrRef> {
		Ok(if let Some(active_block_ref) = self.active_block {
			let active_block = self.get_block(active_block_ref)?;
			let block_len = active_block.instrs.len();

			let data_can_have_predecessor = data.can_have_predecessor();
			let data_is_terminator = data.is_terminator();

			let i = self.ctx.instrs.insert(Instr {
				data,
				ty,
				name: None,
				meta: vec![],
				src: None,
				block: self.active_block
			});

			let cursor = *self.insertion_cursor.get_or_insert(block_len);
			let active_block = self.get_block(active_block_ref)?;

			if data_is_terminator && cursor != block_len {
				return Err(IrErr::CannotInsertTerminatorMidstream(i))
			}

			let last_instr_ref = if cursor == block_len { active_block.instrs.last() } else { active_block.instrs.get(cursor) };

			if let Some(&last_instr_ref) = last_instr_ref {
				if !data_can_have_predecessor {
					return Err(IrErr::CannotHavePredecessor(i))
				}

				let last_instr = self.get_instr(last_instr_ref)?;

				if last_instr.data.is_terminator() {
					return Err(IrErr::CannotAddAfterTerminator(i, last_instr_ref))
				}
			}

			self.get_block_mut(active_block_ref)?.instrs.insert(cursor, i);

			self.insertion_cursor.replace(cursor + 1);

			i
		} else {
			return Err(IrErr::NoActiveBlock)
		})
	}


	pub fn remove_instr (&mut self, i: InstrRef) -> IrResult {
		// This cant be done in the current safety model lol
		// Currently we validate instructions as they are added, and so this would break all safety invariants
		// The same is true for remove_block

		// Technically it can be done, if we introduce a secondary validation pass
		// However, this makes most of the checking done in the current system rather redundant
		todo!("{:?}", i)
	}

	pub fn imm_null (&mut self, ty_ref: TyRef) -> IrResult<InstrRef> {
		self.get_ty(ty_ref)?;

		self.add_instr(InstrData::Null, Some(ty_ref))
	}

	pub fn imm_sint (&mut self, v: i128, ty_ref: TyRef) -> IrResult<InstrRef> {
		if self.get_ty(ty_ref)?.data.is_sint() {
			self.add_instr(InstrData::Int(v), Some(ty_ref))
		} else {
			Err(IrErr::TyErr(TyErr::ExpectedSInt, ty_ref))
		}
	}

	pub fn imm_sint8 (&mut self, v: i8) -> InstrRef {
		let ty = self.sint8_ty();
		self.imm_sint(v as i128, ty).unwrap()
	}

	pub fn imm_sint16 (&mut self, v: i16) -> InstrRef {
		let ty = self.sint16_ty();
		self.imm_sint(v as i128, ty).unwrap()
	}

	pub fn imm_sint32 (&mut self, v: i32) -> InstrRef {
		let ty = self.sint32_ty();
		self.imm_sint(v as i128, ty).unwrap()
	}

	pub fn imm_sint64 (&mut self, v: i64) -> InstrRef {
		let ty = self.sint64_ty();
		self.imm_sint(v as i128, ty).unwrap()
	}

	pub fn imm_sint128 (&mut self, v: i128) -> InstrRef {
		let ty = self.sint128_ty();
		self.imm_sint(v as i128, ty).unwrap()
	}

	pub fn imm_uint (&mut self, v: u128, ty_ref: TyRef) -> IrResult<InstrRef> {
		if self.get_ty(ty_ref)?.data.is_uint() {
			self.add_instr(InstrData::UInt(v), Some(ty_ref))
		} else {
			Err(IrErr::TyErr(TyErr::ExpectedUInt, ty_ref))
		}
	}

	pub fn imm_uint8 (&mut self, v: u8) -> InstrRef {
		let ty = self.uint8_ty();
		self.imm_uint(v as u128, ty).unwrap()
	}

	pub fn imm_uint16 (&mut self, v: u16) -> InstrRef {
		let ty = self.uint16_ty();
		self.imm_uint(v as u128, ty).unwrap()
	}

	pub fn imm_uint32 (&mut self, v: u32) -> InstrRef {
		let ty = self.uint32_ty();
		self.imm_uint(v as u128, ty).unwrap()
	}

	pub fn imm_uint64 (&mut self, v: u64) -> InstrRef {
		let ty = self.uint64_ty();
		self.imm_uint(v as u128, ty).unwrap()
	}

	pub fn imm_uint128 (&mut self, v: u128) -> InstrRef {
		let ty = self.uint128_ty();
		self.imm_uint(v as u128, ty).unwrap()
	}

	pub fn imm_real (&mut self, v: f64, ty_ref: TyRef) -> IrResult<InstrRef> {
		if self.get_ty(ty_ref)?.data.is_real() {
			self.add_instr(InstrData::Real(v), Some(ty_ref))
		} else {
			Err(IrErr::TyErr(TyErr::ExpectedReal, ty_ref))
		}
	}

	pub fn imm_real32 (&mut self, v: f32) -> InstrRef {
		let ty = self.real32_ty();
		self.imm_real(v as f64, ty).unwrap()
	}

	pub fn imm_real64 (&mut self, v: f64) -> InstrRef {
		let ty = self.real64_ty();
		self.imm_real(v as f64, ty).unwrap()
	}

	pub fn imm_string (&mut self, v: String) -> InstrRef {
		let ty = self.string_ty();
		self.add_instr(InstrData::String(v), Some(ty)).unwrap()
	}

	pub fn imm_block_ref (&mut self, v: BlockRef) -> IrResult<InstrRef> {
		self.get_block(v)?;
		let ty = self.block_ty();
		self.add_instr(InstrData::BlockRef(v), Some(ty))
	}

	pub fn imm_global_ref (&mut self, v: GlobalRef) -> IrResult<InstrRef> {
		let ty = self.get_global(v)?.ty;
		self.get_ty(ty)?;
		self.add_instr(InstrData::GlobalRef(v), Some(ty))
	}

	pub fn imm_function_ref (&mut self, v: FunctionRef) -> IrResult<InstrRef> {
		let ty = self.get_function(v)?.ty;
		self.get_ty(ty)?;
		self.add_instr(InstrData::FunctionRef(v), Some(ty))
	}

	pub fn imm_arg_ref (&mut self, v: ArgRef) -> IrResult<InstrRef> {
		let active_function = self.get_active_function()?;
		if !active_function.args.contains(&v) { return Err(IrErr::ArgRefNotFromActiveFunction(v, self.active_function.unwrap())) }

		let ty = self.get_arg(v)?.ty;
		self.get_ty(ty)?;

		self.add_instr(InstrData::ArgRef(v), Some(ty))
	}


	pub fn ty_ck_aggregate_elem (&self, ty: &Ty, element_idx: u64, element_ref: InstrRef) -> IrResult {
		let element_ty = self.get_instr_ty_ref(element_ref)?;
		self.get_ty(element_ty)?;

		match &ty.data {
			&TyData::Array { length, element_ty: expected_ty }
			=> if element_idx >= length {
				Err(IrErr::OutOfBounds(element_ref, element_idx as i128, length))
			} else if element_ty != expected_ty {
				Err(IrErr::TyErr(TyErr::ExpectedTy(expected_ty), element_ty))
			} else {
				Ok(())
			},

			TyData::Structure { field_tys }
			=> if let Some(&expected_ty) = field_tys.get(element_idx as usize) {
				if element_ty == expected_ty {
					Ok(())
				} else {
					Err(IrErr::TyErr(TyErr::ExpectedTy(expected_ty), element_ty))
				}
			} else {
				Err(IrErr::OutOfBounds(element_ref, element_idx as i128, field_tys.len() as u64))
			}

			| TyData::Void { .. }
			| TyData::Block { .. }
			| TyData::Primitive { .. }
			| TyData::Pointer { .. }
			| TyData::Function { .. }
			=> Ok(())
		}
	}

	pub fn make_aggregate (&mut self, elements: Vec<InstrRef>, ty_ref: TyRef) -> IrResult<InstrRef> {
		let ty = self.get_ty(ty_ref)?;

		if !ty.data.is_aggregate() { return Err(IrErr::TyErr(TyErr::ExpectedAggregate, ty_ref)) }

		for (i, &element_instr) in elements.iter().enumerate() {
			self.ty_ck_aggregate_elem(ty, i as u64, element_instr)?;
		}

		self.add_instr(InstrData::MakeAggregate { elements }, Some(ty_ref))
	}

	pub fn allocate (&mut self, length: u64, ty: TyRef) -> IrResult<InstrRef> {
		let ty = self.pointer_ty(ty)?;
		self.add_instr(InstrData::Allocate { length }, Some(ty))
	}

	pub fn load (&mut self, source: InstrRef) -> IrResult<InstrRef> {
		let pty_ref = self.get_instr_ty_ref(source)?;
		let ty = self.get_pointer_element_ty(pty_ref)?;

		self.add_instr(InstrData::Load { source }, Some(ty))
	}

	pub fn store (&mut self, destination: InstrRef, value: InstrRef) -> IrResult<InstrRef> {
		let pty_ref = self.get_instr_ty_ref(destination)?;
		let target_ty = self.get_pointer_element_ty(pty_ref)?;

		let value_ty = self.get_validated_instr_ty_ref(value)?;

		if target_ty != value_ty { return Err(IrErr::TyErr(TyErr::ExpectedTy(target_ty), value_ty)) }

		self.add_instr(InstrData::Store { destination, value }, None)
	}

	pub fn get_element_ptr (&mut self, ptr: InstrRef, indices: Vec<InstrRef>) -> IrResult<InstrRef> {
		if indices.is_empty() { return Err(IrErr::NoGepIndices) }

		let pty_ref = self.get_instr_ty_ref(ptr)?;
		let mut target_ty_ref = self.get_pointer_element_ty(pty_ref)?;

		if indices.len() > 1 {
			for (i, &index_ref) in indices.iter().enumerate().skip(1) {
				let index_instr = self.get_instr(index_ref)?;
				let index = index_instr.data.extract_const_int();

				let target_ty = self.get_ty(target_ty_ref)?;

				match &target_ty.data {
					&TyData::Array { length, element_ty } => {
						if let Some(index) = index {
							if index > (length as i128) { return Err(IrErr::OutOfBounds(index_ref, index, length)) }
						}

						target_ty_ref = element_ty;
					}

					TyData::Structure { field_tys } => {
						let index = index.ok_or(IrErr::NonConstStructGepIndex(i as u64))?;

						if index >= (field_tys.len() as i128) { return Err(IrErr::OutOfBounds(index_ref, index, field_tys.len() as u64)) }

						target_ty_ref = *unsafe { field_tys.get_unchecked(index as usize) };
					}

					TyData::Pointer { .. }
					=> return Err(IrErr::ImplicitLoadInGep(i as u64)),

					| TyData::Void
					| TyData::Block
					| TyData::Primitive { .. }
					| TyData::Function { .. }
					=> return Err(IrErr::TyErr(TyErr::ExpectedAggregate, target_ty_ref))
				}
			}
		}

		self.add_instr(InstrData::GetElementPtr { ptr, indices }, Some(target_ty_ref))
	}

	pub fn cast (&mut self, kind: CastKind, castee: InstrRef, new_ty_ref: TyRef) -> IrResult<InstrRef> {
		let castee_ty_ref = self.get_instr_ty_ref(castee)?;

		let castee_size = self.size_of(castee_ty_ref)?;
		let new_size = self.size_of(new_ty_ref)?;

		let castee_ty = self.get_ty(castee_ty_ref)?;
		let new_ty = self.get_ty(new_ty_ref)?;

		if let Some(cast_err) = match kind {
			CastKind::Bitcast if castee_size != new_size => Some(CastErr::BitcastUnequalSizes),

			CastKind::IntToReal if !castee_ty.data.is_int() => Some(CastErr::IntToRealInvalidCastee),
			CastKind::IntToReal if !new_ty.data.is_real() => Some(CastErr::IntToRealInvalidDestination),

			CastKind::RealToInt if !castee_ty.data.is_real() => Some(CastErr::RealToIntInvalidCastee),
			CastKind::RealToInt if !new_ty.data.is_int() => Some(CastErr::RealToIntInvalidDestination),

			CastKind::Truncate if !(castee_ty.data.is_real() || castee_ty.data.is_int()) => Some(CastErr::ExpectedNumericCastee),
			CastKind::Truncate if !(new_ty.data.is_real() || new_ty.data.is_int()) => Some(CastErr::ExpectedNumericDestination),
			CastKind::Truncate if !((castee_ty.data.is_real() && new_ty.data.is_real()) || (castee_ty.data.is_int() && new_ty.data.is_int())) => Some(CastErr::InvalidTypeRepresentationChange),
			CastKind::Truncate if castee_size < new_size => Some(CastErr::TruncateToLargerType),

			CastKind::ZeroExtend if !castee_ty.data.is_int() => Some(CastErr::ExpectedIntegerCastee),
			CastKind::ZeroExtend if !new_ty.data.is_int() => Some(CastErr::ExpectedIntegerDestination),
			CastKind::ZeroExtend if castee_size > new_size => Some(CastErr::ExtendToSmallerType),
			CastKind::SignExtend if castee_size > new_size => Some(CastErr::ExtendToSmallerType),
			CastKind::SignExtend if !((castee_ty.data.is_real() && new_ty.data.is_real()) || (castee_ty.data.is_int() && new_ty.data.is_int())) => Some(CastErr::InvalidTypeRepresentationChange),

			_ => None
		} {
			return Err(IrErr::CastErr(cast_err, castee_ty_ref, new_ty_ref))
		}

		self.add_instr(InstrData::Cast { kind, castee }, Some(new_ty_ref))
	}

	pub fn bin_result_ty (&mut self, op: BinaryOp, ty_ref: TyRef) -> IrResult<TyRef> {
		use BinaryOp::*;

		let ty = self.get_ty(ty_ref)?;

		Ok(match op {
			Add | Sub | Mul | Div | Rem
			if ty.data.is_int()
			|| ty.data.is_real()
			=> ty_ref,

			LAnd | LOr | BAnd | BOr | BXor
			if ty.data.is_int()
			|| ty.data.is_bool()
			=> ty_ref,

			LSh | RShA | RShL
			if ty.data.is_int()
			=> ty_ref,

			Eq | Ne | Lt | Gt | Le | Ge
			if ty.data.is_bool()
			|| ty.data.is_int()
			|| ty.data.is_real()
			|| ty.data.is_pointer()
			=> self.bool_ty(),

			_ => return Err(IrErr::InvalidBinaryOperand(op, ty_ref))
		})
	}

	pub fn un_result_ty (&mut self, op: UnaryOp, ty_ref: TyRef) -> IrResult<TyRef> {
		use UnaryOp::*;

		let ty = self.get_ty(ty_ref)?;

		Ok(match op {
			Neg
			if ty.data.has_sign()
			=> ty_ref,

			LNot | BNot
			if ty.data.is_int()
			|| ty.data.is_bool()
			=> ty_ref,

			_ => return Err(IrErr::InvalidUnaryOperand(op, ty_ref))
		})
	}

	pub fn binary_op (&mut self, op: BinaryOp, a: InstrRef, b: InstrRef) -> IrResult<InstrRef> {
		let a_ty_ref = self.get_validated_instr_ty_ref(a)?;
		let b_ty_ref = self.get_validated_instr_ty_ref(b)?;

		if a_ty_ref != b_ty_ref { return Err(IrErr::TyErr(TyErr::ExpectedTy(a_ty_ref), b_ty_ref)) }

		let ty = self.bin_result_ty(op, a_ty_ref)?;

		self.add_instr(InstrData::BinaryOp { op, a, b }, Some(ty))
	}

	pub fn unary_op (&mut self, op: UnaryOp, operand: InstrRef) -> IrResult<InstrRef> {
		let operand_ty = self.get_instr_ty_ref(operand)?;

		let ty = self.un_result_ty(op, operand_ty)?;

		self.add_instr(InstrData::UnaryOp { op, operand }, Some(ty))
	}

	pub fn call (&mut self, callee: InstrRef, arguments: Vec<InstrRef>) -> IrResult<InstrRef> {
		let callee_ty = self.get_instr_ty_ref(callee)?;

		let (parameter_tys, result_ty) = self.get_function_ty_data(callee_ty)?;

		if parameter_tys.len() != arguments.len() { return Err(IrErr::WrongNumberOfCallArguments(parameter_tys.len() as u64, arguments.len() as u64)) }

		for (i, &parameter_ty_ref) in parameter_tys.iter().enumerate() {
			let argument_ty_ref = self.get_validated_instr_ty_ref(*unsafe { arguments.get_unchecked(i) })?;

			if parameter_ty_ref != argument_ty_ref { return Err(IrErr::TyErr(TyErr::ExpectedTy(parameter_ty_ref), argument_ty_ref)) }
		}

		self.add_instr(InstrData::Call { callee, arguments }, result_ty)
	}

	pub fn phi (&mut self, ty: TyRef) -> IrResult<InstrRef> {
		self.get_active_block()?;
		self.get_ty(ty)?;

		self.add_instr(InstrData::Phi { edges: vec![] }, Some(ty))
	}

	pub fn add_phi_edge (&mut self, phi: InstrRef, edge_block: BlockRef, edge_val: InstrRef) -> IrResult {
		let existing_edges = self.get_phi_edges(phi)?;

		let phi_block = self.get_instr_block(phi)?;
		let phi_node_ty = self.get_validated_instr_ty_ref(phi)?;

		let edge_ty = self.get_validated_instr_ty_ref(edge_val)?;

		if phi_node_ty != edge_ty { return Err(IrErr::TyErr(TyErr::ExpectedTy(phi_node_ty), edge_ty)) }
		if !phi_block.in_edges.contains(&edge_block) { return Err(IrErr::PhiNodeEdgeNotPredecessor(phi, edge_block)) }
		if existing_edges.iter().any(|(existing_block, _)| *existing_block == edge_block) { return Err(IrErr::PhiNodeDuplicateEdge(phi, edge_block))}

		self.get_phi_edges_mut(phi).unwrap().push((edge_block, edge_val));

		Ok(())
	}

	pub fn set_phi_edges (&mut self, phi: InstrRef, edges: Vec<(BlockRef, InstrRef)>) -> IrResult {
		self.get_phi_edges(phi)?;

		let phi_block = self.get_instr_block(phi)?;
		let phi_node_ty = self.get_validated_instr_ty_ref(phi)?;

		for &(edge_block, edge_val) in edges.iter() {
			let edge_ty = self.get_validated_instr_ty_ref(edge_val)?;

			if phi_node_ty != edge_ty { return Err(IrErr::TyErr(TyErr::ExpectedTy(phi_node_ty), edge_ty)) }
			if !phi_block.in_edges.contains(&edge_block) { return Err(IrErr::PhiNodeEdgeNotPredecessor(phi, edge_block)) }
		}

		self.ctx.instrs.get_mut(phi).unwrap().data = InstrData::Phi { edges };

		Ok(())
	}


	fn add_edge (edges: &mut Vec<BlockRef>, edge: BlockRef) {
		if !edges.contains(&edge) { edges.push(edge) }
	}

	fn link_block_edges (&mut self, from: BlockRef, to: BlockRef) -> IrResult {
		Self::add_edge(&mut self.get_block_mut(from)?.out_edges, to);
		Self::add_edge(&mut self.get_block_mut(to)?.in_edges, from);
		Ok(())
	}

	fn remove_edge (edges: &mut Vec<BlockRef>, edge: BlockRef) {
		let idx = {
			edges
				.iter()
				.enumerate()
				.find(|&(_, &e)| e == edge)
				.map(|(idx, _)| idx)
		};

		if let Some(idx) = idx {
			edges.remove(idx);
		}
	}

	fn unlink_block_edges (&mut self, from: BlockRef, to: BlockRef) -> IrResult {
		Self::remove_edge(&mut self.get_block_mut(from)?.out_edges, to);
		Self::remove_edge(&mut self.get_block_mut(to)?.in_edges, from);
		Ok(())
	}

	pub fn branch (&mut self, destination: BlockRef) -> IrResult<InstrRef> {
		let active_block = self.get_active_block_ref()?;

		self.link_block_edges(active_block, destination)?;

		self.add_instr(InstrData::Branch { destination }, None)
	}

	pub fn conditional_branch (&mut self, condition: InstrRef, then_destination: BlockRef, else_destination: BlockRef) -> IrResult<InstrRef> {
		let active_block = self.get_active_block_ref()?;

		let cond_ty = self.get_instr_ty_ref(condition)?;
		if !self.get_ty(cond_ty)?.data.is_bool() { return Err(IrErr::TyErr(TyErr::ExpectedBool, cond_ty)) }

		self.link_block_edges(active_block, then_destination)?;
		self.link_block_edges(active_block, else_destination)?;

		self.add_instr(InstrData::ConditionalBranch { condition, then_destination, else_destination }, None)
	}

	pub fn switch (&mut self, condition: InstrRef, branches: Vec<(InstrRef, BlockRef)>) -> IrResult<InstrRef> {
		let active_block = self.get_active_block_ref()?;

		let cond_ty_ref = self.get_instr_ty_ref(condition)?;
		let cond_ty = self.get_ty(cond_ty_ref)?;

		if !cond_ty.data.is_scalar() {
			return Err(IrErr::TyErr(TyErr::ExpectedScalar, cond_ty_ref))
		}

		for &(branch_val, branch_block) in branches.iter() {
			let branch_val_ty_ref = self.get_instr_ty_ref(branch_val)?;

			if cond_ty_ref != branch_val_ty_ref { return Err(IrErr::TyErr(TyErr::ExpectedTy(cond_ty_ref), branch_val_ty_ref)) }

			self.link_block_edges(active_block, branch_block)?;
		}

		self.add_instr(InstrData::Switch { condition, branches }, None)
	}

	pub fn computed_branch (&mut self, destination: InstrRef, branches: Vec<BlockRef>) -> IrResult<InstrRef> {
		let active_block = self.get_active_block_ref()?;

		let destination_ty_ref = self.get_instr_ty_ref(destination)?;
		if !self.get_ty(destination_ty_ref)?.data.is_block() { return Err(IrErr::TyErr(TyErr::ExpectedBlock, destination_ty_ref)) }

		for &branch_block in branches.iter() {
			self.link_block_edges(active_block, branch_block)?;
		}

		self.add_instr(InstrData::ComputedBranch { destination, branches }, None)
	}

	pub fn ret (&mut self, value: Option<InstrRef>) -> IrResult<InstrRef> {
		let active_fn_ty = self.get_function(self.get_active_function_ref()?)?.ty;

		let (_, result_ty) = self.get_function_ty_data(active_fn_ty)?;

		match (value, result_ty) {
			(Some(value), Some(result_ty)) => {
				let value_ty = self.get_validated_instr_ty_ref(value)?;
				if value_ty != result_ty { return Err(IrErr::TyErr(TyErr::ExpectedTy(result_ty), value_ty)) }
			}

			(Some(value), None) => {
				return Err(IrErr::UnexpectedValue(value))
			}

			(None, Some(result_ty)) => {
				return Err(IrErr::MissingReturnValue(result_ty))
			}

			(None, None) => { }
		}

		self.add_instr(InstrData::Ret { value }, None)
	}

	pub fn unreachable (&mut self) -> IrResult<InstrRef> {
		self.add_instr(InstrData::Unreachable, None)
	}
}