use std::{cell::Ref, collections::HashSet, ops::{self, Deref}};

use support::{slotmap::{AsKey, Keyed, KeyedMut}, utils::assert};

use crate::{cfg_generator, printer::Printable};

use super::{
	src::*,
	ty::*,
	ir::*,
	cfg::*,
	ty_checker
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FunctionErrLocation {
	Root,
	Block(BlockKey),
	Node(BlockKey, usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IrErrLocation {
	None,
	Ty(TyKey),
	Global(GlobalKey),
	Function(FunctionKey, FunctionErrLocation),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IrErrData {
	EmptyBlock(BlockKey),
	InvalidParamKey(ParamKey),
	InvalidParamIndex(usize),
	InvalidLocalKey(LocalKey),
	InvalidBlockKey(BlockKey),
	InvalidBlockIndex(usize),
	InvalidTyKey(TyKey),
	InvalidGlobalKey(GlobalKey),
	InvalidFunctionKey(FunctionKey),
	InvalidNodeIndex(usize),
	CfgErr(CfgErr),
	TyErr(TyErr),
}

impl From<CfgErr> for IrErrData {
	fn from (e: CfgErr) -> IrErrData { IrErrData::CfgErr(e) }
}

impl From<TyErr> for IrErrData {
	fn from (e: TyErr) -> IrErrData { IrErrData::TyErr(e) }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IrErr {
	pub data: IrErrData,
	pub location: IrErrLocation,
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FunctionErr {
	pub data: IrErrData,
	pub location: FunctionErrLocation,
}

// impl From<IrErrData> for IrErr {
// 	fn from (data: IrErrData) -> IrErr {
// 		IrErr {
// 			data,
// 			location: IrErrLocation::None
// 		}
// 	}
// }

// impl From<CfgErr> for IrErr {
// 	fn from (e: CfgErr) -> IrErr { IrErrData::from(e).into() }
// }

// impl From<TyErr> for IrErr {
// 	fn from (e: TyErr) -> IrErr { IrErrData::from(e).into() }
// }

pub type IrDataResult<T = ()> = Result<T, IrErrData>;
pub type FunctionResult<T = ()> = Result<T, FunctionErr>;
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


pub trait Locate<L> {
	type Result;
	fn at (self, location: L) -> Self::Result;
}

impl Locate<IrErrLocation> for IrErrData {
	type Result = IrErr;
	fn at (self, location: IrErrLocation) -> IrErr {
		IrErr {
			data: self,
			location
		}
	}
}

impl Locate<FunctionErrLocation> for IrErrData {
	type Result = FunctionErr;
	fn at (self, location: FunctionErrLocation) -> FunctionErr {
		FunctionErr {
			data: self,
			location
		}
	}
}

impl Locate<IrErrLocation> for TyErr {
	type Result = IrErr;
	fn at (self, location: IrErrLocation) -> IrErr {
		IrErr {
			data: IrErrData::TyErr(self),
			location
		}
	}
}

impl Locate<FunctionErrLocation> for TyErr {
	type Result = FunctionErr;
	fn at (self, location: FunctionErrLocation) -> FunctionErr {
		FunctionErr {
			data: IrErrData::TyErr(self),
			location
		}
	}
}

impl Locate<IrErrLocation> for CfgErr {
	type Result = IrErr;
	fn at (self, location: IrErrLocation) -> IrErr {
		IrErr {
			data: IrErrData::CfgErr(self),
			location
		}
	}
}

impl Locate<FunctionErrLocation> for CfgErr {
	type Result = FunctionErr;
	fn at (self, location: FunctionErrLocation) -> FunctionErr {
		FunctionErr {
			data: IrErrData::CfgErr(self),
			location
		}
	}
}

impl Locate<FunctionKey> for FunctionErrLocation {
	type Result = IrErrLocation;
	fn at (self, location: FunctionKey) -> IrErrLocation {
		IrErrLocation::Function(location, self)
	}
}

impl Locate<FunctionKey> for FunctionErr {
	type Result = IrErr;
	fn at (self, location: FunctionKey) -> IrErr {
		IrErr {
			data: self.data,
			location: self.location.at(location)
		}
	}
}


impl<T, E, D> Locate<D> for Result<T, E>
where E: Locate<D>
{
	type Result = Result<T, E::Result>;
	fn at (self, location: D) -> Self::Result {
		self.map_err(|e| e.at(location))
	}
}










pub struct BlockManipulator<'a> (KeyedMut<'a, Block>);

impl<'a> ops::Deref for BlockManipulator<'a> {
	type Target = KeyedMut<'a, Block>;
	fn deref (&self) -> &Self::Target {
		&self.0
	}
}

impl<'a> ops::DerefMut for BlockManipulator<'a> {
	fn deref_mut	(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl<'a> AsRef<Block> for BlockManipulator<'a> {
	fn as_ref (&self) -> &Block { self.value }
}

impl<'a> AsMut<Block> for BlockManipulator<'a> {
	fn as_mut (&mut self) -> &mut Block { self.value }
}

impl<'a> AsKey<BlockKey> for BlockManipulator<'a> {
	fn as_key(&self) -> BlockKey { self.0.as_key() }
}

impl<'a> BlockManipulator<'a> {
	pub fn set_name (mut self, name: &str) -> Self {
		self.name = Some(name.to_owned());
		self
	}

	pub fn into_ref (self) -> &'a Block {
		self.0.into_ref()
	}

	pub fn into_mut (self) -> &'a mut Block {
		self.0.into_mut()
	}

	pub fn into_key (self) -> BlockKey {
		self.0.into_key()
	}

	pub fn into_keyed (self) -> Keyed<'a, Block> {
		self.0.into_keyed()
	}

	pub fn into_keyed_mut (self) -> KeyedMut<'a, Block> {
		self.0
	}
}

pub struct ParamManipulator<'a> (KeyedMut<'a, Param>);

impl<'a> ops::Deref for ParamManipulator<'a> {
	type Target = KeyedMut<'a, Param>;
	fn deref (&self) -> &Self::Target {
		&self.0
	}
}

impl<'a> ops::DerefMut for ParamManipulator<'a> {
	fn deref_mut	(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl<'a> AsRef<Param> for ParamManipulator<'a> {
	fn as_ref (&self) -> &Param { self.value }
}

impl<'a> AsMut<Param> for ParamManipulator<'a> {
	fn as_mut (&mut self) -> &mut Param { self.value }
}

impl<'a> AsKey<ParamKey> for ParamManipulator<'a> {
	fn as_key(&self) -> ParamKey { self.0.as_key() }
}

impl<'a> ParamManipulator<'a> {
	pub fn set_name (mut self, name: &str) -> Self {
		self.name = Some(name.to_owned());
		self
	}

	pub fn set_ty<K: AsKey<TyKey>> (mut self, ty: K) -> Self {
		self.ty = ty.as_key();
		self
	}

	pub fn set_src (mut self, src_attribution: SrcAttribution) -> Self {
		self.src = Some(src_attribution);
		self
	}

	pub fn clear_src (mut self) -> Self {
		self.src = None;
		self
	}

	pub fn add_meta (mut self, meta_key: ParamMetaKey) -> Self {
		self.meta.push(meta_key);
		self
	}

	pub fn into_ref (self) -> &'a Param {
		self.0.into_ref()
	}

	pub fn into_mut (self) -> &'a mut Param {
		self.0.into_mut()
	}

	pub fn into_key (self) -> ParamKey {
		self.0.into_key()
	}

	pub fn into_keyed (self) -> Keyed<'a, Param> {
		self.0.into_keyed()
	}

	pub fn into_keyed_mut (self) -> KeyedMut<'a, Param> {
		self.0
	}
}



pub struct LocalManipulator<'a> (KeyedMut<'a, Local>);

impl<'a> ops::Deref for LocalManipulator<'a> {
	type Target = KeyedMut<'a, Local>;
	fn deref (&self) -> &Self::Target {
		&self.0
	}
}

impl<'a> ops::DerefMut for LocalManipulator<'a> {
	fn deref_mut	(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl<'a> AsRef<Local> for LocalManipulator<'a> {
	fn as_ref (&self) -> &Local { self.value }
}

impl<'a> AsMut<Local> for LocalManipulator<'a> {
	fn as_mut (&mut self) -> &mut Local { self.value }
}

impl<'a> AsKey<LocalKey> for LocalManipulator<'a> {
	fn as_key(&self) -> LocalKey { self.0.as_key() }
}

impl<'a> LocalManipulator<'a> {
	pub fn set_name (mut self, name: &str) -> Self {
		self.name = Some(name.to_owned());
		self
	}

	pub fn set_ty<K: AsKey<TyKey>> (mut self, ty: K) -> Self {
		self.ty = ty.as_key();
		self
	}

	pub fn set_src (mut self, src_attribution: SrcAttribution) -> Self {
		self.src = Some(src_attribution);
		self
	}

	pub fn clear_src (mut self) -> Self {
		self.src = None;
		self
	}

	pub fn add_meta (mut self, meta_key: LocalMetaKey) -> Self {
		self.meta.push(meta_key);
		self
	}

	pub fn into_ref (self) -> &'a Local {
		self.0.into_ref()
	}

	pub fn into_mut (self) -> &'a mut Local {
		self.0.into_mut()
	}

	pub fn into_key (self) -> LocalKey {
		self.0.into_key()
	}

	pub fn into_keyed (self) -> Keyed<'a, Local> {
		self.0.into_keyed()
	}

	pub fn into_keyed_mut (self) -> KeyedMut<'a, Local> {
		self.0
	}
}



pub struct GlobalManipulator<'a> (KeyedMut<'a, Global>);

impl<'a> ops::Deref for GlobalManipulator<'a> {
	type Target = KeyedMut<'a, Global>;
	fn deref (&self) -> &Self::Target {
		&self.0
	}
}

impl<'a> ops::DerefMut for GlobalManipulator<'a> {
	fn deref_mut	(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl<'a> AsRef<Global> for GlobalManipulator<'a> {
	fn as_ref (&self) -> &Global { self.value }
}

impl<'a> AsMut<Global> for GlobalManipulator<'a> {
	fn as_mut (&mut self) -> &mut Global { self.value }
}

impl<'a> AsKey<GlobalKey> for GlobalManipulator<'a> {
	fn as_key(&self) -> GlobalKey { self.0.as_key() }
}

impl<'a> GlobalManipulator<'a> {
	pub fn set_name (mut self, name: &str) -> Self {
		self.name = Some(name.to_owned());
		self
	}

	pub fn set_src (mut self, src_attribution: SrcAttribution) -> Self {
		self.src = Some(src_attribution);
		self
	}

	pub fn clear_src (mut self) -> Self {
		self.src = None;
		self
	}

	pub fn add_meta (mut self, meta_key: GlobalMetaKey) -> Self {
		self.meta.push(meta_key);
		self
	}

	pub fn into_ref (self) -> &'a Global {
		self.0.into_ref()
	}

	pub fn into_mut (self) -> &'a mut Global {
		self.0.into_mut()
	}

	pub fn into_key (self) -> GlobalKey {
		self.0.into_key()
	}

	pub fn into_keyed (self) -> Keyed<'a, Global> {
		self.0.into_keyed()
	}

	pub fn into_keyed_mut (self) -> KeyedMut<'a, Global> {
		self.0
	}
}



pub struct FunctionManipulator<'a> (KeyedMut<'a, Function>);

impl<'a> ops::Deref for FunctionManipulator<'a> {
	type Target = KeyedMut<'a, Function>;
	fn deref (&self) -> &Self::Target {
		&self.0
	}
}

impl<'a> ops::DerefMut for FunctionManipulator<'a> {
	fn deref_mut	(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl<'a> AsRef<Function> for FunctionManipulator<'a> {
	fn as_ref (&self) -> &Function { self.value }
}

impl<'a> AsMut<Function> for FunctionManipulator<'a> {
	fn as_mut (&mut self) -> &mut Function { self.value }
}

impl<'a> AsKey<FunctionKey> for FunctionManipulator<'a> {
	fn as_key(&self) -> FunctionKey { self.0.as_key() }
}

impl<'a> FunctionManipulator<'a> {
	pub fn set_name (mut self, name: &str) -> Self {
		self.name = Some(name.to_owned());
		self
	}

	pub fn set_src (mut self, src_attribution: SrcAttribution) -> Self {
		self.src = Some(src_attribution);
		self
	}

	pub fn clear_src (mut self) -> Self {
		self.src = None;
		self
	}

	pub fn add_meta (mut self, meta_key: FunctionMetaKey) -> Self {
		self.meta.push(meta_key);
		self
	}

	pub fn into_ref (self) -> &'a Function {
		self.0.into_ref()
	}

	pub fn into_mut (self) -> &'a mut Function {
		self.0.into_mut()
	}

	pub fn into_key (self) -> FunctionKey {
		self.0.into_key()
	}

	pub fn into_keyed (self) -> Keyed<'a, Function> {
		self.0.into_keyed()
	}

	pub fn into_keyed_mut (self) -> KeyedMut<'a, Function> {
		self.0
	}
}



pub struct TyManipulator<'a> (KeyedMut<'a, Ty>);

impl<'a> ops::Deref for TyManipulator<'a> {
	type Target = KeyedMut<'a, Ty>;
	fn deref (&self) -> &Self::Target {
		&self.0
	}
}

impl<'a> ops::DerefMut for TyManipulator<'a> {
	fn deref_mut	(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl<'a> AsRef<Ty> for TyManipulator<'a> {
	fn as_ref (&self) -> &Ty { self.value }
}

impl<'a> AsMut<Ty> for TyManipulator<'a> {
	fn as_mut (&mut self) -> &mut Ty { self.value }
}

impl<'a> AsKey<TyKey> for TyManipulator<'a> {
	fn as_key(&self) -> TyKey { self.0.as_key() }
}

impl<'a> TyManipulator<'a> {
	pub fn set_name (mut self, name: &str) -> Self {
		self.name = Some(name.to_owned());
		self
	}

	pub fn set_src (mut self, src_attribution: SrcAttribution) -> Self {
		self.src = Some(src_attribution);
		self
	}

	pub fn clear_src (mut self) -> Self {
		self.src = None;
		self
	}

	pub fn add_meta (mut self, meta_key: TyMetaKey) -> Self {
		self.meta.push(meta_key);
		self
	}

	pub fn into_ref (self) -> &'a Ty {
		self.0.into_ref()
	}

	pub fn into_mut (self) -> &'a mut Ty {
		self.0.into_mut()
	}

	pub fn into_key (self) -> TyKey {
		self.0.into_key()
	}

	pub fn into_keyed (self) -> Keyed<'a, Ty> {
		self.0.into_keyed()
	}

	pub fn into_keyed_mut (self) -> KeyedMut<'a, Ty> {
		self.0
	}
}


pub struct IrManipulator<'a> (&'a mut Ir);

impl<'a> ops::Deref for IrManipulator<'a> {
	type Target = &'a mut Ir;
	fn deref (&self) -> &Self::Target {
		&self.0
	}
}

impl<'a> ops::DerefMut for IrManipulator<'a> {
	fn deref_mut	(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

impl<'a> IrManipulator<'a> {
	pub fn set_name (mut self, name: &str) -> Self {
		self.name = Some(name.to_owned());
		self
	}

	pub fn set_src (mut self, src_attribution: SrcAttribution) -> Self {
		self.src = Some(src_attribution);
		self
	}

	pub fn clear_src (mut self) -> Self {
		self.src = None;
		self
	}

	pub fn add_meta (mut self, meta_key: IrMetaKey) -> Self {
		self.meta.push(meta_key);
		self
	}

	pub fn into_ref (self) -> &'a Ir {
		self.0
	}

	pub fn into_mut (self) -> &'a mut Ir {
		self.0
	}
}




pub enum Either<A, B> {
	A(A),
	B(B),
}

pub struct BuilderResult<T, E> {
	pub value: T,
	pub error: Option<E>,
}


impl<T, E> BuilderResult<T, E> {
	pub fn new (value: T, error: Option<E>) -> Self {
		Self { value, error }
	}

	pub fn into_error (self) -> Result<T, E> {
		match self.error {
			None => Ok(self.value),
			Some(e) => Err(e),
		}
	}

	pub fn unwrap (self) -> T
	where E: std::fmt::Debug
	{
		if let Some(err) = self.error {
			panic!("Cannot unwrap BuilderResult: {:#?}", err)
		}

		self.value
	}

	pub fn expect (self, description: &str) -> T
	where E: std::fmt::Debug
	{
		if let Some(err) = self.error {
			panic!("Expected {} for BuilderResult but found err: {:#?}", description, err)
		}

		self.value
	}

	pub fn map<U> (self, f: impl FnOnce (T) -> U) -> BuilderResult<U, E> {
		BuilderResult::new(f(self.value), self.error)
	}
}

use std::fmt;
use crate::printer::{ self, PrinterState };

pub trait RichUnwrap<'c> {
	type Printer: fmt::Display;
	fn print (self, state: PrinterState<'c>) -> Self::Printer;
}

impl<'c> RichUnwrap<'c> for TyManipulator<'c> {
	type Printer = printer::TyPrinter<'c, 'c>;
	fn print (self, state: PrinterState<'c>) -> Self::Printer {
		Keyed::<'c, Ty>::create_printer(self.into_keyed(), state)
	}
}

impl<'c> RichUnwrap<'c> for Keyed<'c, Ty> {
	type Printer = printer::TyPrinter<'c, 'c>;
	fn print (self, state: PrinterState<'c>) -> Self::Printer {
		Keyed::<'c, Ty>::create_printer(self, state)
	}
}

impl<'c> RichUnwrap<'c> for TyKey {
	type Printer = printer::TyPrinter<'c, 'c>;
	fn print (self, state: PrinterState<'c>) -> Self::Printer {
		Keyed::<'c, Ty>::create_printer(Keyed::new(self, state.ctx.tys.get(self).unwrap()), state)
	}
}


impl<'c> RichUnwrap<'c> for GlobalManipulator<'c> {
	type Printer = printer::GlobalPrinter<'c, 'c>;
	fn print (self, state: PrinterState<'c>) -> Self::Printer {
		Keyed::<'c, Global>::create_printer(self.into_keyed(), state)
	}
}

impl<'c> RichUnwrap<'c> for Keyed<'c, Global> {
	type Printer = printer::GlobalPrinter<'c, 'c>;
	fn print (self, state: PrinterState<'c>) -> Self::Printer {
		Keyed::<'c, Global>::create_printer(self, state)
	}
}

impl<'c> RichUnwrap<'c> for GlobalKey {
	type Printer = printer::GlobalPrinter<'c, 'c>;
	fn print (self, state: PrinterState<'c>) -> Self::Printer {
		Keyed::<'c, Global>::create_printer(Keyed::new(self, state.ctx.globals.get(self).unwrap()), state)
	}
}


impl<'c> RichUnwrap<'c> for FunctionManipulator<'c> {
	type Printer = printer::FunctionPrinter<'c, 'c>;
	fn print (self, state: PrinterState<'c>) -> Self::Printer {
		Keyed::<'c, Function>::create_printer(self.into_keyed(), state)
	}
}

impl<'c> RichUnwrap<'c> for Keyed<'c, Function> {
	type Printer = printer::FunctionPrinter<'c, 'c>;
	fn print (self, state: PrinterState<'c>) -> Self::Printer {
		Keyed::<'c, Function>::create_printer(self, state)
	}
}

impl<'c> RichUnwrap<'c> for FunctionKey {
	type Printer = printer::FunctionPrinter<'c, 'c>;
	fn print (self, state: PrinterState<'c>) -> Self::Printer {
		Keyed::<'c, Function>::create_printer(Keyed::new(self, state.ctx.functions.get(self).unwrap()), state)
	}
}

impl<'c, T> BuilderResult<T, IrErr> {
	pub fn take_rich<U: RichUnwrap<'c>> (self, ctx: &'c Context, f: impl FnOnce (T) -> U) -> U {
		self.map(f).unwrap_rich(ctx)
	}
}

impl<'c, T: RichUnwrap<'c>> BuilderResult<T, IrErr> {
	#[track_caller]
	pub fn unwrap_rich (self, ctx: &'c Context) -> T {
		if let Some(err) = self.error {
			let state = PrinterState::new(ctx).with_error(err);
			panic!("{}\n\nCannot unwrap BuilderResult:\n{}", state.print_self(), self.value.print(state))
		}

		self.value
	}
}



#[derive(Debug, Default)]
pub struct TyDict {
	void: TyKey,
	block: TyKey,
	bool: TyKey,
	sint8: TyKey, sint16: TyKey, sint32: TyKey, sint64: TyKey, sint128: TyKey,
	uint8: TyKey, uint16: TyKey, uint32: TyKey, uint64: TyKey, uint128: TyKey,
	real32: TyKey, real64: TyKey,
}

#[derive(Debug)]
pub struct Builder<'c> {
	pub ctx: &'c mut Context,
	tys: TyDict,
}


impl<'c> Builder<'c> {
	pub fn new (ctx: &'c mut Context) -> Self {
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

		let tys = prims! [
			(void: TyData::Void),
			(block: TyData::Block),
			(bool: Bool),
			(sint8: SInt8), (sint16: SInt16), (sint32: SInt32), (sint64: SInt64), (sint128: SInt128),
			(uint8: UInt8), (uint16: UInt16), (uint32: UInt32), (uint64: UInt64), (uint128: UInt128),
			(real32: Real32), (real64: Real64),
		];



		Self { ctx, tys }
	}

	pub fn const_zero (&self, ty_key: impl AsKey<TyKey>) -> IrDataResult<Constant> {
		let ty_key = ty_key.as_key();
		let ty = self.get_ty(ty_key)?;

		Ok(match &ty.data {
			TyData::Void
			=> return Err(TyErr::TypeHasNoNull(ty_key).into()),

			| TyData::Block
			| TyData::Pointer { .. }
			| TyData::Function { .. }
			=> Constant::Null(ty_key),

			TyData::Primitive(prim)
			=> prim.const_zero(),

			TyData::Array { .. }  | TyData::Structure { .. }
			=> Constant::Aggregate(ty_key, ConstantAggregateData::Zeroed),
		})
	}

	pub fn void_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.void).unwrap() }
	pub fn block_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.block).unwrap() }

	pub fn bool_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.bool).unwrap() }

	pub fn sint8_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.sint8).unwrap() }
	pub fn sint16_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.sint16).unwrap() }
	pub fn sint32_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.sint32).unwrap() }
	pub fn sint64_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.sint64).unwrap() }
	pub fn sint128_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.sint128).unwrap() }

	pub fn uint8_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.uint8).unwrap() }
	pub fn uint16_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.uint16).unwrap() }
	pub fn uint32_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.uint32).unwrap() }
	pub fn uint64_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.uint64).unwrap() }
	pub fn uint128_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.uint128).unwrap() }

	pub fn real32_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.real32).unwrap() }
	pub fn real64_ty (&self) -> Keyed<Ty> { self.ctx.tys.get_keyed(self.tys.real64).unwrap() }


	pub fn pointer_ty<K: AsKey<TyKey>> (&mut self, target_ty: K) -> IrDataResult<TyManipulator> {
		let target_ty = self.get_ty(target_ty)?.as_key();

		Ok(TyManipulator(self.ctx.add_ty(TyData::Pointer { target_ty }.into())))
	}

	pub fn array_ty<K: AsKey<TyKey>> (&mut self, length: u32, element_ty: K) -> IrDataResult<TyManipulator> {
		let element_ty = self.get_ty(element_ty)?.as_key();

		Ok(TyManipulator(self.ctx.add_ty(TyData::Array { length, element_ty }.into())))
	}

	pub fn empty_structure_ty (&mut self) -> TyManipulator {
		TyManipulator(self.ctx.add_ty(TyData::Structure { field_tys: Vec::default() }.into()))
	}

	pub fn set_structure_ty_body (&mut self, ty_key: TyKey, body: Vec<TyKey>) -> IrDataResult<TyManipulator> {
		match self.get_ty_mut(ty_key).map(KeyedMut::into_mut) {
			Ok(Ty { data: TyData::Structure { field_tys }, .. }) => {
				assert(field_tys.is_empty(), IrErrData::TyErr(TyErr::ExpectedStructure(ty_key)))?;
				*field_tys = body;
				Ok(TyManipulator(self.get_ty_mut(ty_key).unwrap()))
			}
			Err(e) => Err(e),
			_ => Err(IrErrData::TyErr(TyErr::ExpectedStructure(ty_key)))
		}
	}

	pub fn structure_ty (&mut self, field_tys: Vec<TyKey>) -> IrDataResult<TyManipulator> {
		for &ft in field_tys.iter() {
			self.get_ty(ft)?;
		}

		Ok(TyManipulator(self.ctx.add_ty(TyData::Structure { field_tys }.into())))
	}

	pub fn function_ty (&mut self, parameter_tys: Vec<TyKey>, result_ty: Option<TyKey>) -> IrDataResult<TyManipulator> {
		for &pt in parameter_tys.iter() {
			self.get_ty(pt)?;
		}

		if let Some(rt) = result_ty {
			self.get_ty(rt)?;
		}

		Ok(TyManipulator(self.ctx.add_ty(TyData::Function { parameter_tys, result_ty}.into())))
	}



	pub fn get_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrDataResult<Keyed<Ty>> {
		let ty_key = ty_key.as_key();

		self.ctx.tys.get_keyed(ty_key).ok_or(IrErrData::InvalidTyKey(ty_key))
	}

	pub fn get_ty_mut<K: AsKey<TyKey>> (&mut self, ty_key: K) -> IrDataResult<KeyedMut<Ty>> {
		let ty_key = ty_key.as_key();

		self.ctx.tys.get_keyed_mut(ty_key).ok_or(IrErrData::InvalidTyKey(ty_key))
	}


	pub fn get_finalized_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrDataResult<Keyed<Ty>> {
		let ty_key = ty_key.as_key();

		self.finalize_ty(ty_key)?;
		self.get_ty(ty_key)
	}

	pub fn get_finalized_ty_mut<K: AsKey<TyKey>> (&mut self, ty_key: K) -> IrDataResult<KeyedMut<Ty>> {
		let ty_key = ty_key.as_key();

		self.finalize_ty(ty_key)?;
		self.get_ty_mut(ty_key)
	}


	pub fn get_global<K: AsKey<GlobalKey>> (&self, global_key: K) -> IrDataResult<Keyed<Global>> {
		let global_key = global_key.as_key();

		self.ctx.globals.get_keyed(global_key).ok_or(IrErrData::InvalidGlobalKey(global_key))
	}

	pub fn get_global_mut<K: AsKey<GlobalKey>> (&mut self, global_key: K) -> IrDataResult<GlobalManipulator> {
		let global_key = global_key.as_key();

		self.ctx.globals.get_keyed_mut(global_key).ok_or(IrErrData::InvalidGlobalKey(global_key)).map(GlobalManipulator)
	}


	pub fn get_function<K: AsKey<FunctionKey>> (&self, function_key: K) -> IrDataResult<Keyed<Function>> {
		let function_key = function_key.as_key();

		self.ctx.functions.get_keyed(function_key).ok_or(IrErrData::InvalidFunctionKey(function_key))
	}

	pub fn get_function_mut<K: AsKey<FunctionKey>> (&mut self, function_key: K) -> IrDataResult<FunctionManipulator> {
		let function_key = function_key.as_key();

		self.ctx.functions.get_keyed_mut(function_key).ok_or(IrErrData::InvalidFunctionKey(function_key)).map(FunctionManipulator)
	}



	pub fn finalize_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrDataResult<Ref<Layout>> {
		fn finalize_ty_impl<'x> (this: &'x Builder, wip: &mut HashSet<TyKey>, ty_key: TyKey) -> IrDataResult<Ref<'x, Layout>> {
			use TyData::*;

			if !wip.contains(&ty_key) {
				wip.insert(ty_key);
			} else {
				return Err(IrErrData::TyErr(TyErr::InfiniteRecursive(ty_key)));
			}

			let ty = this.get_ty(ty_key)?;

			if ty.layout.borrow().is_none() {
				let layout = match &ty.data {
					Void => Layout::custom_scalar(0, 1),

					&Primitive(prim) => this.ctx.target.primitive_layout(prim),

					Block | &Pointer { .. } | &Function { .. } => this.ctx.target.pointer_layout(),

					&Array { length, element_ty } => {
						let layout_ref = finalize_ty_impl(this, wip, element_ty)?;
						let Layout { size: elem_size, align: elem_align, .. } = layout_ref.deref();
						Layout::custom_scalar(length * *elem_size, *elem_align)
					},

					Structure { field_tys } => {
						let field_tys = field_tys.clone().into_iter();
						let mut size = 0;
						let mut align = 0;

						let mut field_offsets = vec![];

						for field_ty_key in field_tys {
							let layout_ref = finalize_ty_impl(this, wip, field_ty_key)?;
							let Layout { size: field_size, align: field_align, .. } = layout_ref.deref();

							if *field_align > align { align = *field_align }

							let padding = (*field_align - (size % *field_align)) % *field_align;

							size += padding;

							field_offsets.push(size);

							size += *field_size;
						}

						size = if align < 2 { size } else { ((size + align - 1) / align) * align };

						Layout::structure(size, align, field_offsets)
					}
				};

				this.ctx.tys.get(ty_key).unwrap().layout.borrow_mut().replace(layout);
			}

			let base = this.ctx.tys.get(ty_key).unwrap().layout.borrow();

			wip.remove(&ty_key);

			Ok(Ref::map(base, |opt| opt.as_ref().unwrap()))
		}

		finalize_ty_impl(self, &mut HashSet::default(), ty_key.as_key())
	}

	pub fn size_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrDataResult<u32> {
		Ok(self.finalize_ty(ty_key)?.size)
	}

	pub fn align_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrDataResult<u32> {
		Ok(self.finalize_ty(ty_key)?.align)
	}

	pub fn field_offsets_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrDataResult<Ref<[u32]>> {
		let ty_key = ty_key.as_key();

		if self.get_ty(ty_key)?.is_structure() {
			Ok(Ref::map(self.finalize_ty(ty_key)?, |l| l.field_offsets.as_slice()))
		} else {
			Err(TyErr::ExpectedStructure(ty_key.as_key()).into())
		}
	}



	pub fn create_function (&mut self) -> FunctionBuilder<'_, 'c> {
		FunctionBuilder::new(self)
	}


	pub fn create_global (&mut self, ty: TyKey, init: Option<Constant>) -> BuilderResult<GlobalManipulator, IrErr> {
		let g = self.ctx.globals.insert(Global {
			ty,
			init,
			.. Global::default()
		}).as_key();

		let result = ty_checker::check_global(self, g);

		BuilderResult::new(self.get_global_mut(g).unwrap(), result.err())
	}


	/// Warning: This is a very expensive function, it probably isnt necessary to call this under normal circumstances
	pub fn validate_tys (&mut self) -> IrResult {
		for &ty_key in self.ctx.tys.keys() {
			self.get_finalized_ty(ty_key).at(IrErrLocation::Ty(ty_key))?;
		}

		Ok(())
	}

	/// Warning: This is a fairly expensive function, it should only be used if you have manually created globals,
	/// or modified the type or initializer of Globals after creation
	pub fn validate_globals (&mut self) -> IrResult {
		// SAFETY:
		// this is safe because the type checker doesnt mutate globals
		let globals = unsafe {
			std::mem::transmute::<std::slice::Iter<'_, _>, std::slice::Iter<'static, _>>(self.ctx.globals.keys())
		};

		for &global_key in globals {
			ty_checker::check_global(self, global_key)?;
		}

		Ok(())
	}

	/// Warning: This is a very expensive function, it should only be used if you have manually created functions,
	/// or modified functions after FunctionBuilder finalization
	pub fn validate_functions (&mut self) -> IrResult {
		// SAFETY:
		// this is safe because the type checker doesnt mutate functions
		let functions = unsafe {
			std::mem::transmute::<std::slice::Iter<'_, _>, std::slice::Iter<'static, _>>(self.ctx.functions.keys())
		};

		for &function_key in functions {
			let cfg = cfg_generator::generate(self, function_key)?;
			let (cfg, ty_map) = ty_checker::check_function(self, cfg, function_key)?;

			let mut function = self.get_function_mut(function_key).unwrap();

			function.cfg = cfg;
			function.ty_map = ty_map;
		}

		Ok(())
	}


	/// Warning: This is an intensely expensive function, it should only be called if you're absolutely certain you need it
	///
	/// See `validate_tys`, `validate_globals`, and `validate_functions` for more details on the use case
	pub fn validate_all (&mut self) -> IrResult {
		self.validate_tys()?;
		self.validate_globals()?;
		self.validate_functions()
	}
}













#[derive(Debug)]
pub struct FunctionBuilder<'x, 'b> {
	pub builder: &'x mut Builder<'b>,

	function_key: FunctionKey,
	function: Function,

	active_block: Option<BlockKey>,
	insertion_cursor: InsertionCursor,
	active_src: Option<SrcAttribution>,
}



impl<'x, 'b> FunctionBuilder<'x, 'b> {
	pub fn new (builder: &'x mut Builder<'b>) -> Self {
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



	pub fn create_child_function (&mut self) -> FunctionBuilder<'_, 'b> {
		// SAFETY:
		// This mutably borrows self, and all the things produced by this borrow it, so theres no harm here
		FunctionBuilder::new(unsafe { std::mem::transmute::<&'_ mut Builder<'b>, &'_ mut Builder<'_>>(self.builder) })
	}




	pub fn finalize (mut self) -> BuilderResult<FunctionManipulator<'b>, IrErr> {
		self.clear_active_block();

		let function_key = self.function_key;

		if let Err(e) = self.generate_own_ty() {
			// TODO: safety justification
			return unsafe { std::mem::transmute(BuilderResult::new(
				FunctionManipulator(self.builder.ctx.functions.define(function_key, self.function).unwrap()),
				Some(e.at(FunctionErrLocation::Root.at(function_key)))
			)) }
		}

		let builder = self.builder;
		let function = self.function;

		builder.ctx.functions
			.define(
				function_key,
				function
			)
			.unwrap();

		// TODO: safety justification
		unsafe { std::mem::transmute(match cfg_generator::generate(builder, function_key) {
			Ok(cfg) => {
				match ty_checker::check_function(builder, cfg, function_key) {
					Ok((cfg, ty_map)) => {
						let mut function = builder.get_function_mut(function_key).unwrap();

						function.cfg = cfg;
						function.ty_map = ty_map;

						BuilderResult::new(function, None)
					}

					Err(e) => BuilderResult::new(builder.get_function_mut(function_key).unwrap(), Some(e))
				}
			},
			Err(e) => BuilderResult::new(builder.get_function_mut(function_key).unwrap(), Some(e))
		}) }
	}



	pub fn get_own_function (&self) -> Keyed<Function> {
		Keyed { key: self.function_key, value: &self.function }
	}

	pub fn get_own_function_mut (&mut self) -> KeyedMut<Function> {
		KeyedMut { key: self.function_key, value: &mut self.function }
	}


	pub fn set_name (&mut self, name: impl Into<String>) {
		self.function.name = Some(name.into());
	}

	pub fn get_name (&mut self) -> Option<&str> {
		self.function.name.as_deref()
	}

	pub fn clear_name (&mut self) -> Option<String> {
		self.function.name.take()
	}



	pub fn generate_own_ty (&mut self) -> IrDataResult<TyManipulator> {
		let result_ty = if let Some(result_ty) = self.function.result {
			self.builder.get_ty(result_ty)?;
			Some(result_ty)
		} else {
			None
		};

		let mut parameter_tys = vec![];

		for &param_key in self.function.param_order.iter() {
			let param = self.get_param(param_key)?;

			parameter_tys.push(param.ty);
		}

		let ty = self.builder.function_ty(parameter_tys, result_ty)?;

		self.function.ty = ty.as_key();

		Ok(ty)
	}




	pub fn set_return_ty<K: AsKey<TyKey>> (&mut self, ty_key: K) {
		let ty = ty_key.as_key();

		self.function.result = Some(ty)
	}

	pub fn set_no_return_ty (&mut self) {
		self.function.result = None
	}




	pub fn void_ty (&self) -> Keyed<Ty> { self.builder.void_ty() }
	pub fn block_ty (&self) -> Keyed<Ty> { self.builder.block_ty() }
	pub fn bool_ty (&self) -> Keyed<Ty> { self.builder.bool_ty() }
	pub fn sint8_ty (&self) -> Keyed<Ty> { self.builder.sint8_ty() }
	pub fn sint16_ty (&self) -> Keyed<Ty> { self.builder.sint16_ty() }
	pub fn sint32_ty (&self) -> Keyed<Ty> { self.builder.sint32_ty() }
	pub fn sint64_ty (&self) -> Keyed<Ty> { self.builder.sint64_ty() }
	pub fn sint128_ty (&self) -> Keyed<Ty> { self.builder.sint128_ty() }
	pub fn uint8_ty (&self) -> Keyed<Ty> { self.builder.uint8_ty() }
	pub fn uint16_ty (&self) -> Keyed<Ty> { self.builder.uint16_ty() }
	pub fn uint32_ty (&self) -> Keyed<Ty> { self.builder.uint32_ty() }
	pub fn uint64_ty (&self) -> Keyed<Ty> { self.builder.uint64_ty() }
	pub fn uint128_ty (&self) -> Keyed<Ty> { self.builder.uint128_ty() }
	pub fn real32_ty (&self) -> Keyed<Ty> { self.builder.real32_ty() }
	pub fn real64_ty (&self) -> Keyed<Ty> { self.builder.real64_ty() }

	pub fn pointer_ty<K: AsKey<TyKey>> (&mut self, target_ty: K) -> IrDataResult<TyManipulator> { self.builder.pointer_ty(target_ty) }
	pub fn array_ty<K: AsKey<TyKey>> (&mut self, length: u32, element_ty: K) -> IrDataResult<TyManipulator> { self.builder.array_ty(length, element_ty) }
	pub fn empty_structure_ty (&mut self) -> TyManipulator { self.builder.empty_structure_ty() }
	pub fn set_structure_ty_body (&mut self, ty_key: TyKey, body: Vec<TyKey>) -> IrDataResult<TyManipulator> { self.builder.set_structure_ty_body(ty_key, body) }
	pub fn structure_ty (&mut self, field_tys: Vec<TyKey>) -> IrDataResult<TyManipulator> { self.builder.structure_ty(field_tys) }
	pub fn function_ty (&mut self, parameter_tys: Vec<TyKey>, result_ty: Option<TyKey>) -> IrDataResult<TyManipulator> { self.builder.function_ty(parameter_tys, result_ty) }

	pub fn get_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrDataResult<Keyed<Ty>> { self.builder.get_ty(ty_key) }
	pub fn get_ty_mut<K: AsKey<TyKey>> (&mut self, ty_key: K) -> IrDataResult<KeyedMut<Ty>> { self.builder.get_ty_mut(ty_key) }

	pub fn get_global<K: AsKey<GlobalKey>> (&self, global_key: K) -> IrDataResult<Keyed<Global>> { self.builder.get_global(global_key) }
	pub fn get_global_mut<K: AsKey<GlobalKey>> (&mut self, global_key: K) -> IrDataResult<GlobalManipulator> { self.builder.get_global_mut(global_key) }

	pub fn get_function<K: AsKey<FunctionKey>> (&self, function_key: K) -> IrDataResult<Keyed<Function>> {
		let function_key = function_key.as_key();

		if function_key == self.function_key {
			return Ok(Keyed { key: function_key, value: &self.function })
		}

		self.builder.get_function(function_key)
	}

	pub fn get_function_mut<K: AsKey<FunctionKey>> (&mut self, function_key: K) -> IrDataResult<FunctionManipulator> {
		let function_key = function_key.as_key();

		if function_key == self.function_key {
			return Ok(FunctionManipulator(KeyedMut { key: function_key, value: &mut self.function }))
		}

		self.builder.get_function_mut(function_key)
	}

	pub fn finalize_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrDataResult<Ref<Layout>> { self.builder.finalize_ty(ty_key) }

	pub fn size_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrDataResult<u32> { self.builder.size_of(ty_key) }
	pub fn align_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrDataResult<u32> { self.builder.align_of(ty_key) }
	pub fn field_offsets_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrDataResult<Ref<[u32]>> { self.builder.field_offsets_of(ty_key) }



	pub fn make_local<K: AsKey<TyKey>> (&mut self, ty_key: K) -> LocalManipulator {
		let ty = ty_key.as_key();

		LocalManipulator(self.function.locals.insert(Local { ty, .. Local::default() }))
	}

	pub fn get_local<K: AsKey<LocalKey>> (&self, local_key: K) -> IrDataResult<Keyed<Local>> {
		let local_key = local_key.as_key();

		self.function.locals.get_keyed(local_key).ok_or(IrErrData::InvalidLocalKey(local_key))
	}

	pub fn get_local_mut<K: AsKey<LocalKey>> (&mut self, local_key: K) -> IrDataResult<LocalManipulator> {
		let local_key = local_key.as_key();

		self.function.locals.get_keyed_mut(local_key).ok_or(IrErrData::InvalidLocalKey(local_key)).map(LocalManipulator)
	}




	pub fn append_param<K: AsKey<TyKey>> (&mut self, ty_key: K) -> ParamManipulator {
		let ty = ty_key.as_key();

		let param = self.function.param_data.insert(Param { ty, .. Param::default() });

		self.function.param_order.push(param.as_key());

		ParamManipulator(param)
	}

	pub fn insert_param<K: AsKey<TyKey>> (&mut self, idx: usize, ty_key: K) -> ParamManipulator {
		let ty = ty_key.as_key();

		assert!(idx <= self.function.param_order.len(), "Invalid param index");

		let param = self.function.param_data.insert(Param { ty, .. Param::default() });

		self.function.param_order.insert(idx, param.as_key());

		ParamManipulator(param)
	}

	pub fn remove_param<K: AsKey<ParamKey>> (&mut self, param_key: K) -> Param {
		let param_key = param_key.as_key();

		let idx = self.get_param_index(param_key).expect("valid param key");

		let param = self.function.param_data.remove(param_key).unwrap();
		self.function.param_order.remove(idx);

		param
	}


	pub fn move_param_to_start<K: AsKey<ParamKey>> (&mut self, param_key: K) {
		let param_key = param_key.as_key();

		let idx = self.get_param_index(param_key).expect("valid param key");

		if idx != 0 {
			self.function.param_order.remove(idx);
			self.function.param_order.insert(0, param_key);
		}
	}

	pub fn move_param_to_end<K: AsKey<ParamKey>> (&mut self, param_key: K) {
		let param_key = param_key.as_key();

		let idx = self.get_param_index(param_key).expect("valid param key");

		if idx < self.function.param_order.len() - 1 {
			self.function.param_order.remove(idx);
			self.function.param_order.push(param_key);
		}
	}

	pub fn move_param_before<KA: AsKey<ParamKey>, KB: AsKey<ParamKey>> (&mut self, param_to_move: KA, destination_param: KB) {
		let param_to_move = param_to_move.as_key();
		let destination_param = destination_param.as_key();

		let idx_to_move = self.get_param_index(param_to_move).expect("valid param key");
		let destination_idx = self.get_param_index(destination_param).expect("valid param key");

		self.function.param_order.remove(idx_to_move);
		self.function.param_order.insert(destination_idx, param_to_move);
	}

	pub fn move_param_after<KA: AsKey<ParamKey>, KB: AsKey<ParamKey>> (&mut self, param_to_move: KA, destination_param: KB) {
		let param_to_move = param_to_move.as_key();
		let destination_param = destination_param.as_key();

		let idx_to_move = self.get_param_index(param_to_move).expect("valid param key");
		let destination_idx = self.get_param_index(destination_param).expect("valid param key");

		self.function.param_order.remove(idx_to_move);
		self.function.param_order.insert(destination_idx + 1, param_to_move);
	}

	pub fn swap_params<KA: AsKey<ParamKey>, KB: AsKey<ParamKey>> (&mut self, a: KA, b: KB) {
		let a = self.get_param_index(a).expect("valid param key");
		let b = self.get_param_index(b).expect("valid param key");

		self.function.param_order.swap(a, b);
	}


	pub fn get_param_index<K: AsKey<ParamKey>> (&self, param_key: K) -> IrDataResult<usize> {
		let param_key = param_key.as_key();

		self.function.param_order
			.iter()
			.enumerate()
			.find(|&(_, &pk)| pk == param_key)
			.map(|(i, _)| i)
			.ok_or(IrErrData::InvalidParamKey(param_key))
	}

	pub fn get_param<K: AsKey<ParamKey>> (&self, param_key: K) -> IrDataResult<Keyed<Param>> {
		let param_key = param_key.as_key();

		self.function.param_data.get_keyed(param_key).ok_or(IrErrData::InvalidParamKey(param_key))
	}

	pub fn get_param_mut<K: AsKey<ParamKey>> (&mut self, param_key: K) -> IrDataResult<ParamManipulator> {
		let param_key = param_key.as_key();

		self.function.param_data.get_keyed_mut(param_key).ok_or(IrErrData::InvalidParamKey(param_key)).map(ParamManipulator)
	}




	pub fn append_block (&mut self, block: Block) -> BlockManipulator {
		let block = self.function.block_data.insert(block);
		self.function.block_order.push(block.as_key());
		BlockManipulator(block)
	}

	pub fn insert_block (&mut self, idx: usize, block: Block) -> IrDataResult<BlockManipulator> {
		if idx > self.function.block_order.len() { return Err(IrErrData::InvalidBlockIndex(idx)) }

		let block = self.function.block_data.insert(block);

		self.function.block_order.insert(idx, block.as_key());

		Ok(BlockManipulator(block))
	}

	pub fn append_new_block (&mut self) -> BlockManipulator {
		self.append_block(Block::default())
	}

	pub fn insert_new_block (&mut self, idx: usize) -> IrDataResult<BlockManipulator> {
		self.insert_block(idx, Block::default())
	}

	pub fn remove_block<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrDataResult<Block> {
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


	pub fn move_block_to_start<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrDataResult {
		let block_key = block_key.as_key();

		let idx = self.get_block_index(block_key)?;

		self.function.block_order.remove(idx);
		self.function.block_order.insert(0, block_key);

		Ok(())
	}

	pub fn move_block_to_end<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrDataResult {
		let block_key = block_key.as_key();

		let idx = self.get_block_index(block_key)?;

		self.function.block_order.remove(idx);
		self.function.block_order.push(block_key);

		Ok(())
	}

	pub fn move_block_before<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, block_to_move: KA, destination_block: KB) -> IrDataResult {
		let block_to_move = block_to_move.as_key();
		let destination_block = destination_block.as_key();

		let idx_to_move = self.get_block_index(block_to_move)?;
		let destination_idx = self.get_block_index(destination_block)?;

		self.function.block_order.remove(idx_to_move);
		self.function.block_order.insert(destination_idx, block_to_move);

		Ok(())
	}

	pub fn move_block_after<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, block_to_move: KA, destination_block: KB) -> IrDataResult {
		let block_to_move = block_to_move.as_key();
		let destination_block = destination_block.as_key();

		let idx_to_move = self.get_block_index(block_to_move)?;
		let destination_idx = self.get_block_index(destination_block)?;

		self.function.block_order.remove(idx_to_move);
		self.function.block_order.insert(destination_idx + 1, block_to_move);

		Ok(())
	}

	pub fn swap_blocks<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, a: KA, b: KB) -> IrDataResult {
		let a = self.get_block_index(a)?;
		let b = self.get_block_index(b)?;

		self.function.block_order.swap(a, b);

		Ok(())
	}


	pub fn get_block_index<K: AsKey<BlockKey>> (&self, block_key: K) -> IrDataResult<usize> {
		let block_key = block_key.as_key();

		self.function.block_order
			.iter()
			.enumerate()
			.find(|&(_, &br)| br == block_key)
			.map(|(i, _)| i)
			.ok_or(IrErrData::InvalidBlockKey(block_key))
	}

	pub fn get_block<K: AsKey<BlockKey>> (&self, block_key: K) -> IrDataResult<Keyed<Block>> {
		let block_key = block_key.as_key();
		self.function.block_data.get_keyed(block_key).ok_or(IrErrData::InvalidBlockKey(block_key))
	}

	pub fn get_block_mut<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrDataResult<BlockManipulator> {
		let block_key = block_key.as_key();
		self.function.block_data.get_keyed_mut(block_key).ok_or(IrErrData::InvalidBlockKey(block_key)).map(BlockManipulator)
	}

	pub fn get_active_block_key (&self) -> Option<BlockKey> {
		self.active_block
	}

	pub fn get_active_block (&self) -> Keyed<Block> {
		self.get_block(self.get_active_block_key().expect("active block")).unwrap()
	}

	pub fn get_active_block_mut (&mut self) -> BlockManipulator {
		self.get_block_mut(self.get_active_block_key().expect("active block")).unwrap()
	}


	pub fn set_active_block<K: AsKey<BlockKey>> (&mut self, block_key: K) -> Option<(BlockKey, InsertionCursor)> {
		let block_key = block_key.as_key();

		self.get_block(block_key).expect("valid block key for active block");

		let prev_loc = self.clear_active_block();

		self.active_block = Some(block_key);

		prev_loc
	}

	pub fn clear_active_block (&mut self) -> Option<(BlockKey, InsertionCursor)> {
		let block = self.active_block.take();
		let cursor = self.insertion_cursor.take();

		block.map(|block| (block, cursor))
	}




	pub fn get_cursor (&self) -> Option<InsertionCursor> {
		self.active_block?;

		Some(self.insertion_cursor)
	}

	pub fn set_cursor (&mut self, idx: usize) {
		assert!(idx <= self.get_active_block().ir.len(), "Invalid node index");

		self.insertion_cursor = InsertionCursor::Index(idx);
	}

	pub fn move_cursor_to_end (&mut self) {
		self.get_active_block();
		self.insertion_cursor = InsertionCursor::End;
	}

	pub fn move_cursor_to_start (&mut self) {
		self.get_active_block();
		self.insertion_cursor = InsertionCursor::Start;
	}


	pub fn append_node<I: Into<Ir>> (&mut self, i: I) -> IrManipulator {
		let mut node = i.into();

		if node.src.is_none() {
			node.src = self.active_src;
		}

		if let InsertionCursor::Index(cursor) = self.get_cursor().expect("active block") {
			if cursor == self.get_active_block().ir.len() - 1 {
				self.set_cursor(cursor + 1);
			}
		}

		let mut block = self.get_active_block_mut();

		let idx = block.ir.len();

		block.ir.push(node);

		IrManipulator(unsafe { block.into_mut().ir.get_unchecked_mut(idx) })
	}

	pub fn insert_node<I: Into<Ir>> (&mut self, idx: usize, i: I) -> IrManipulator {
		assert!(idx <= self.get_active_block().ir.len(), "Invalid node index");

		if let InsertionCursor::Index(cursor) = self.get_cursor().unwrap() {
			if cursor >= idx {
				self.set_cursor(cursor + 1);
			}
		}

		let mut node = i.into();

		if node.src.is_none() {
			node.src = self.active_src;
		}

		let mut block = self.get_active_block_mut();

		block.ir.insert(idx, node);

		IrManipulator(unsafe { block.into_mut().ir.get_unchecked_mut(idx) })
	}

	pub fn write_node<I: Into<Ir>> (&mut self, i: I) -> IrManipulator {
		let mut node = i.into();

		if node.src.is_none() {
			node.src = self.active_src;
		}

		let idx = match self.get_cursor().expect("active block") {
			InsertionCursor::Start => 0,
			InsertionCursor::Index(idx) => {
				self.set_cursor(idx + 1);
				idx
			},
			InsertionCursor::End => self.get_active_block().ir.len(),
		};

		let mut block = self.get_active_block_mut();

		block.ir.insert(idx, node);

		IrManipulator(unsafe { block.into_mut().ir.get_unchecked_mut(idx) })
	}

	pub fn remove_node (&mut self, idx: usize) -> Ir {
		assert!(idx < self.get_active_block().ir.len(), "Invalid node index");

		if let InsertionCursor::Index(cursor) = self.get_cursor().unwrap() {
			if cursor >= idx {
				self.set_cursor(cursor.saturating_sub(1));
			}
		}

		let mut block = self.get_active_block_mut();

		block.ir.remove(idx)
	}


	pub fn move_node_to_start (&mut self, idx: usize) {
		let mut block = self.get_active_block_mut();

		block.ir.get(idx).expect("valid node index");

		let node = block.ir.remove(idx);
		block.ir.insert(0, node);
	}

	pub fn move_node_to_end (&mut self, idx: usize) {
		let mut block = self.get_active_block_mut();

		block.ir.get(idx).expect("valid node index");

		let node = block.ir.remove(idx);
		block.ir.push(node);
	}

	pub fn move_node_before (&mut self, idx_to_move: usize, destination_idx: usize) {
		let mut block = self.get_active_block_mut();

		block.ir.get(idx_to_move).expect("valid node index");
		block.ir.get(destination_idx).expect("valid node index");

		let node = block.ir.remove(idx_to_move);
		block.ir.insert(destination_idx, node);
	}

	pub fn move_node_after (&mut self, idx_to_move: usize, destination_idx: usize) {
		let mut block = self.get_active_block_mut();

		block.ir.get(idx_to_move).expect("valid node index");
		block.ir.get(destination_idx).expect("valid node index");

		let node = block.ir.remove(idx_to_move);
		block.ir.insert(destination_idx + 1, node);
	}

	pub fn swap_nodes (&mut self, a_idx: usize, b_idx: usize) {
		let mut block = self.get_active_block_mut();

		block.ir.get(a_idx).expect("valid node index");
		block.ir.get(b_idx).expect("valid node index");

		block.ir.swap(a_idx, b_idx);
	}


	pub fn get_node (&self, idx: usize) -> IrDataResult<&Ir> {
		self.get_active_block().into_ref().ir.get(idx).ok_or(IrErrData::InvalidNodeIndex(idx))
	}

	pub fn get_node_mut (&mut self, idx: usize) -> IrDataResult<IrManipulator> {
		self.get_active_block_mut().into_mut().ir.get_mut(idx).ok_or(IrErrData::InvalidNodeIndex(idx)).map(IrManipulator)
	}


	pub fn constant (&mut self, constant: Constant) -> IrManipulator { self.write_node(IrData::Constant(constant)) }

	pub fn const_null<K: AsKey<TyKey>> (&mut self, ty_key: K) -> IrManipulator { self.constant(Constant::Null(ty_key.as_key())) }
	pub fn const_bool (&mut self, value: bool) -> IrManipulator { self.constant(Constant::Bool(value)) }
	pub fn const_sint8 (&mut self, value: i8) -> IrManipulator { self.constant(Constant::SInt8(value)) }
	pub fn const_sint16 (&mut self, value: i16) -> IrManipulator { self.constant(Constant::SInt16(value)) }
	pub fn const_sint32 (&mut self, value: i32) -> IrManipulator { self.constant(Constant::SInt32(value)) }
	pub fn const_sint64 (&mut self, value: i64) -> IrManipulator { self.constant(Constant::SInt64(value)) }
	pub fn const_sint128 (&mut self, value: i128) -> IrManipulator { self.constant(Constant::SInt128(value)) }
	pub fn const_uint8 (&mut self, value: u8) -> IrManipulator { self.constant(Constant::UInt8(value)) }
	pub fn const_uint16 (&mut self, value: u16) -> IrManipulator { self.constant(Constant::UInt16(value)) }
	pub fn const_uint32 (&mut self, value: u32) -> IrManipulator { self.constant(Constant::UInt32(value)) }
	pub fn const_uint64 (&mut self, value: u64) -> IrManipulator { self.constant(Constant::UInt64(value)) }
	pub fn const_uint128 (&mut self, value: u128) -> IrManipulator { self.constant(Constant::UInt128(value)) }
	pub fn const_real32 (&mut self, value: f32) -> IrManipulator { self.constant(Constant::Real32(value)) }
	pub fn const_real64 (&mut self, value: f64) -> IrManipulator { self.constant(Constant::Real64(value)) }



	pub fn build_aggregate<K: AsKey<TyKey>> (&mut self, ty_key: K, data: AggregateData) -> IrManipulator {
		let ty_key = ty_key.as_key();

		self.write_node(IrData::BuildAggregate(ty_key, data))
	}

	pub fn get_element (&mut self, idx: u32) -> IrManipulator {
		self.write_node(IrData::GetElement(idx))
	}

	pub fn set_element (&mut self, idx: u32) -> IrManipulator {
		self.write_node(IrData::SetElement(idx))
	}

	pub fn global_ref<K: AsKey<GlobalKey>> (&mut self, key: K) -> IrManipulator {
		let key = key.as_key();

		self.write_node(IrData::GlobalRef(key))
	}

	pub fn function_ref<K: AsKey<FunctionKey>> (&mut self, key: K) -> IrManipulator {
		let key = key.as_key();

		self.write_node(IrData::FunctionRef(key))
	}

	pub fn block_ref<K: AsKey<BlockKey>> (&mut self, key: K) -> IrManipulator {
		let key = key.as_key();

		self.write_node(IrData::BlockRef(key))
	}

	pub fn param_ref<K: AsKey<ParamKey>> (&mut self, key: K) -> IrManipulator {
		let key = key.as_key();

		self.write_node(IrData::ParamRef(key))
	}

	pub fn local_ref<K: AsKey<LocalKey>> (&mut self, key: K) -> IrManipulator {
		let key = key.as_key();

		self.write_node(IrData::LocalRef(key))
	}


	pub fn phi<K: AsKey<TyKey>> (&mut self, key: K) -> IrManipulator {
		let key = key.as_key();

		self.write_node(IrData::Phi(key))
	}


	pub fn binary_op (&mut self, op: BinaryOp) -> IrManipulator {
		self.write_node(IrData::BinaryOp(op))
	}

	pub fn unary_op (&mut self, op: UnaryOp) -> IrManipulator {
		self.write_node(IrData::UnaryOp(op))
	}

	pub fn cast_op<K: AsKey<TyKey>> (&mut self, op: CastOp, ty_key: K) -> IrManipulator {
		let ty_key = ty_key.as_key();

		self.write_node(IrData::CastOp(op, ty_key))
	}


	pub fn gep (&mut self, num_indices: u32) -> IrManipulator {
		self.write_node(IrData::Gep(num_indices))
	}

	pub fn load (&mut self) -> IrManipulator {
		self.write_node(IrData::Load)
	}

	pub fn store (&mut self) -> IrManipulator {
		self.write_node(IrData::Store)
	}


	pub fn branch<K: AsKey<BlockKey>> (&mut self,	destination: K) -> IrManipulator {
		let destination = destination.as_key();

		self.write_node(IrData::Branch(destination))
	}

	pub fn cond_branch<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, then_block: KA, else_block: KB) -> IrManipulator {
		let then_block = then_block.as_key();
		let else_block = else_block.as_key();

		self.write_node(IrData::CondBranch(then_block, else_block))
	}

	pub fn switch (&mut self, case_blocks: Vec<(Constant, BlockKey)>, default_block: BlockKey) -> IrManipulator {
		self.write_node(IrData::Switch(case_blocks, default_block))
	}

	pub fn computed_branch (&mut self, destinations: Vec<BlockKey>) -> IrManipulator {
		self.write_node(IrData::ComputedBranch(destinations))
	}


	pub fn call (&mut self) -> IrManipulator {
		self.write_node(IrData::Call)
	}

	pub fn ret (&mut self) -> IrManipulator {
		self.write_node(IrData::Ret)
	}


	pub fn duplicate (&mut self, idx: u32) -> IrManipulator {
		self.write_node(IrData::Duplicate(idx))
	}

	pub fn discard (&mut self, idx: u32) -> IrManipulator {
		self.write_node(IrData::Discard(idx))
	}

	pub fn swap (&mut self, idx: u32) -> IrManipulator {
		self.write_node(IrData::Swap(idx))
	}


	pub fn unreachable (&mut self) -> IrManipulator {
		self.write_node(IrData::Unreachable)
	}
}