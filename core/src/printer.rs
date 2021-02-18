use std::{cell::{Ref, RefCell}, fmt, hint::unreachable_unchecked};

use fmt::Display;
use support::utils::index_of;


use support::{
	utils::flip_ref_opt_to_opt_ref,
	slotmap::{ Keyed, AsKey },
};

use super::{
	builder::{
		IrErr,
		IrResult,
		IrErrData,
		IrErrLocation,
		FunctionErrLocation
	},
	src::SrcAttribution,
	ir::{
		GlobalKey,
		Context,
		FunctionCollapsePredictor,
		FunctionKey,
		BinaryOp,
		LocalMetaKey,
		ParamMetaKey,
		AggregateData,
		BlockKey,
		LocalKey,
		IrMetaKey,
		Ir,
		ParamKey,
		ConstantAggregateData,
		GlobalMetaKey,
		Block,
		ContextCollpasePredictor,
		FunctionMetaKey,
		Constant,
		CastOp,
		Function,
		IrData,
		UnaryOp,
	},
	ty::{
		TyKey,
		TyMetaKey,
		PrimitiveTy,
		TyData,
		Ty
	},
};


impl fmt::Display for PrimitiveTy {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			PrimitiveTy::Bool => write!(f, "bool"),
			PrimitiveTy::SInt8 => write!(f, "sint8"),
			PrimitiveTy::SInt16 => write!(f, "sint16"),
			PrimitiveTy::SInt32 => write!(f, "sint32"),
			PrimitiveTy::SInt64 => write!(f, "sint64"),
			PrimitiveTy::SInt128 => write!(f, "sint128"),
			PrimitiveTy::UInt8 => write!(f, "uint8"),
			PrimitiveTy::UInt16 => write!(f, "uint16"),
			PrimitiveTy::UInt32 => write!(f, "uint32"),
			PrimitiveTy::UInt64 => write!(f, "uint64"),
			PrimitiveTy::UInt128 => write!(f, "uint128"),
			PrimitiveTy::Real32 => write!(f, "real32"),
			PrimitiveTy::Real64 => write!(f, "real64"),
		}
	}
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
			CastOp::SIntToUInt => write!(f, "sint_to_uint"),
			CastOp::UIntToSInt => write!(f, "uint_to_sint"),
			CastOp::ZeroExtend => write!(f, "zero_extend"),
			CastOp::SignExtend => write!(f, "sign_extend"),
			CastOp::Truncate => write!(f, "truncate"),
			CastOp::Bitcast => write!(f, "bitcast"),
		}
	}
}



#[derive(Debug)]
pub struct PrinterState<'ctx> {
	ctx: ContextCollpasePredictor<'ctx>,
	function: RefCell<Option<FunctionCollapsePredictor<'ctx>>>,
	err_data: Option<IrErrData>,
	err_location: IrErrLocation,
}

impl<'ctx> PrinterState<'ctx> {
	pub fn new (ctx: &'ctx Context) -> Self {
		Self {
			ctx: ctx.predict_collapse(),
			function: RefCell::new(None),
			err_data: None,
			err_location: IrErrLocation::None,
		}
	}

	pub fn with_err (mut self, err_data: Option<IrErrData>, err_location: IrErrLocation) -> Self {
		if let Some(err_data) = err_data {
			self.set_err_data(err_data);
		} else {
			self.clear_err_data();
		}

		self.set_err_location(err_location);

		self
	}

	pub fn with_result (mut self, result: IrResult) -> Self {
		match result {
			Ok(()) => {
				self.clear_err_data();
				self.clear_err_location();
			}

			Err(IrErr { data, location }) => {
				self.set_err_data(data);
				self.set_err_location(location);
			}
		}

		self
	}

	pub fn set_err_data (&mut self, data: IrErrData) {
		self.err_data.replace(data);
	}

	pub fn clear_err_data (&mut self) {
		self.err_data.take();
	}

	pub fn set_err_location (&mut self, location: IrErrLocation) {
		self.err_location = location;
	}

	pub fn clear_err_location (&mut self) {
		self.err_location = IrErrLocation::None;
	}

	pub fn print_function (&'ctx self, function: FunctionKey) -> FunctionPrinter<'ctx, 'ctx> {
		self.ctx.functions.get_value_keyed(function).unwrap().printer(self)
	}
}


pub trait Printer<'data, 'ctx>: Display {
	type Data: ?Sized;

	fn data (&self) -> Self::Data;
	fn state (&self) -> &'ctx PrinterState<'ctx>;
	fn ctx (&self) -> &'ctx ContextCollpasePredictor<'ctx> { &self.state().ctx }

	fn set_function (&self, function_key: FunctionKey) {
		let fpred = self.ctx().function_predictor(function_key).unwrap();
		self.state().function.borrow_mut().replace(fpred);
	}

	fn clear_function (&self) {
		self.state().function.borrow_mut().take();
	}

	fn get_function (&self) -> Ref<FunctionCollapsePredictor<'ctx>> {
		flip_ref_opt_to_opt_ref(self.state().function.borrow()).unwrap()
	}

	fn child<P: Printable<'data, 'ctx>> (&self, c: P) -> P::Printer {
		c.printer(self.state())
	}

	fn pair<K, V> (&self, p: &'data (K, V)) -> PairPrinter<'data, 'ctx, K, V>
	where
		&'data K: Printable<'data, 'ctx>,
		&'data V: Printable<'data, 'ctx>,
	{
		PairPrinter(p, self.state())
	}

	fn list<P> (&self, l: &'data [P]) -> ListPrinter<'data, 'ctx, P>
	where &'data P: Printable<'data, 'ctx>
	{
		ListPrinter(l, self.state())
	}

	fn pair_list<K, V> (&self, l: &'data [(K, V)]) -> PairListPrinter<'data, 'ctx, K, V>
	where
		&'data K: Printable<'data, 'ctx>,
		&'data V: Printable<'data, 'ctx>,
	{
		PairListPrinter(l, self.state())
	}
}

pub trait Printable<'data, 'ctx> {
	type Printer: Display;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer;
}




pub struct ListPrinter<'data, 'ctx, P: 'data> (&'data [P], &'ctx PrinterState<'ctx>)
where &'data P: Printable<'data, 'ctx>;

impl<'data, 'ctx, P: 'data> Printer<'data, 'ctx> for ListPrinter<'data, 'ctx, P>
where &'data P: Printable<'data, 'ctx>
{
	type Data = &'data [P];

	fn data (&self) -> &'data [P] { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx, P: 'data> fmt::Display for ListPrinter<'data, 'ctx, P>
where &'data P: Printable<'data, 'ctx>
{
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		for (i, e) in self.0.iter().enumerate() {
			self.child(e).fmt(f)?;

			if i < self.0.len() - 1 {
				write!(f, " ")?;
			}
		}
		Ok(())
	}
}

// impl<'data, 'ctx, P: 'data> Printable<'data, 'ctx> for &'data [P]
// where &'data P: Printable<'data, 'ctx>
// {
// 	type Printer = ListPrinter<'data, 'ctx, P>;
// 	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { ListPrinter(self, state) }
// }


pub struct PairListPrinter<'data, 'ctx, K, V> (&'data [(K, V)], &'ctx PrinterState<'ctx>)
where
	&'data K: Printable<'data, 'ctx>,
	&'data V: Printable<'data, 'ctx>,
;

impl<'data, 'ctx, K, V> Printer<'data, 'ctx> for PairListPrinter<'data, 'ctx, K, V>
where
	&'data K: Printable<'data, 'ctx>,
	&'data V: Printable<'data, 'ctx>,
{
	type Data = &'data [(K, V)];

	fn data (&self) -> &'data [(K, V)] { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx, K, V> fmt::Display for PairListPrinter<'data, 'ctx, K, V>
where
	&'data K: Printable<'data, 'ctx>,
	&'data V: Printable<'data, 'ctx>,
{
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		for (i, (k, v)) in self.0.iter().enumerate() {
			self.child(k).fmt(f)?;
			self.child(v).fmt(f)?;

			if i < self.0.len() - 1 {
				write!(f, " ")?;
			}
		}
		Ok(())
	}
}





pub struct DPrinter<'data, 'ctx, D: ?Sized + Display> (&'data D, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx, D: ?Sized + Display> Printer<'data, 'ctx> for DPrinter<'data, 'ctx, D> {
	type Data = &'data D;

	fn data (&self) -> &'data D { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx, D: ?Sized + Display> fmt::Display for DPrinter<'data, 'ctx, D> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", self.0)
	}
}

// impl<'data, 'ctx, D: 'data + Display> Printable<'data, 'ctx> for D {
// 	type Printer = DPrinter<'data, 'ctx, D>;
// 	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { DPrinter(self, state) }
// }

macro_rules! impl_dprinter {
	($($ty:ty),+ $(,)?) => {
		$(
			impl<'data, 'ctx> Printable<'data, 'ctx> for &'data $ty {
				type Printer = DPrinter<'data, 'ctx, $ty>;
				fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { DPrinter(self, state) }
			}
		)+
	};
}


impl_dprinter! {
	u8, u16, u32, u64, u128,
	i8, i16, i32, i64, i128,
	f32, f64,
	str,
}


pub struct PairPrinter<'data, 'ctx, K: 'data, V: 'data> (&'data (K, V), &'ctx PrinterState<'ctx>)
where
	&'data K: Printable<'data, 'ctx>,
	&'data V: Printable<'data, 'ctx>,
;

impl<'data, 'ctx, K: 'data, V: 'data> Printer<'data, 'ctx> for PairPrinter<'data, 'ctx,K, V>
where
	&'data K: Printable<'data, 'ctx>,
	&'data V: Printable<'data, 'ctx>,
{
	type Data = &'data (K, V);

	fn data (&self) -> &'data (K, V) { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx, K: 'data, V: 'data> fmt::Display for PairPrinter<'data, 'ctx, K, V>
where
	&'data K: Printable<'data, 'ctx>,
	&'data V: Printable<'data, 'ctx>,
{
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let (k,v) = self.0;
		write!(f, "({} {})", self.child(k), self.child(v))
	}
}






pub struct TyKeyPrinter<'data, 'ctx> (&'data TyKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for TyKeyPrinter<'data, 'ctx> {
	type Data = &'data TyKey;

	fn data (&self) -> &'data TyKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for TyKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if let Some(ty) = self.ctx().tys.get_value(*self.0) {
			write!(f, "(ty {})", self.child(ty))
		} else {
			write!(f, "(ty (INVALID {:?}))", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data TyKey {
	type Printer = TyKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { TyKeyPrinter(self, state) }
}




pub struct GlobalKeyPrinter<'data, 'ctx> (&'data GlobalKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for GlobalKeyPrinter<'data, 'ctx> {
	type Data = &'data GlobalKey;

	fn data (&self) -> &'data GlobalKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for GlobalKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if let Some(glo) = self.ctx().globals.get_value(*self.data()) {
			if let Some(name) = glo.name.as_ref() {
				write!(f, "(global \"{}\")", name)
			} else if let Some(index) = self.ctx().globals.get_index(*self.data()) {
				write!(f, "(global {})", index)
			} else {
				// SAFETY: if there is a value there is an index
				unsafe { unreachable_unchecked() }
			}
		} else {
			write!(f, "(global (INVALID {:?}))", self.data())
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data GlobalKey {
	type Printer = GlobalKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { GlobalKeyPrinter(self, state) }
}




pub struct FunctionKeyPrinter<'data, 'ctx> (&'data FunctionKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for FunctionKeyPrinter<'data, 'ctx> {
	type Data = &'data FunctionKey;

	fn data (&self) -> &'data FunctionKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for FunctionKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if let Some(func) = self.ctx().functions.get_value(*self.0) {
			if let Some(name) = func.name.as_ref() {
				write!(f, "(function \"{}\")", name)
			} else if let Some(index) = self.ctx().functions.get_index(*self.data()) {
				write!(f, "(function {})", index)
			} else {
				// SAFETY: if there is a value there is an index
				unsafe { unreachable_unchecked() }
			}
		} else {
			write!(f, "(function (INVALID {:?}))", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data FunctionKey {
	type Printer = FunctionKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { FunctionKeyPrinter(self, state) }
}





pub struct BlockKeyPrinter<'data, 'ctx> (&'data BlockKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for BlockKeyPrinter<'data, 'ctx> {
	type Data = &'data BlockKey;

	fn data (&self) -> &'data BlockKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for BlockKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let func = self.get_function();

		if let Some(block) = func.block_data.get(*self.0) {
			if let Some(name) = block.name.as_ref() {
				return write!(f, "(block \"{}\")", name)
			} else if let Some(block_idx) = index_of(func.block_order.iter(), self.0) {
				return write!(f, "(block {})", block_idx)
			}
		}

		write!(f, "(block (INVALID {:?}))", self.0)
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data BlockKey {
	type Printer = BlockKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { BlockKeyPrinter(self, state) }
}




pub struct ParamKeyPrinter<'data, 'ctx> (&'data ParamKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ParamKeyPrinter<'data, 'ctx> {
	type Data = &'data ParamKey;

	fn data (&self) -> &'data ParamKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for ParamKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let func = self.get_function();

		if let Some(param) = func.param_data.get(*self.0) {
			if let Some(name) = param.name.as_ref() {
				return write!(f, "(param \"{}\")", name)
			} else if let Some(param_idx) = index_of(func.param_order.iter(), self.0) {
				return write!(f, "(param {})", param_idx)
			}
		}

		write!(f, "(param (INVALID {:?}))", self.0)
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data ParamKey {
	type Printer = ParamKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { ParamKeyPrinter(self, state) }
}




pub struct LocalKeyPrinter<'data, 'ctx> (&'data LocalKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for LocalKeyPrinter<'data, 'ctx> {
	type Data = &'data LocalKey;

	fn data (&self) -> &'data LocalKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for LocalKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let func = self.get_function();

		if let Some(local) = func.locals.get_value(*self.0) {
			if let Some(name) = local.name.as_ref() {
				write!(f, "(local \"{}\")", name)
			} else if let Some(index) = func.locals.get_index(*self.0) {
				write!(f, "(local {})", index)
			} else {
				// SAFETY: if there is a value there is an index
				unsafe { unreachable_unchecked() }
			}
		} else {
			write!(f, "(local (INVALID {:?}))", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data LocalKey {
	type Printer = LocalKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { LocalKeyPrinter(self, state) }
}



pub struct SrcAttributionPrinter<'data, 'ctx> (&'data SrcAttribution, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for SrcAttributionPrinter<'data, 'ctx> {
	type Data = &'data SrcAttribution;

	fn data (&self) -> &'data SrcAttribution { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for SrcAttributionPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, ":src (", )?;

		if let Some(src) = self.ctx().srcs.get_value(self.0.key) {
			write!(f, "{}", src.path.display())?;
		} else if let Some(idx) = self.ctx().srcs.get_index(self.0.key) {
			write!(f, "{}", idx)?;
		} else {
			write!(f, "(INVALID {:?})", self.0.key)?;
		}

		if let Some(range) = self.0.range {
			if let Some(src) = self.ctx().srcs.get_value(self.0.key) {
				let (line, col) = src.get_line_col(range.0);
				write!(f, ":{}:{}", line, col)?;

				let (eline, ecol) = src.get_line_col(range.1);
				write!(f, " to {}:{}", eline, ecol)?;
			}
		}

		write!(f, ")")
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data SrcAttribution {
	type Printer = SrcAttributionPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { SrcAttributionPrinter(self, state) }
}



pub struct ParamMetaKeyPrinter<'data, 'ctx> (&'data ParamMetaKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ParamMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data ParamMetaKey;

	fn data (&self) -> &'data ParamMetaKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for ParamMetaKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, ":#")?;

		if let Some(idx) = self.ctx().meta.param.get_index(*self.0) {
			write!(f, "{}", idx)
		} else {
			write!(f, "(INVALID {:?})", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data ParamMetaKey {
	type Printer = ParamMetaKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { ParamMetaKeyPrinter(self, state) }
}



pub struct LocalMetaKeyPrinter<'data, 'ctx> (&'data LocalMetaKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for LocalMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data LocalMetaKey;

	fn data (&self) -> &'data LocalMetaKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for LocalMetaKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, ":#")?;

		if let Some(idx) = self.ctx().meta.local.get_index(*self.0) {
			write!(f, "{}", idx)
		} else {
			write!(f, "(INVALID {:?})", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data LocalMetaKey {
	type Printer = LocalMetaKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { LocalMetaKeyPrinter(self, state) }
}



pub struct IrMetaKeyPrinter<'data, 'ctx> (&'data IrMetaKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for IrMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data IrMetaKey;

	fn data (&self) -> &'data IrMetaKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for IrMetaKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, ":#")?;

		if let Some(idx) = self.ctx().meta.ir.get_index(*self.0) {
			write!(f, "{}", idx)
		} else {
			write!(f, "(INVALID {:?})", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data IrMetaKey {
	type Printer = IrMetaKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { IrMetaKeyPrinter(self, state) }
}



pub struct TyMetaKeyPrinter<'data, 'ctx> (&'data TyMetaKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for TyMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data TyMetaKey;

	fn data (&self) -> &'data TyMetaKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for TyMetaKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, ":#")?;

		if let Some(idx) = self.ctx().meta.ty.get_index(*self.0) {
			write!(f, "{}", idx)
		} else {
			write!(f, "(INVALID {:?})", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data TyMetaKey {
	type Printer = TyMetaKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { TyMetaKeyPrinter(self, state) }
}



pub struct FunctionMetaKeyPrinter<'data, 'ctx> (&'data FunctionMetaKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for FunctionMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data FunctionMetaKey;

	fn data (&self) -> &'data FunctionMetaKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for FunctionMetaKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, ":#")?;

		if let Some(idx) = self.ctx().meta.function.get_index(*self.0) {
			write!(f, "{}", idx)
		} else {
			write!(f, "(INVALID {:?})", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data FunctionMetaKey {
	type Printer = FunctionMetaKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { FunctionMetaKeyPrinter(self, state) }
}



pub struct GlobalMetaKeyPrinter<'data, 'ctx> (&'data GlobalMetaKey, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for GlobalMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data GlobalMetaKey;

	fn data (&self) -> &'data GlobalMetaKey { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for GlobalMetaKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, ":#")?;

		if let Some(idx) = self.ctx().meta.global.get_index(*self.0) {
			write!(f, "{}", idx)
		} else {
			write!(f, "(INVALID {:?})", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data GlobalMetaKey {
	type Printer = GlobalMetaKeyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { GlobalMetaKeyPrinter(self, state) }
}





pub struct TyPrinter<'data, 'ctx> (&'data Ty, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for TyPrinter<'data, 'ctx> {
	type Data = &'data Ty;

	fn data (&self) -> &'data Ty { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for TyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if let Some(name) = self.0.name.as_ref() {
			return write!(f, "{}", name)
		}

		match &self.0.data {
			TyData::Void => { write!(f, "void") }
			TyData::Block => { write!(f, "block") }
			TyData::Primitive(primitive_ty) => { write!(f, "{}", primitive_ty) }
			TyData::Pointer { target_ty } => { write!(f, "*{}", self.child(target_ty)) }
			TyData::Array { length, element_ty } => { write!(f, "[{}]{}", length, self.child(element_ty)) }

			TyData::Structure { field_tys } => {
				write!(f, "struct {{ {} }}", self.list(field_tys.as_slice()))
			}

			TyData::Function { parameter_tys, result_ty } => {
				write!(f, "({})", self.list(parameter_tys.as_slice()))?;

				write!(f, " -> ")?;

				if let Some(result_ty) = result_ty {
					self.child(result_ty).fmt(f)
				} else {
					write!(f, "()")
				}
			}
		}?;

		if let Some(src_attr) = self.0.src.as_ref() {
			write!(f, " {}", self.child(src_attr))?;
		}

		for meta_key in self.0.meta.iter() {
			write!(f, " {}", self.child(meta_key))?;
		}

		Ok(())
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data Ty {
	type Printer = TyPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { TyPrinter(self, state) }
}





pub struct ConstantPrinter<'data, 'ctx> (&'data Constant, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ConstantPrinter<'data, 'ctx> {
	type Data = &'data Constant;

	fn data (&self) -> &'data Constant { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for ConstantPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.0 {
			Constant::Null(ty_key) => {
				write!(f, "(null {})", self.child(ty_key))
			}

			Constant::Bool(bool) => { write!(f, "(bool {})", bool) }
			Constant::SInt8(i8) => { write!(f, "(sint8 {})", i8) }
			Constant::SInt16(i16) => { write!(f, "(sint16 {})", i16) }
			Constant::SInt32(i32) => { write!(f, "(sint32 {})", i32) }
			Constant::SInt64(i64) => { write!(f, "(sint64 {})", i64) }
			Constant::SInt128(i128) => { write!(f, "(sint128 {})", i128) }
			Constant::UInt8(u8) => { write!(f, "(uint8 {})", u8) }
			Constant::UInt16(u16) => { write!(f, "(uint16 {})", u16) }
			Constant::UInt32(u32) => { write!(f, "(uint32 {})", u32) }
			Constant::UInt64(u64) => { write!(f, "(uint64 {})", u64) }
			Constant::UInt128(u128) => { write!(f, "(uint128 {})", u128) }
			Constant::Real32(f32) => { write!(f, "(real32 {})", f32) }
			Constant::Real64(f64) => { write!(f, "(real64 {})", f64) }

			Constant::Aggregate(ty_key, constant_aggregate_data) => {
				write!(f, "({} {})", self.child(ty_key), self.child(constant_aggregate_data))
			}
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data Constant {
	type Printer = ConstantPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { ConstantPrinter(self, state) }
}





pub struct ConstantAggregateDataPrinter<'data, 'ctx> (&'data ConstantAggregateData, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ConstantAggregateDataPrinter<'data, 'ctx> {
	type Data = &'data ConstantAggregateData;

	fn data (&self) -> &'data ConstantAggregateData { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for ConstantAggregateDataPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.0 {
			ConstantAggregateData::Uninitialized => { write!(f, "uninitialized") }
			ConstantAggregateData::Zeroed => { write!(f, "zeroed") }
			ConstantAggregateData::CopyFill(box_constant) => { write!(f, "(copy_fill ({}))", self.child(box_constant.as_ref())) }
			ConstantAggregateData::Indexed(indexed_elements) => { write!(f, "(indexed ({}))", self.pair_list(indexed_elements.as_slice())) }
			ConstantAggregateData::Complete(constants) => { write!(f, "(compete ({}))", self.list(constants.as_slice())) }
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data ConstantAggregateData {
	type Printer = ConstantAggregateDataPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { ConstantAggregateDataPrinter(self, state) }
}





pub struct AggregateDataPrinter<'data, 'ctx> (&'data AggregateData, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for AggregateDataPrinter<'data, 'ctx> {
	type Data = &'data AggregateData;

	fn data (&self) -> &'data AggregateData { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for AggregateDataPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.0 {
			AggregateData::Uninitialized => { write!(f, "uninitialized") }
			AggregateData::Zeroed => { write!(f, "zeroed") }
			AggregateData::CopyFill => { write!(f, "copy_fill") }

			AggregateData::Indexed(indices) => { write!(f, "(indexed ({}))", self.list(indices.as_slice())) }

			AggregateData::Complete => { write!(f, "compete") }
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data AggregateData {
	type Printer = AggregateDataPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { AggregateDataPrinter(self, state) }
}





pub struct IrDataPrinter<'data, 'ctx> (&'data IrData, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for IrDataPrinter<'data, 'ctx> {
	type Data = &'data IrData;

	fn data (&self) -> &'data IrData { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for IrDataPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.0 {
			IrData::Constant(constant) => { write!(f, "constant {}", self.child(constant)) }

			IrData::BuildAggregate(ty_key, aggregate_data) => { write!(f, "build_aggregate {} {}", self.child(ty_key), self.child(aggregate_data)) }

			IrData::GlobalRef(global_key) => { write!(f, "ref {}", self.child(global_key)) }
			IrData::FunctionRef(function_key) => { write!(f, "ref {}", self.child(function_key)) }
			IrData::BlockRef(block_key) => { write!(f, "ref {}", self.child(block_key)) }
			IrData::ParamRef(param_key) => { write!(f, "ref {}", self.child(param_key)) }
			IrData::LocalRef(local_key) => { write!(f, "ref {}", self.child(local_key)) }

			IrData::Phi(ty_key) => { write!(f, "phi {}", self.child(ty_key)) }

			IrData::BinaryOp(op) => { write!(f, "binary_op {}", op) }
			IrData::UnaryOp(op) => { write!(f, "unary_op {}", op) }
			IrData::CastOp(op, ty_key) => { write!(f, "cast_op {} {}", op, self.child(ty_key)) }

			IrData::Gep(num_indices) => { write!(f, "gep {}", num_indices) }
			IrData::Load => { write!(f, "load") }
			IrData::Store => { write!(f, "store") }

			IrData::Branch(destination) => { write!(f, "branch {}", self.child(destination)) }
			IrData::CondBranch(then_block_key, else_block_key) => { write!(f, "cond_branch {} {}", self.child(then_block_key), self.child(else_block_key)) }
			IrData::Switch(cases) => { write!(f, "switch ({})", self.pair_list(cases.as_slice())) }
			IrData::ComputedBranch(destinations) => { write!(f, "computed_branch ({})", self.list(destinations.as_slice())) }

			IrData::Call => { write!(f, "call") }
			IrData::Ret => { write!(f, "ret") }

			IrData::Duplicate => { write!(f, "duplicate") }
			IrData::Discard => { write!(f, "discard") }

			IrData::Unreachable => { write!(f, "unreachable") }
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data IrData {
	type Printer = IrDataPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { IrDataPrinter(self, state) }
}



pub struct IrPrinter<'data, 'ctx> (&'data Ir, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for IrPrinter<'data, 'ctx> {
	type Data = &'data Ir;

	fn data (&self) -> &'data Ir { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for IrPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "({}", self.child(&self.0.data))?;

		if let Some(name) = self.0.name.as_ref() {
			write!(f, " :name \"{}\"", name)?;
		}

		if let Some(src_attr) = self.0.src.as_ref() {
			write!(f, " {}", self.child(src_attr))?;
		}

		for meta_key in self.0.meta.iter() {
			write!(f, " {}", self.child(meta_key))?;
		}

		write!(f, ")")
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data Ir {
	type Printer = IrPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { IrPrinter(self, state) }
}



pub struct ErrorPrinter<'data, 'ctx> (Option<&'data IrErrData>, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ErrorPrinter<'data, 'ctx> {
	type Data = Option<&'data IrErrData>;

	fn data (&self) -> Option<&'data IrErrData> { self.0 }
	fn state	(&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for ErrorPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "^ Error")?;

		if let Some(err_data) = self.data() {
			write!(f, ": {:?}", err_data)?;
		}

		Ok(())
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for Option<&'data IrErrData> {
	type Printer = ErrorPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { ErrorPrinter(self, state) }
}





pub struct BlockPrinter<'data, 'ctx> (Keyed<'data, Block>, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for BlockPrinter<'data, 'ctx> {
	type Data = Keyed<'data, Block>;

	fn data (&self) -> Keyed<'data, Block> { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for BlockPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "(block")?;

		if let Some(name) = self.0.name.as_ref() {
			write!(f, " :name \"{}\"", name)?;
		}

		write!(f, " (body")?;

		if !self.0.ir.is_empty() {
			writeln!(f)?;

			match self.state().err_location {
				IrErrLocation::Function(err_function_key, FunctionErrLocation::Node(err_block_key, err_node_idx))
				if err_function_key == self.get_function().own_key
				&& err_block_key == self.data().as_key()
				=> {
					for (i, node) in self.0.ir.iter().enumerate() {
						writeln!(f, "\t\t\t{}", self.child(node))?;

						if i == err_node_idx {
							writeln!(f, "\t\t\t{}", self.child(self.state().err_data.as_ref()))?;
						}
					}
				}

				_ => {
					for node in self.0.ir.iter() {
						writeln!(f, "\t\t\t{}", self.child(node))?;
					}
				}
			}

			for node in self.0.ir.iter() {
				writeln!(f, "\t\t\t{}", self.child(node))?;
			}

			write!(f, "\t\t")?;
		} else {
			write!(f, " ()")?;
		}

		write!(f, "))")
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for Keyed<'data, Block> {
	type Printer = BlockPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { BlockPrinter(self, state) }
}




pub struct FunctionPrinter<'data, 'ctx> (Keyed<'data, Function>, &'ctx PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for FunctionPrinter<'data, 'ctx> {
	type Data = Keyed<'data, Function>;

	fn data (&self) -> Keyed<'data, Function> { self.0 }
	fn state (&self) -> &'ctx PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for FunctionPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.set_function(self.data().as_key());

		write!(f, "(function")?;


		if let Some(name) = self.0.name.as_ref() {
			write!(f, " :name \"{}\"", name)?;
		} else {
			write!(f, " :id {}", self.get_function().own_index)?;
		}

		if let Some(src) = self.0.src.as_ref() {
			write!(f, " {}", self.child(src))?;
		}

		for meta_key in self.0.meta.iter() {
			write!(f, " {}", self.child(meta_key))?;
		}


		write!(f, "\n\t(params (")?;

		for (i, &param_key) in self.0.param_order.iter().enumerate() {
			let param = self.0.param_data.get(param_key).unwrap();

			if param.name.is_some() || param.src.is_some() || !param.meta.is_empty() {
				write!(f, "({}", self.child(&param.ty))?;

				if let Some(name) = param.name.as_ref() {
					write!(f, " :name \"{}\"", name)?;
				}

				if let Some(src_attr) = self.0.src.as_ref() {
					write!(f, " {}", self.child(src_attr))?;
				}

				for meta_key in self.0.meta.iter() {
					write!(f, " {}", self.child(meta_key))?;
				}

				write!(f, ")")?;
			} else {
				self.child(&param.ty).fmt(f)?;
			}

			if i < self.0.param_order.len() - 1 {
				write!(f, " ")?;
			}
		}

		write!(f, "))")?;


		write!(f, "\n\t(result ")?;

		if let Some(result) = self.0.result.as_ref() {
			self.child(result).fmt(f)?;
		} else {
			write!(f, "()")?;
		}

		write!(f, ")")?;


		write!(f, "\n\t(locals (")?;

		for (i, &local_key) in self.0.locals.keys().enumerate() {
			let local = self.0.locals.get(local_key).unwrap();

			if local.name.is_some() || local.src.is_some() || !local.meta.is_empty() {
				write!(f, "({}", self.child(&local.ty))?;

				if let Some(name) = local.name.as_ref() {
					write!(f, " :name \"{}\"", name)?;
				}

				if let Some(src_attr) = self.0.src.as_ref() {
					write!(f, " {}", self.child(src_attr))?;
				}

				for meta_key in self.0.meta.iter() {
					write!(f, " {}", self.child(meta_key))?;
				}

				write!(f, ")")?;
			} else {
				self.child(&local.ty).fmt(f)?;
			}

			if i < self.0.locals.len() - 1 {
				write!(f, " ")?;
			}
		}

		write!(f, "))")?;


		if !self.0.block_order.is_empty() {
			writeln!(f, "\n\t(body")?;

			for &block_key in self.0.block_order.iter() {
				let block = self.0.block_data.get_keyed(block_key).unwrap();

				writeln!(f, "\t\t{}", self.child(block))?;

				match self.state().err_location {
					IrErrLocation::Function(err_function_key, FunctionErrLocation::Block(err_block_key))
					if err_function_key == self.data().as_key()
					&& err_block_key == block.as_key()
					=> {
						writeln!(f, "\t\t{}", self.child(self.state().err_data.as_ref()))?;
					}

					_ => { }
				}
			}

			writeln!(f, "\t)")?;
		}

		writeln!(f, ")")?;

		match self.state().err_location {
			IrErrLocation::Function(err_function_key, FunctionErrLocation::Root)
			if err_function_key == self.data().as_key()
			=> {
				writeln!(f, "{}", self.child(self.state().err_data.as_ref()))?;
			}

			_ => { }
		}


		self.clear_function();

		Ok(())
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for Keyed<'data, Function> {
	type Printer = FunctionPrinter<'data, 'ctx>;
	fn printer (self, state: &'ctx PrinterState<'ctx>) -> Self::Printer { FunctionPrinter(self, state) }
}