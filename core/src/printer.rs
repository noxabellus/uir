use std::{fmt, writeln};

use fmt::Display;
use support::utils::index_of;

use super::{
	ir::*,
	ty::*,
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


#[derive(Debug, Clone, Copy)]
pub struct PrinterState<'ctx> {
	ctx: &'ctx Context,
	function: Option<&'ctx Function>
}

impl<'ctx> PrinterState<'ctx> {
	pub fn new (ctx: &'ctx Context) -> Self {
		Self {
			ctx,
			function: None
		}
	}

	pub fn with_function (ctx: &'ctx Context, function: &'ctx Function) -> Self {
		Self {
			ctx,
			function: Some(function)
		}
	}

	pub fn set_function (&mut self, function: &'ctx Function) -> Option<&'ctx Function> {
		self.function.replace(function)
	}

	pub fn clear_function (&mut self) -> Option<&'ctx Function> {
		self.function.take()
	}

	pub fn print<'data, P: Printable<'data, 'ctx>> (self, value: &'data P) -> P::Printer {
		value.printer(self)
	}

	pub fn print_own_function (self) -> FunctionPrinter<'ctx, 'ctx> {
		self.function.unwrap().printer(self)
	}
}


pub trait Printer<'data, 'ctx>: Display {
	type Data: ?Sized;

	fn data (&self) -> Self::Data;
	fn state (&self) -> PrinterState<'ctx>;
	fn ctx (&self) -> &'ctx Context { self.state().ctx }
	fn function (&self) -> &'ctx Function { self.state().function.as_ref().unwrap() }

	fn child<P: ?Sized + Printable<'data, 'ctx>> (&self, c: &'data P) -> P::Printer {
		c.printer(self.state())
	}
}

pub trait Printable<'data, 'ctx> {
	type Printer: Display;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer;
}




pub struct ListPrinter<'data, 'ctx, P: 'data + Printable<'data, 'ctx>> (&'data [P], PrinterState<'ctx>);
impl<'data, 'ctx, P: 'data + Printable<'data, 'ctx>> Printer<'data, 'ctx> for ListPrinter<'data, 'ctx, P> {
	type Data = &'data [P];

	fn data (&self) -> &'data [P] { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx, P: 'data + Printable<'data, 'ctx>> fmt::Display for ListPrinter<'data, 'ctx, P> {
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

impl<'data, 'ctx, P: 'data + Printable<'data, 'ctx>> Printable<'data, 'ctx> for [P] {
	type Printer = ListPrinter<'data, 'ctx, P>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { ListPrinter(self, state) }
}





pub struct DPrinter<'data, 'ctx, D: ?Sized + Display> (&'data D, PrinterState<'ctx>);
impl<'data, 'ctx, D: ?Sized + Display> Printer<'data, 'ctx> for DPrinter<'data, 'ctx, D> {
	type Data = &'data D;

	fn data (&self) -> &'data D { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx, D: ?Sized + Display> fmt::Display for DPrinter<'data, 'ctx, D> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", self.0)
	}
}

// impl<'data, 'ctx, D: 'data + Display> Printable<'data, 'ctx> for D {
// 	type Printer = DPrinter<'data, 'ctx, D>;
// 	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { DPrinter(self, state) }
// }

macro_rules! impl_dprinter {
	($($ty:ty),+ $(,)?) => {
		$(
			impl<'data, 'ctx> Printable<'data, 'ctx> for $ty {
				type Printer = DPrinter<'data, 'ctx, $ty>;
				fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { DPrinter(self, state) }
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


pub struct PairPrinter<'data, 'ctx, K: Printable<'data, 'ctx>, V: Printable<'data, 'ctx>> (&'data (K, V), PrinterState<'ctx>);
impl<'data, 'ctx, K: Printable<'data, 'ctx>, V: Printable<'data, 'ctx>> Printer<'data, 'ctx> for PairPrinter<'data, 'ctx, K, V> {
	type Data = &'data (K, V);

	fn data (&self) -> &'data (K, V) { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx, K: Printable<'data, 'ctx>, V: Printable<'data, 'ctx>> fmt::Display for PairPrinter<'data, 'ctx, K, V> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let (k,v) = self.0;
		write!(f, "({} {})", self.child(k), self.child(v))
	}
}

impl<'data, 'ctx, K: 'data + Printable<'data, 'ctx>, V: 'data + Printable<'data, 'ctx>> Printable<'data, 'ctx> for (K, V) {
	type Printer = PairPrinter<'data, 'ctx, K, V>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { PairPrinter(self, state) }
}





pub struct TyKeyPrinter<'data, 'ctx> (&'data TyKey, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for TyKeyPrinter<'data, 'ctx> {
	type Data = &'data TyKey;

	fn data (&self) -> &'data TyKey { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for TyKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if let Some(ty) = self.ctx().tys.get(*self.0) {
			write!(f, "(ty {})", self.child(ty))
		} else {
			write!(f, "(ty (INVALID {:?}))", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for TyKey {
	type Printer = TyKeyPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { TyKeyPrinter(self, state) }
}




pub struct GlobalKeyPrinter<'data, 'ctx> (&'data GlobalKey, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for GlobalKeyPrinter<'data, 'ctx> {
	type Data = &'data GlobalKey;

	fn data (&self) -> &'data GlobalKey { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for GlobalKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if let Some(glo) = self.ctx().globals.get(*self.0) {
			if let Some(name) = glo.name.as_ref() {
				write!(f, "(global \"{}\")", name)
			} else {
				write!(f, "(global {:?})", self.0)
			}
		} else {
			write!(f, "(global (INVALID {:?}))", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for GlobalKey {
	type Printer = GlobalKeyPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { GlobalKeyPrinter(self, state) }
}




pub struct FunctionKeyPrinter<'data, 'ctx> (&'data FunctionKey, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for FunctionKeyPrinter<'data, 'ctx> {
	type Data = &'data FunctionKey;

	fn data (&self) -> &'data FunctionKey { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for FunctionKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if let Some(func) = self.ctx().functions.get(*self.0) {
			if let Some(name) = func.name.as_ref() {
				write!(f, "(function \"{}\")", name)
			} else {
				write!(f, "(function {:?})", self.0)
			}
		} else {
			write!(f, "(function (INVALID {:?}))", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for FunctionKey {
	type Printer = FunctionKeyPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { FunctionKeyPrinter(self, state) }
}





pub struct BlockKeyPrinter<'data, 'ctx> (&'data BlockKey, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for BlockKeyPrinter<'data, 'ctx> {
	type Data = &'data BlockKey;

	fn data (&self) -> &'data BlockKey { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for BlockKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let func = self.function();

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

impl<'data, 'ctx> Printable<'data, 'ctx> for BlockKey {
	type Printer = BlockKeyPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { BlockKeyPrinter(self, state) }
}




pub struct ParamKeyPrinter<'data, 'ctx> (&'data ParamKey, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ParamKeyPrinter<'data, 'ctx> {
	type Data = &'data ParamKey;

	fn data (&self) -> &'data ParamKey { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for ParamKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let func = self.function();

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

impl<'data, 'ctx> Printable<'data, 'ctx> for ParamKey {
	type Printer = ParamKeyPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { ParamKeyPrinter(self, state) }
}




pub struct LocalKeyPrinter<'data, 'ctx> (&'data LocalKey, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for LocalKeyPrinter<'data, 'ctx> {
	type Data = &'data LocalKey;

	fn data (&self) -> &'data LocalKey { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for LocalKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let func = self.function();

		if let Some(local) = func.locals.get(*self.0) {
			if let Some(name) = local.name.as_ref() {
				write!(f, "(local \"{}\")", name)
			} else {
				write!(f, "(local {:?})", self.0)
			}
		} else {
			write!(f, "(local (INVALID {:?}))", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for LocalKey {
	type Printer = LocalKeyPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { LocalKeyPrinter(self, state) }
}





pub struct TyPrinter<'data, 'ctx> (&'data Ty, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for TyPrinter<'data, 'ctx> {
	type Data = &'data Ty;

	fn data (&self) -> &'data Ty { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
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
				write!(f, "struct {{ {} }}", self.child(field_tys.as_slice()))
			}

			TyData::Function { parameter_tys, result_ty } => {
				write!(f, "({})", self.child(parameter_tys.as_slice()))?;

				write!(f, " -> ")?;

				if let Some(result_ty) = result_ty {
					self.child(result_ty).fmt(f)
				} else {
					write!(f, "()")
				}
			}
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for Ty {
	type Printer = TyPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { TyPrinter(self, state) }
}





pub struct ConstantPrinter<'data, 'ctx> (&'data Constant, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ConstantPrinter<'data, 'ctx> {
	type Data = &'data Constant;

	fn data (&self) -> &'data Constant { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for ConstantPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.0 {
			Constant::Null(ty_key) => {
				write!(f, "({} null)", self.child(ty_key))
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

impl<'data, 'ctx> Printable<'data, 'ctx> for Constant {
	type Printer = ConstantPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { ConstantPrinter(self, state) }
}





pub struct ConstantAggregateDataPrinter<'data, 'ctx> (&'data ConstantAggregateData, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ConstantAggregateDataPrinter<'data, 'ctx> {
	type Data = &'data ConstantAggregateData;

	fn data (&self) -> &'data ConstantAggregateData { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for ConstantAggregateDataPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.0 {
			ConstantAggregateData::Uninitialized => { write!(f, "uninitialized") }
			ConstantAggregateData::Zeroed => { write!(f, "zeroed") }
			ConstantAggregateData::CopyFill(box_constant) => { write!(f, "(copy_fill ({}))", self.child(box_constant.as_ref())) }
			ConstantAggregateData::Indexed(indexed_elements) => { write!(f, "(indexed ({}))", self.child(indexed_elements.as_slice())) }
			ConstantAggregateData::Complete(constants) => { write!(f, "(compete ({}))", self.child(constants.as_slice())) }
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for ConstantAggregateData {
	type Printer = ConstantAggregateDataPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { ConstantAggregateDataPrinter(self, state) }
}





pub struct AggregateDataPrinter<'data, 'ctx> (&'data AggregateData, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for AggregateDataPrinter<'data, 'ctx> {
	type Data = &'data AggregateData;

	fn data (&self) -> &'data AggregateData { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for AggregateDataPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.0 {
			AggregateData::Uninitialized => { write!(f, "uninitialized") }
			AggregateData::Zeroed => { write!(f, "zeroed") }
			AggregateData::CopyFill => { write!(f, "copy_fill") }

			AggregateData::Indexed(indices) => { write!(f, "(indexed ({}))", self.child(indices.as_slice())) }

			AggregateData::Complete => { write!(f, "compete") }
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for AggregateData {
	type Printer = AggregateDataPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { AggregateDataPrinter(self, state) }
}





pub struct IrDataPrinter<'data, 'ctx> (&'data IrData, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for IrDataPrinter<'data, 'ctx> {
	type Data = &'data IrData;

	fn data (&self) -> &'data IrData { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
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
			IrData::Switch(cases) => { write!(f, "switch ({})", self.child(cases.as_slice())) }
			IrData::ComputedBranch(destinations) => { write!(f, "computed_branch ({})", self.child(destinations.as_slice())) }

			IrData::Call => { write!(f, "call") }
			IrData::Ret => { write!(f, "ret") }

			IrData::Duplicate => { write!(f, "duplicate") }
			IrData::Discard => { write!(f, "discard") }

			IrData::Unreachable => { write!(f, "unreachable") }
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for IrData {
	type Printer = IrDataPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { IrDataPrinter(self, state) }
}





pub struct IrPrinter<'data, 'ctx> (&'data Ir, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for IrPrinter<'data, 'ctx> {
	type Data = &'data Ir;

	fn data (&self) -> &'data Ir { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for IrPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "({}", self.child(&self.0.data))?;

		if let Some(name) = self.0.name.as_ref() {
			write!(f, " :name \"{}\"", name)?;
		}

		write!(f, ")")
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for Ir {
	type Printer = IrPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { IrPrinter(self, state) }
}




pub struct BlockPrinter<'data, 'ctx> (&'data Block, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for BlockPrinter<'data, 'ctx> {
	type Data = &'data Block;

	fn data (&self) -> &'data Block { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
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

impl<'data, 'ctx> Printable<'data, 'ctx> for Block {
	type Printer = BlockPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { BlockPrinter(self, state) }
}




pub struct FunctionPrinter<'data, 'ctx> (&'data Function, PrinterState<'ctx>);
impl<'data, 'ctx> Printer<'data, 'ctx> for FunctionPrinter<'data, 'ctx> {
	type Data = &'data Function;

	fn data (&self) -> &'data Function { self.0 }
	fn state (&self) -> PrinterState<'ctx> { self.1 }
}

impl<'data, 'ctx> fmt::Display for FunctionPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "(function")?;


		if let Some(name) = self.0.name.as_ref() {
			write!(f, " :name \"{}\"", name)?;
		}


		write!(f, "\n\t(params (")?;

		for (i, &param_key) in self.0.param_order.iter().enumerate() {
			let param = self.0.param_data.get(param_key).unwrap();

			if let Some(name) = param.name.as_ref() {
				write!(f, "({} :name \"{}\")", self.child(&param.ty), name)?;
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

			if let Some(name) = local.name.as_ref() {
				write!(f, "({} :name \"{}\")", self.child(&local.ty), name)?;
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
				let block = self.0.block_data.get(block_key).unwrap();

				writeln!(f, "\t\t{}", self.child(block))?;
			}

			writeln!(f, "\t)")?;
		}

		writeln!(f, ")")
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for Function {
	type Printer = FunctionPrinter<'data, 'ctx>;
	fn printer (&'data self, state: PrinterState<'ctx>) -> Self::Printer { FunctionPrinter(self, state) }
}