use std::{cell::{Ref, RefCell, RefMut}, fmt, hint::unreachable_unchecked};

use support::{
	utils::{ index_of },
	slotmap::{ Key, Keyable, Keyed, AsKey, Slotmap },
};


use crate::ir::Meta;

use super::{
	builder::{
		IrErr,
		IrErrData,
		IrErrLocation,
		FunctionErrLocation
	},
	src::SrcAttribution,
	cfg::CfgErr,
	ir::{
		GlobalKey,
		Context,
		FunctionKey,
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
		FunctionMetaKey,
		Constant,
		Function,
		Global,
		IrData,
		FunctionMeta,
		GlobalMeta,
		ParamMeta,
		LocalMeta,
		IrMeta,
	},
	ty::{
		TyKey,
		TyMetaKey,
		TyMeta,
		TyData,
		TyErr,
		Ty,
	},
};




#[derive(Debug, Clone, Copy)]
pub struct PrinterState<'c> {
	pub ctx: &'c Context,
	pub function: Option<Keyed<'c, Function>>,
	pub err_data: Option<IrErrData>,
	pub err_location: IrErrLocation,
	pub indent: usize,
}

impl<'c> PrinterState<'c> {
	pub fn new (ctx: &'c Context) -> Self {
		Self {
			ctx,
			function: None,
			err_data: None,
			err_location: IrErrLocation::None,
			indent: 0
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

	pub fn with_possible_error (mut self, error: Option<IrErr>) -> Self {
		match error {
			None => {
				self.clear_err_data();
				self.clear_err_location();

				self
			}

			Some(x) => {

				self.with_error(x)
			}
		}
	}

	pub fn with_error (mut self, IrErr { data, location }: IrErr) -> Self {
		self.set_err_data(data);
		self.set_err_location(location);

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

	pub fn print_global (&self, global: GlobalKey) -> GlobalPrinter<'c, 'c> {
		GlobalPrinter(self.ctx.globals.get_keyed(global).unwrap(), RefCell::new(*self))
	}

	pub fn print_function (&self, function: FunctionKey) -> FunctionPrinter<'c, 'c> {
		FunctionPrinter(self.ctx.functions.get_keyed(function).unwrap(), RefCell::new(*self))
	}

	pub fn print_ty (&self, ty: TyKey) -> TyPrinter<'c, 'c> {
		TyPrinter(self.ctx.tys.get_keyed(ty).unwrap(), RefCell::new(*self))
	}

	pub fn print_self (&self) -> ContextPrinter<'c> {
		ContextPrinter(RefCell::new(*self))
	}

	pub fn indent (&self) -> Indent {
		Indent(self.indent)
	}

	pub fn incr_indent (&mut self) {
		self.indent += 1;
	}

	pub fn decr_indent (&mut self) {
		self.indent -= 1;
	}
}

pub struct Indent(usize);
impl fmt::Display for Indent {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		for _ in 0..self.0 { write!(f, "\t")?; }
		Ok(())
	}
}


pub trait Printer<'data, 'ctx>: fmt::Display {
	type Data: ?Sized;

	fn data (&self) -> Self::Data;
	fn state (&self) -> Ref<'_, PrinterState<'ctx>>;
	fn state_copy (&self) -> PrinterState<'ctx> { *self.state() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>>;
	fn ctx (&self) -> &'ctx Context { &self.state().ctx }

	fn indent (&self) -> Indent { self.state().indent() }
	fn incr_indent (&self) { self.state_mut().incr_indent() }
	fn decr_indent (&self) { self.state_mut().decr_indent() }

	fn set_function (&self, function_key: FunctionKey) {
		let f = self.ctx().functions.get_keyed(function_key).unwrap();
		self.state_mut().function.replace(f);
	}

	fn clear_function (&self) {
		self.state_mut().function.take();
	}

	fn get_function (&self) -> Keyed<'ctx, Function> {
		self.state().function.unwrap()
	}

	fn child<P: Printable<'data, 'ctx>> (&self, data: P) -> P::Printer {
		P::create_printer(data, self.state_copy())
	}

	fn pair<K, V> (&self, p: &'data (K, V)) -> PairPrinter<'data, 'ctx, K, V>
	where
		&'data K: Printable<'data, 'ctx>,
		&'data V: Printable<'data, 'ctx>,
	{
		PairPrinter(p, RefCell::new(self.state_copy()))
	}

	fn list<P> (&self, l: &'data [P]) -> ListPrinter<'data, 'ctx, P>
	where &'data P: Printable<'data, 'ctx>
	{
		ListPrinter(l, RefCell::new(self.state_copy()))
	}

	fn pair_list<K, V> (&self, l: &'data [(K, V)]) -> PairListPrinter<'data, 'ctx, K, V>
	where
		&'data K: Printable<'data, 'ctx>,
		&'data V: Printable<'data, 'ctx>,
	{
		PairListPrinter(l, RefCell::new(self.state_copy()))
	}
}

pub trait Printable<'data, 'ctx> {
	type Printer: Printer<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer;
}




pub struct ListPrinter<'data, 'ctx, P: 'data> (&'data [P], RefCell<PrinterState<'ctx>>)
where &'data P: Printable<'data, 'ctx>;

impl<'data, 'ctx, P: 'data> Printer<'data, 'ctx> for ListPrinter<'data, 'ctx, P>
where &'data P: Printable<'data, 'ctx>
{
	type Data = &'data [P];

	fn data (&self) -> &'data [P] { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx, P: 'data> fmt::Display for ListPrinter<'data, 'ctx, P>
where &'data P: Printable<'data, 'ctx>,
{
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if !self.0.is_empty() {
			writeln!(f)?;
			self.incr_indent();

			for e in self.0.iter() {
				writeln!(f, "{}{}", self.indent(), self.child::<&'data P>(e))?;
			}

			self.decr_indent();
			write!(f, "{}", self.indent())?;
		} else {
			write!(f, "()")?;
		}

		Ok(())
	}
}

// impl<'data, 'ctx, P: 'data> Printable<'data, 'ctx> for &'data [P]
// where &'data P: Printable<'data, 'ctx>
// {
// 	type Printer = ListPrinter<'data, 'ctx, P>;
// 	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { ListPrinter::<'data,'ctx>(data, RefCell::new(state)) }
// }


pub struct PairListPrinter<'data, 'ctx, K, V> (&'data [(K, V)], RefCell<PrinterState<'ctx>>)
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
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx, K, V> fmt::Display for PairListPrinter<'data, 'ctx, K, V>
where
	&'data K: Printable<'data, 'ctx>,
	&'data V: Printable<'data, 'ctx>,
{
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.incr_indent();

		for (k, v) in self.0.iter() {
			writeln!(f, "{}({} {})", self.indent(), self.child(k), self.child(v))?;
		}

		self.decr_indent();

		Ok(())
	}
}





pub struct DPrinter<'data, 'ctx, D: ?Sized + fmt::Display> (&'data D, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx, D: ?Sized + fmt::Display> Printer<'data, 'ctx> for DPrinter<'data, 'ctx, D> {
	type Data = &'data D;

	fn data (&self) -> &'data D { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx, D: ?Sized + fmt::Display> fmt::Display for DPrinter<'data, 'ctx, D> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", self.0)
	}
}

// impl<'data, 'ctx, D: 'data + fmt::Display> Printable<'data, 'ctx> for D {
// 	type Printer = DPrinter<'data, 'ctx, D>;

//

// 	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { Self::eate_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { Self::::Printer(data, RefCell::new(state)) ) }
// }

macro_rules! impl_dprinter {
	($($ty:ty),+ $(,)?) => {
		$(
			impl<'data, 'ctx> Printable<'data, 'ctx> for &'data $ty {
				type Printer = DPrinter<'data, 'ctx, $ty>;
				fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { DPrinter::<'data, 'ctx, $ty>(data, RefCell::new(state)) }
			}
		)+
	};
}


impl_dprinter! {
	u8, u16, u32, u64, u128, usize,
	i8, i16, i32, i64, i128, isize,
	f32, f64,
	str,
}


pub struct PairPrinter<'data, 'ctx, K: 'data, V: 'data> (&'data (K, V), RefCell<PrinterState<'ctx>>)
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
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx, K: 'data, V: 'data> fmt::Display for PairPrinter<'data, 'ctx, K, V>
where
	&'data K: Printable<'data, 'ctx>,
	&'data V: Printable<'data, 'ctx>,
{
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let (k, v) = self.0;
		write!(f, "({} {})", self.child(k), self.child(v))
	}
}






pub struct TyKeyPrinter<'data, 'ctx> (&'data TyKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for TyKeyPrinter<'data, 'ctx> {
	type Data = &'data TyKey;

	fn data (&self) -> &'data TyKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for TyKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if let Some(ty) = self.ctx().tys.get(*self.0) {
			if let Some(intrinsic) = ty.get_pure_intrinsic_name() {
				return write!(f, "(ty {})", intrinsic)
			}

			if let Some(name) = ty.name.as_ref() {
				write!(f, "(ty \"{}\")", name)
			} else if let Some(idx) = self.ctx().tys.get_index(*self.0) {
				write!(f, "(ty {})", idx)
			} else {
				// SAFETY: if we can get the value we can get the index
				unsafe { unreachable_unchecked() }
			}
		} else {
			write!(f, "(ty (INVALID {:?}))", self.0)
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data TyKey {
	type Printer = TyKeyPrinter<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { TyKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}




pub struct GlobalKeyPrinter<'data, 'ctx> (&'data GlobalKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for GlobalKeyPrinter<'data, 'ctx> {
	type Data = &'data GlobalKey;

	fn data (&self) -> &'data GlobalKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for GlobalKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if let Some(glo) = self.ctx().globals.get(*self.data()) {
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { GlobalKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}




pub struct FunctionKeyPrinter<'data, 'ctx> (&'data FunctionKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for FunctionKeyPrinter<'data, 'ctx> {
	type Data = &'data FunctionKey;

	fn data (&self) -> &'data FunctionKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for FunctionKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if let Some(func) = self.ctx().functions.get(*self.0) {
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { FunctionKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}





pub struct BlockKeyPrinter<'data, 'ctx> (&'data BlockKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for BlockKeyPrinter<'data, 'ctx> {
	type Data = &'data BlockKey;

	fn data (&self) -> &'data BlockKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { BlockKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}




pub struct ParamKeyPrinter<'data, 'ctx> (&'data ParamKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ParamKeyPrinter<'data, 'ctx> {
	type Data = &'data ParamKey;

	fn data (&self) -> &'data ParamKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { ParamKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}




pub struct LocalKeyPrinter<'data, 'ctx> (&'data LocalKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for LocalKeyPrinter<'data, 'ctx> {
	type Data = &'data LocalKey;

	fn data (&self) -> &'data LocalKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for LocalKeyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		let func = self.get_function();

		if let Some(local) = func.locals.get(*self.0) {
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { LocalKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}



pub struct SrcAttributionPrinter<'data, 'ctx> (&'data SrcAttribution, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for SrcAttributionPrinter<'data, 'ctx> {
	type Data = &'data SrcAttribution;

	fn data (&self) -> &'data SrcAttribution { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for SrcAttributionPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, ":src (", )?;

		if let Some(src) = self.ctx().srcs.get(self.0.key) {
			write!(f, "{}", src.path.display())?;
		} else if let Some(idx) = self.ctx().srcs.get_index(self.0.key) {
			write!(f, "{}", idx)?;
		} else {
			write!(f, "(INVALID {:?})", self.0.key)?;
		}

		if let Some(range) = self.0.range {
			if let Some(src) = self.ctx().srcs.get(self.0.key) {
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { SrcAttributionPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}



pub struct ParamMetaKeyPrinter<'data, 'ctx> (&'data ParamMetaKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ParamMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data ParamMetaKey;

	fn data (&self) -> &'data ParamMetaKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { ParamMetaKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}



pub struct LocalMetaKeyPrinter<'data, 'ctx> (&'data LocalMetaKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for LocalMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data LocalMetaKey;

	fn data (&self) -> &'data LocalMetaKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { LocalMetaKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}



pub struct IrMetaKeyPrinter<'data, 'ctx> (&'data IrMetaKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for IrMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data IrMetaKey;

	fn data (&self) -> &'data IrMetaKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { IrMetaKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}



pub struct TyMetaKeyPrinter<'data, 'ctx> (&'data TyMetaKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for TyMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data TyMetaKey;

	fn data (&self) -> &'data TyMetaKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { TyMetaKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}



pub struct FunctionMetaKeyPrinter<'data, 'ctx> (&'data FunctionMetaKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for FunctionMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data FunctionMetaKey;

	fn data (&self) -> &'data FunctionMetaKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { FunctionMetaKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}



pub struct GlobalMetaKeyPrinter<'data, 'ctx> (&'data GlobalMetaKey, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for GlobalMetaKeyPrinter<'data, 'ctx> {
	type Data = &'data GlobalMetaKey;

	fn data (&self) -> &'data GlobalMetaKey { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { GlobalMetaKeyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}





pub struct TyPrinter<'data, 'ctx> (Keyed<'data, Ty>, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for TyPrinter<'data, 'ctx> {
	type Data = Keyed<'data, Ty>;

	fn data (&self) -> Keyed<'data, Ty> { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for TyPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "(ty")?;

		write!(f, " :id {}", self.ctx().tys.get_index(self.0.as_key()).unwrap())?;

		if let Some(intrinsic) = self.0.get_pure_intrinsic_name() {
			return write!(f, " ({}))", intrinsic)
		}

		if let Some(name) = self.0.name.as_ref() {
			write!(f, " :name \"{}\"", name)?;
		}

		if let Some(src_attr) = self.0.src.as_ref() {
			write!(f, " {}", self.child(src_attr))?;
		}

		for meta in self.0.meta.iter() {
			write!(f, " :#{}", self.child(meta))?;
		}

		write!(f, " ")?;

		match &self.0.data {
			TyData::Void => { write!(f, "(void)")?; }
			TyData::Block => { write!(f, "(block)")?; }
			TyData::Primitive(primitive_ty) => { write!(f, "({})", primitive_ty)?; }
			TyData::Pointer { target_ty } => { write!(f, "(pointer {})", self.child(target_ty))?; }
			TyData::Array { length, element_ty } => { write!(f, "(array {} {})", length, self.child(element_ty))?; }
			TyData::Vector { length, element_ty, .. } => { write!(f, "(vector {} {})", length, self.child(element_ty))?; }

			TyData::Structure { field_tys } => {
				write!(f, "(struct {})", self.list(field_tys.as_slice()))?;
			}

			TyData::Function { parameter_tys, result_ty } => {
				writeln!(f, "(function")?;
				self.incr_indent();


				writeln!(f, "{}(params {})", self.indent(), self.list(parameter_tys.as_slice()))?;


				write!(f, "{}(result ", self.indent())?;

				if let Some(result_ty) = result_ty {
					self.child(result_ty).fmt(f)?;
				} else {
					write!(f, "(")?;
				}
				write!(f, ")")?;



				writeln!(f)?;
				self.decr_indent();
				write!(f, "{})", self.indent())?;
			}
		}

		write!(f, ")")?;


		if matches!(self.state().err_location, IrErrLocation::Ty(key) if key == self.0.as_key()) {
			writeln!(f, "\n{}", self.child(self.state().err_data))?;
		}

		Ok(())
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for Keyed<'data, Ty> {
	type Printer = TyPrinter<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { TyPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}





pub struct ConstantPrinter<'data, 'ctx> (&'data Constant, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ConstantPrinter<'data, 'ctx> {
	type Data = &'data Constant;

	fn data (&self) -> &'data Constant { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { ConstantPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}





pub struct ConstantAggregateDataPrinter<'data, 'ctx> (&'data ConstantAggregateData, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for ConstantAggregateDataPrinter<'data, 'ctx> {
	type Data = &'data ConstantAggregateData;

	fn data (&self) -> &'data ConstantAggregateData { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for ConstantAggregateDataPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.0 {
			ConstantAggregateData::Uninitialized => { write!(f, "uninitialized") }
			ConstantAggregateData::Zeroed => { write!(f, "zeroed") }
			ConstantAggregateData::CopyFill(box_constant) => { write!(f, "(copy_fill ({}))", self.child(box_constant.as_ref())) }
			ConstantAggregateData::Indexed(indexed_elements) => { write!(f, "(indexed ({}))", self.pair_list(indexed_elements.as_slice())) }
			ConstantAggregateData::Complete(constants) => { write!(f, "(complete ({}))", self.list(constants.as_slice())) }
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data ConstantAggregateData {
	type Printer = ConstantAggregateDataPrinter<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { ConstantAggregateDataPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}





pub struct AggregateDataPrinter<'data, 'ctx> (&'data AggregateData, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for AggregateDataPrinter<'data, 'ctx> {
	type Data = &'data AggregateData;

	fn data (&self) -> &'data AggregateData { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for AggregateDataPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.0 {
			AggregateData::Uninitialized => { write!(f, "uninitialized") }
			AggregateData::Zeroed => { write!(f, "zeroed") }
			AggregateData::CopyFill => { write!(f, "copy_fill") }

			AggregateData::Indexed(indices) => { write!(f, "(indexed ({}))", self.list(indices.as_slice())) }

			AggregateData::Complete => { write!(f, "complete") }
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data AggregateData {
	type Printer = AggregateDataPrinter<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { AggregateDataPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}





pub struct IrDataPrinter<'data, 'ctx> (&'data IrData, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for IrDataPrinter<'data, 'ctx> {
	type Data = &'data IrData;

	fn data (&self) -> &'data IrData { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for IrDataPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.0 {
			IrData::Constant(constant) => { write!(f, "constant {}", self.child(constant)) }

			IrData::BuildAggregate(ty_key, aggregate_data) => { write!(f, "build_aggregate {} {}", self.child(ty_key), self.child(aggregate_data)) }
			IrData::SetElement(idx) => { write!(f, "set_element {}", self.child(idx)) }
			IrData::GetElement(idx) => { write!(f, "get_element {}", self.child(idx)) }

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
			IrData::Switch(cases, default) => { write!(f, "switch (cases: {} default: {})", self.pair_list(cases.as_slice()), self.child(default)) }
			IrData::ComputedBranch(destinations) => { write!(f, "computed_branch ({})", self.list(destinations.as_slice())) }

			IrData::Call => { write!(f, "call") }
			IrData::Ret => { write!(f, "ret") }

			IrData::Duplicate(idx) => { write!(f, "duplicate {}", self.child(idx)) }
			IrData::Discard(idx) => { write!(f, "discard {}", self.child(idx)) }
			IrData::Swap(idx) => { write!(f, "swap {}", self.child(idx)) }

			IrData::Unreachable => { write!(f, "unreachable") }
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data IrData {
	type Printer = IrDataPrinter<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { IrDataPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}



pub struct IrPrinter<'data, 'ctx> (&'data Ir, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for IrPrinter<'data, 'ctx> {
	type Data = &'data Ir;

	fn data (&self) -> &'data Ir { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
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
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { IrPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}



pub struct PossibleErrorPrinter<'ctx> (Option<IrErrData>, RefCell<PrinterState<'ctx>>);
impl<'ctx> Printer<'_, 'ctx> for PossibleErrorPrinter<'ctx> {
	type Data = Option<IrErrData>;

	fn data (&self) -> Option<IrErrData> { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'ctx> fmt::Display for PossibleErrorPrinter<'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "^ Error")?;

		if let Some(err_data) = self.data() {
			write!(f, ": {}", self.child(err_data))?;
		}

		Ok(())
	}
}

impl<'ctx> Printable<'_, 'ctx> for Option<IrErrData> {
	type Printer = PossibleErrorPrinter<'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { PossibleErrorPrinter::<'ctx>(data, RefCell::new(state)) }
}




pub struct IrErrorPrinter<'ctx> (IrErrData, RefCell<PrinterState<'ctx>>);
impl<'ctx> Printer<'_, 'ctx> for IrErrorPrinter<'ctx> {
	type Data = IrErrData;

	fn data (&self) -> IrErrData { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'ctx> fmt::Display for IrErrorPrinter<'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match &self.data() {
			IrErrData::EmptyBlock(block_key) => { write!(f, "Block {} contains no instructions", self.child(block_key)) }
			IrErrData::InvalidParamKey(param_key) => { write!(f, "Invalid param key {}", self.child(param_key)) }
			IrErrData::InvalidParamIndex(param_idx) => { write!(f, "Invalid param index {}", param_idx) }
			IrErrData::InvalidLocalKey(local_key) => { write!(f, "Invalid local key {}", self.child(local_key)) }
			IrErrData::InvalidBlockKey(block_key) => { write!(f, "Invalid block key {}", self.child(block_key)) }
			IrErrData::InvalidBlockIndex(block_idx) => { write!(f, "Invalid block index {}", block_idx) }
			IrErrData::InvalidTyKey(ty_key) => { write!(f, "Invalid type key {}", self.child(ty_key)) }
			IrErrData::InvalidGlobalKey(global_key) => { write!(f, "Invalid global key {}", self.child(global_key)) }
			IrErrData::InvalidFunctionKey(function_key) => { write!(f, "Invalid function key {}", self.child(function_key)) }
			IrErrData::InvalidNodeIndex(node_idx) => { write!(f, "Invalid node index {}", node_idx) }
			IrErrData::CfgErr(cfg_err) => { write!(f, "{}", self.child(cfg_err)) }
			IrErrData::TyErr(ty_err) => { write!(f, "{}", self.child(ty_err)) }
		}
	}
}

impl<'ctx> Printable<'_, 'ctx> for IrErrData {
	type Printer = IrErrorPrinter<'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { IrErrorPrinter::<'ctx>(data, RefCell::new(state)) }
}


pub struct CfgErrorPrinter<'data, 'ctx> (&'data CfgErr, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for CfgErrorPrinter<'data, 'ctx> {
	type Data = &'data CfgErr;

	fn data (&self) -> &'data CfgErr { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for CfgErrorPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.data() {
			CfgErr::ExistingOutEdge(from, to) => { write!(f, "Duplicate out edge from {} to {}", self.child(from), self.child(to)) }
			CfgErr::ExistingInEdge(from, to) => { write!(f, "Duplicate in edge from {} to {}", self.child(from), self.child(to)) }
			CfgErr::InvalidEdge(from, to) => { write!(f, "Invalid edge from {} to {}", self.child(from), self.child(to)) }
			CfgErr::MissingOutEdge(block_key) => { write!(f, "Missing edge to {}", self.child(block_key)) }
			CfgErr::MissingInEdge(block_key) => { write!(f, "Missing edge from {}", self.child(block_key)) }

			CfgErr::PhiNotAtTop => { write!(f, "Phi nodes must be placed before other instruction types")}
			CfgErr::NodeAfterTerminator => { write!(f, "Cannot have instructions following a terminator node") }
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data CfgErr {
	type Printer = CfgErrorPrinter<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { CfgErrorPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}




pub struct TyErrPrinter<'data, 'ctx> (&'data TyErr, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for TyErrPrinter<'data, 'ctx> {
	type Data = &'data TyErr;

	fn data (&self) -> &'data TyErr { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for TyErrPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self.data() {
			TyErr::StackUnderflow => { write!(f, "Stack underflow") }
			TyErr::ExpectedConstant => { write!(f, "Expected a constant value") }
			TyErr::GepNoIndices => { write!(f, "Gep instruction has no indices") }
			TyErr::TypeHasNoNull(ty_key) => { write!(f, "Type {} cannot have a null (zero) value", self.child(ty_key)) }
			TyErr::PhiMissingInPredecessor(block_key) => { write!(f, "Phi node has no corresponding value in predecessor {}", self.child(block_key)) }
			TyErr::PhiTypeMismatch(block_key, expected_ty, found_ty) => { write!(f, "Phi node has type {} but the value in predecessor {} has type {}", self.child(expected_ty), self.child(block_key), self.child(found_ty)) }
			TyErr::PhiNoPredecessors(block_key) => { write!(f, "Phi node in block {} with no predecessors", self.child(block_key)) }
			TyErr::UnusedValues(block_key, num_unused) => { write!(f, "Block {} has {} value(s) remaining on the stack with no corresponding phi nodes in successors", self.child(block_key), num_unused) }
			TyErr::UnusedValuesNoSuccessor(block_key, num_unused) => { write!(f, "Block {} has {} value(s) remaining on the stack with no successors", self.child(block_key), num_unused) }
			TyErr::GepTargetNotPointer(ty_key) => { write!(f, "Target of gep instruction is not of pointer type but {}", self.child(ty_key)) }
			TyErr::GepInvalidSubElement(elem_idx, ty_key) => { write!(f, "Subtarget of gep instruction at element {} is not an aggregate but {}", elem_idx, self.child(ty_key)) }
			TyErr::GepImplicitLoad(elem_idx, ty_key) => { write!(f, "Subtarget of gep instruction at element {} requires an implicit load because it is of pointer type {}", elem_idx, self.child(ty_key)) }
			TyErr::GepInvalidIndex(elem_idx, ty_key) => { write!(f, "Gep instruction element {} index is not an integer but {}", elem_idx, self.child(ty_key)) }
			TyErr::GepOutOfBounds(elem_idx, ty_key, len, idx) => { write!(f, "Gep instruction element {} constant index {} is out of bounds 0 <-> {} for subtarget type {}", elem_idx, idx, len, self.child(ty_key)) }
			TyErr::ExpectedTy(expected_ty, found_ty) => { write!(f, "Expected type {}, but found {}", self.child(expected_ty), self.child(found_ty)) }
			TyErr::ExpectedArray(ty_key) => { write!(f, "Value is not an array but {}", self.child(ty_key)) }
			TyErr::ExpectedVector(ty_key) => { write!(f, "Value is not an vector but {}", self.child(ty_key)) }
			TyErr::ExpectedStructure(ty_key) => { write!(f, "Value is not a struct but {}", self.child(ty_key)) }
			TyErr::ExpectedEmptyStructure(ty_key) => { write!(f, "Expected structure type {} to have no fields", self.child(ty_key)) }
			TyErr::ExpectedFunction(ty_key) => { write!(f, "Value is not a function but {}", self.child(ty_key)) }
			TyErr::ExpectedBlock(ty_key) => { write!(f, "Value is not a block reference but {}", self.child(ty_key)) }
			TyErr::ExpectedPointer(ty_key) => { write!(f, "Value is not a pointer but {}", self.child(ty_key)) }
			TyErr::ExpectedAggregateTy(ty_key) => { write!(f, "Value is not an aggregate but {}", self.child(ty_key)) }
			TyErr::ExpectedInteger(ty_key) => { write!(f, "Value is not an integer but {}", self.child(ty_key)) }
			TyErr::InvalidSwitchTy(ty_key) => { write!(f, "Values of type {} cannot be switched on", self.child(ty_key)) }
			TyErr::DuplicateAggregateIndex(loc_a, loc_b, idx) => { write!(f, "Aggregate initialization contains multiple entries for the same index {}, at {} and {}", idx, loc_a, loc_b) }
			TyErr::InvalidAggregateIndex(ty_key, idx) => { write!(f, "Aggregate of type {} has no index {}", self.child(ty_key), idx) }
			TyErr::MissingAggregateElement(ty_key, idx) => { write!(f, "Aggregate initialization of type {} is missing element for index {}", self.child(ty_key), idx) }
			TyErr::ExpectedAggregateElementTy(ty_key, idx, expected_ty, found_ty) => { write!(f, "Aggregate initialization of type {} has invalid type for index {}: expected {}, but found {}", self.child(ty_key), idx, self.child(expected_ty), self.child(found_ty)) }
			TyErr::BinaryOpTypeMismatch(left_ty, right_ty) => { write!(f, "Binary operator has mismatched operand types: left is {}, but right is {}", self.child(left_ty), self.child(right_ty)) }
			TyErr::BinaryOpInvalidOperandTy(op, operand_ty) => { write!(f, "Binary operator {} has no meaning for operand ty {}", op, self.child(operand_ty)) }
			TyErr::UnaryOpInvalidOperandTy(op, operand_ty) => { write!(f, "Unary operator {} has no meaning for operand ty {}", op, self.child(operand_ty)) }
			TyErr::InvalidCast(op, from_ty, to_ty) => { write!(f, "Cannot perform cast {} from {} to {}", op, self.child(from_ty), self.child(to_ty)) }
			TyErr::InfiniteRecursive(ty_key) => { write!(f, "Type contains infinitely recursive structure with reference to {}", self.child(ty_key)) }
		}
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data TyErr {
	type Printer = TyErrPrinter<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { TyErrPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}




pub struct BlockPrinter<'data, 'ctx> (Keyed<'data, Block>, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for BlockPrinter<'data, 'ctx> {
	type Data = Keyed<'data, Block>;

	fn data (&self) -> Keyed<'data, Block> { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
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
			self.incr_indent();

			match self.state().err_location {
				IrErrLocation::Function(err_function_key, FunctionErrLocation::Node(err_block_key, err_node_idx))
				if err_function_key == self.get_function().as_key()
				&& err_block_key == self.data().as_key()
				=> {
					for (i, node) in self.0.ir.iter().enumerate() {
						writeln!(f, "{}{}", self.indent(), self.child(node))?;

						if i == err_node_idx {
							writeln!(f, "{}{}", self.indent(), self.child(self.state().err_data))?;
						}
					}
				}

				_ => {
					for node in self.0.ir.iter() {
						writeln!(f, "{}{}", self.indent(), self.child(node))?;
					}
				}
			}

			self.decr_indent();
			write!(f, "{}", self.indent())?;
		} else {
			write!(f, " ()")?;
		}

		write!(f, "))")
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for Keyed<'data, Block> {
	type Printer = BlockPrinter<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { BlockPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}




pub struct FunctionPrinter<'data, 'ctx> (Keyed<'data, Function>, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for FunctionPrinter<'data, 'ctx> {
	type Data = Keyed<'data, Function>;

	fn data (&self) -> Keyed<'data, Function> { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for FunctionPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.set_function(self.data().as_key());

		write!(f, "(function")?;

		write!(f, " :id {}", self.ctx().functions.get_index(self.0.as_key()).unwrap())?;

		if let Some(name) = self.0.name.as_ref() {
			write!(f, " :name \"{}\"", name)?;
		}

		if let Some(src) = self.0.src.as_ref() {
			write!(f, " {}", self.child(src))?;
		}

		for meta_key in self.0.meta.iter() {
			write!(f, " {}", self.child(meta_key))?;
		}

		writeln!(f)?;
		self.incr_indent();


		if !self.0.param_order.is_empty() {
			writeln!(f, "{}(params", self.indent())?;
			self.incr_indent();

			for (i, &param_key) in self.0.param_order.iter().enumerate() {
				let param = self.0.param_data.get(param_key).unwrap();

				if param.name.is_some() || param.src.is_some() || !param.meta.is_empty() {
					write!(f, "{}({}", self.indent(), self.child(&param.ty))?;

					if let Some(name) = param.name.as_ref() {
						write!(f, " :name \"{}\"", name)?;
					}

					if let Some(src_attr) = self.0.src.as_ref() {
						write!(f, " {}", self.child(src_attr))?;
					}

					for meta_key in self.0.meta.iter() {
						write!(f, " {}", self.child(meta_key))?;
					}

					writeln!(f, ")")?;
				} else {
					writeln!(f, "{}{}", self.indent(), self.child(&param.ty))?;
				}

				if i < self.0.param_order.len() - 1 {
					write!(f, " ")?;
				}
			}

			self.decr_indent();
			writeln!(f, "{})", self.indent())?;
		}


		write!(f, "{}(result ", self.indent())?;

		if let Some(result) = self.0.result.as_ref() {
			self.child(result).fmt(f)?;
		} else {
			write!(f, "()")?;
		}

		writeln!(f, ")")?;



		if !self.0.locals.is_empty() {
			writeln!(f, "{}(locals", self.indent())?;
			self.incr_indent();

			for (i, &local_key) in self.0.locals.keys().enumerate() {
				let local = self.0.locals.get(local_key).unwrap();

				if local.name.is_some() || local.src.is_some() || !local.meta.is_empty() {
					write!(f, "{}({}", self.indent(), self.child(&local.ty))?;

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

			self.decr_indent();
			writeln!(f, "{})", self.indent())?;
		}


		if !self.0.block_order.is_empty() {
			writeln!(f, "{}(body", self.indent())?;
			self.incr_indent();

			for &block_key in self.0.block_order.iter() {
				let block = self.0.block_data.get_keyed(block_key).unwrap();

				writeln!(f, "\t\t{}", self.child(block))?;

				match self.state().err_location {
					IrErrLocation::Function(err_function_key, FunctionErrLocation::Block(err_block_key))
					if err_function_key == self.data().as_key()
					&& err_block_key == block.as_key()
					=> {
						writeln!(f, "\t\t{}", self.child(self.state().err_data))?;
					}

					_ => { }
				}
			}

			self.decr_indent();
			writeln!(f, "{})", self.indent())?;
		}


		self.decr_indent();
		writeln!(f, "{})", self.indent())?;

		if matches!(self.state().err_location,
			IrErrLocation::Function(err_function_key, FunctionErrLocation::Root)
			if err_function_key == self.data().as_key()
	 	) {
			writeln!(f, "{}{}", self.indent(), self.child(self.state().err_data))?;
		}


		self.clear_function();

		Ok(())
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for Keyed<'data, Function> {
	type Printer = FunctionPrinter<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { FunctionPrinter(data, RefCell::new(state)) }
}





pub struct GlobalPrinter<'data, 'ctx> (Keyed<'data, Global>, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for GlobalPrinter<'data, 'ctx> {
	type Data = Keyed<'data, Global>;

	fn data (&self) -> Keyed<'data, Global> { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for GlobalPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "(global")?;

		write!(f, " :id {}", self.ctx().globals.get_index(self.0.as_key()).unwrap())?;

		if let Some(name) = self.0.name.as_ref() {
			write!(f, " :name \"{}\"", name)?;
		}

		if let Some(src) = self.0.src.as_ref() {
			write!(f, " {}", self.child(src))?;
		}

		for meta_key in self.0.meta.iter() {
			write!(f, " {}", self.child(meta_key))?;
		}


		write!(f, " (init ")?;

		if let Some(init) = self.0.init.as_ref() {
			write!(f, "{}", self.child(init))?;
		} else {
			write!(f, "()")?;
		}

		write!(f, "))")?;

		if matches!(self.state().err_location, IrErrLocation::Global(key) if key == self.0.as_key()) {
			writeln!(f, "\n{}", self.child(self.state().err_data))?;
		}


		Ok(())
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for Keyed<'data, Global> {
	type Printer = GlobalPrinter<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { GlobalPrinter(data, RefCell::new(state)) }
}



macro_rules! meta_printers {
	($($tyname:ident($field:ident)),+ $(,)?) => { $(
		support::paste! {
			pub struct [<$tyname Printer>]<'data, 'ctx> (Keyed<'data, $tyname>, RefCell<PrinterState<'ctx>>);
			impl<'data, 'ctx> Printer<'data, 'ctx> for [<$tyname Printer>]<'data, 'ctx> {
				type Data = Keyed<'data, $tyname>;

				fn data (&self) -> Keyed<'data, $tyname> { self.0 }
				fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
				fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
			}

			impl<'data, 'ctx> fmt::Display for [<$tyname Printer>]<'data, 'ctx> {
				fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
					writeln!(f, "{}(:#{} {})", self.indent(), self.ctx().meta.$field.get_index(self.0.as_key()).unwrap(), self.0.into_ref())
				}
			}

			impl<'data, 'ctx> Printable<'data, 'ctx> for Keyed<'data, $tyname> {
				type Printer = [<$tyname Printer>]<'data, 'ctx>;
				fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { [< $tyname Printer >]::<'data, 'ctx>(data, RefCell::new(state)) }
			}
		}
	)+ };
}

meta_printers! {
	TyMeta(ty),
	FunctionMeta(function),
	GlobalMeta(global),
	ParamMeta(param),
	LocalMeta(local),
	IrMeta(ir),
}



pub struct SlotmapPrinter<'data, 'ctx, K: 'data + Key, V: 'data + Keyable<Key = K>> (&'data Slotmap<K, V>, RefCell<PrinterState<'ctx>>)
where
	Keyed<'data, V>: Printable<'data,'ctx>,
;

impl<'data, 'ctx, K: 'data + Key, V: 'data + Keyable<Key = K>> Printer<'data, 'ctx> for SlotmapPrinter<'data, 'ctx, K, V>
where
	Keyed<'data, V>: Printable<'data,'ctx>,
{
	type Data = &'data Slotmap<K, V>;

	fn data (&self) -> Self::Data { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx, K: 'data + Key, V: 'data + Keyable<Key = K>> fmt::Display for SlotmapPrinter<'data, 'ctx, K, V>
where
	Keyed<'data, V>: Printable<'data,'ctx>,
{
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if !self.0.is_empty() {
			writeln!(f)?;
			self.incr_indent();

			for (&key, value) in self.0.iter() {
				writeln!(f, "{}{}", self.indent(), self.child(Keyed::new(key, value)))?;
			}

			self.decr_indent();
			write!(f, "{}", self.indent())?;
		} else {
			write!(f, "()")?;
		}

		Ok(())
	}
}






pub struct MetaPrinter<'data, 'ctx> (&'data Meta, RefCell<PrinterState<'ctx>>);
impl<'data, 'ctx> Printer<'data, 'ctx> for MetaPrinter<'data, 'ctx> {
	type Data = &'data Meta;

	fn data (&self) -> &'data Meta { self.0 }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.1.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.1.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for MetaPrinter<'data, 'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		writeln!(f, "(meta ")?;

		self.incr_indent();

		if !self.0.ty.is_empty() { writeln!(f, "{}(ty {})", self.indent(), SlotmapPrinter(&self.0.ty, RefCell::new(self.state_copy())))?; }
		if !self.0.function.is_empty() { writeln!(f, "{}(function {})", self.indent(), SlotmapPrinter(&self.0.function, RefCell::new(self.state_copy())))?; }
		if !self.0.param.is_empty() { writeln!(f, "{}(param {})", self.indent(), SlotmapPrinter(&self.0.param, RefCell::new(self.state_copy())))?; }
		if !self.0.local.is_empty() { writeln!(f, "{}(local {})", self.indent(), SlotmapPrinter(&self.0.local, RefCell::new(self.state_copy())))?; }
		if !self.0.global.is_empty() { writeln!(f, "{}(global {})", self.indent(), SlotmapPrinter(&self.0.global, RefCell::new(self.state_copy())))?; }
		if !self.0.ir.is_empty() { writeln!(f, "{}(ir {})", self.indent(), SlotmapPrinter(&self.0.ir, RefCell::new(self.state_copy())))?; }

		self.decr_indent();
		write!(f, "{})", self.indent())
	}
}

impl<'data, 'ctx> Printable<'data, 'ctx> for &'data Meta {
	type Printer = MetaPrinter<'data, 'ctx>;
	fn create_printer (data: Self, state: PrinterState<'ctx>) -> Self::Printer { MetaPrinter::<'data, 'ctx>(data, RefCell::new(state)) }
}


pub struct ContextPrinter<'ctx> (RefCell<PrinterState<'ctx>>);
impl<'ctx> Printer<'ctx, 'ctx> for ContextPrinter<'ctx> {
	type Data = &'ctx Context;

	fn data (&self) -> &'ctx Context { self.state().ctx }
	fn state (&self) -> Ref<'_, PrinterState<'ctx>> { self.0.borrow() }
	fn state_mut (&self) -> RefMut<'_, PrinterState<'ctx>> { self.0.borrow_mut() }
}

impl<'data, 'ctx> fmt::Display for ContextPrinter<'ctx> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if matches!(self.state().err_location, IrErrLocation::None) {
			if let Some(err_data) = self.state().err_data {
				writeln!(f, "Error: {}", self.child(err_data))?;
			}
		}
		if !self.data().tys.is_empty() { writeln!(f, "{}(types {})", self.indent(), SlotmapPrinter(&self.data().tys, RefCell::new(self.state_copy())))?; }
		if !self.data().globals.is_empty() { writeln!(f, "{}(globals {})", self.indent(), SlotmapPrinter(&self.data().globals, RefCell::new(self.state_copy())))?; }
		if !self.data().functions.is_empty() { writeln!(f, "{}(functions {})", self.indent(), SlotmapPrinter(&self.data().functions, RefCell::new(self.state_copy())))?; }
		if !self.data().meta.is_empty() { writeln!(f, "{}{}", self.indent(), self.child(&self.data().meta))?; }
		Ok(())
	}
}

impl<'ctx> Printable<'ctx, 'ctx> for &'ctx Context {
	type Printer = ContextPrinter<'ctx>;
	fn create_printer (_: Self, state: PrinterState<'ctx>) -> Self::Printer { ContextPrinter::<'ctx>(RefCell::new(state)) }
}