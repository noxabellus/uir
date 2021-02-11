use std::{cell::Ref, ops::{self, Deref}};

use support::{slotmap::{AsKey, Keyed, KeyedMut}};

use crate::cfg_generator;

use super::{
	src::*,
	ty::*,
	ir::*,
	cfg::*,
	ty_checker::{ self, * },
};


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IrErr {
	NoActiveBlock,
	InvalidParamKey(ParamKey),
	InvalidParamIndex(usize),
	InvalidLocalKey(LocalKey),
	ExpectedAggregateTy(TyKey),
	InvalidAggregateIndex(TyKey, u64),
	InvalidBlockKey(BlockKey),
	InvalidBlockIndex(usize),
	InvalidTyKey(TyKey),
	InvalidGlobalKey(GlobalKey),
	InvalidFunctionKey(FunctionKey),
	InvalidNodeIndex(usize),
	CfgErr(CfgErr),
	TyErr(TyErr),
	NodeAfterTerminator(BlockKey, usize),
	FunctionAlreadyDefined(FunctionKey),
}

impl From<CfgErr> for IrErr {
	fn from (e: CfgErr) -> IrErr { IrErr::CfgErr(e) }
}

impl From<TyErr> for IrErr {
	fn from (e: TyErr) -> IrErr { IrErr::TyErr(e) }
}

impl From<TyCkErr> for IrErr {
	fn from (e: TyCkErr) -> IrErr {
		match e {
			TyCkErr::TyErr(e) => e.into(),
			TyCkErr::IrErr(e) => e
		}
	}
}

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

	pub fn set_init (mut self, constant: Constant) -> Self {
		self.init = Some(constant);
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
	ctx: &'c mut Context,
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


	pub fn pointer_ty<K: AsKey<TyKey>> (&mut self, target_ty: K) -> IrResult<TyManipulator> {
		let target_ty = self.get_ty(target_ty)?.as_key();

		Ok(TyManipulator(self.ctx.add_ty(TyData::Pointer { target_ty }.into())))
	}

	pub fn array_ty<K: AsKey<TyKey>> (&mut self, length: u64, element_ty: K) -> IrResult<TyManipulator> {
		let element_ty = self.get_ty(element_ty)?.as_key();

		Ok(TyManipulator(self.ctx.add_ty(TyData::Array { length, element_ty }.into())))
	}

	pub fn structure_ty (&mut self, field_tys: Vec<TyKey>) -> IrResult<TyManipulator> {
		for &ft in field_tys.iter() {
			self.get_ty(ft)?;
		}

		Ok(TyManipulator(self.ctx.add_ty(TyData::Structure { field_tys }.into())))
	}

	pub fn function_ty (&mut self, parameter_tys: Vec<TyKey>, result_ty: Option<TyKey>) -> IrResult<TyManipulator> {
		for &pt in parameter_tys.iter() {
			self.get_ty(pt)?;
		}

		if let Some(rt) = result_ty {
			self.get_ty(rt)?;
		}

		Ok(TyManipulator(self.ctx.add_ty(TyData::Function { parameter_tys, result_ty}.into())))
	}



	pub fn get_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<Keyed<Ty>> {
		let ty_key = ty_key.as_key();

		self.ctx.tys.get_keyed(ty_key).ok_or(IrErr::InvalidTyKey(ty_key))
	}

	pub fn get_ty_mut<K: AsKey<TyKey>> (&mut self, ty_key: K) -> IrResult<KeyedMut<Ty>> {
		let ty_key = ty_key.as_key();

		self.ctx.tys.get_keyed_mut(ty_key).ok_or(IrErr::InvalidTyKey(ty_key))
	}


	pub fn get_finalized_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<Keyed<Ty>> {
		let ty_key = ty_key.as_key();

		self.finalize_ty(ty_key)?;
		self.get_ty(ty_key)
	}

	pub fn get_finalized_ty_mut<K: AsKey<TyKey>> (&mut self, ty_key: K) -> IrResult<KeyedMut<Ty>> {
		let ty_key = ty_key.as_key();

		self.finalize_ty(ty_key)?;
		self.get_ty_mut(ty_key)
	}


	pub fn get_global<K: AsKey<GlobalKey>> (&self, global_key: K) -> IrResult<Keyed<Global>> {
		let global_key = global_key.as_key();

		self.ctx.globals.get_keyed(global_key).ok_or(IrErr::InvalidGlobalKey(global_key))
	}

	pub fn get_global_mut<K: AsKey<GlobalKey>> (&mut self, global_key: K) -> IrResult<GlobalManipulator> {
		let global_key = global_key.as_key();

		self.ctx.globals.get_keyed_mut(global_key).ok_or(IrErr::InvalidGlobalKey(global_key)).map(GlobalManipulator)
	}


	pub fn get_function<K: AsKey<FunctionKey>> (&self, function_key: K) -> IrResult<Keyed<Function>> {
		let function_key = function_key.as_key();

		self.ctx.functions.get_keyed(function_key).ok_or(IrErr::InvalidFunctionKey(function_key))
	}

	pub fn get_function_mut<K: AsKey<FunctionKey>> (&mut self, function_key: K) -> IrResult<KeyedMut<Function>> {
		let function_key = function_key.as_key();

		self.ctx.functions.get_keyed_mut(function_key).ok_or(IrErr::InvalidFunctionKey(function_key))
	}



	pub fn finalize_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<Ref<Layout>> {
		use TyData::*;

		let ty_key = ty_key.as_key();

		let ty = self.get_ty(ty_key)?;

		if ty.layout.borrow().is_none() {
			let layout = match &ty.data {
				Void => Layout::custom_scalar(0, 1),

				&Primitive(prim) => self.ctx.target.get_primitive_layout(prim),

				Block | &Pointer { .. } | &Function { .. } => self.ctx.target.get_pointer_layout(),

				&Array { length, element_ty } => {
					let layout_ref = self.finalize_ty(element_ty)?;
					let Layout { size: elem_size, align: elem_align, .. } = layout_ref.deref();
					Layout::custom_scalar(length * *elem_size, *elem_align)
				},

				Structure { field_tys } => {
					let field_tys = field_tys.clone().into_iter();
					let mut size = 0;
					let mut align = 0;

					let mut field_offsets = vec![];

					for field_ty_key in field_tys {
						let layout_ref = self.finalize_ty(field_ty_key)?;
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

			self.ctx.tys.get(ty_key).unwrap().layout.borrow_mut().replace(layout);
		}

		let base = self.ctx.tys.get(ty_key).unwrap().layout.borrow();

		Ok(Ref::map(base, |opt| opt.as_ref().unwrap()))
	}

	pub fn size_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<u64> {
		Ok(self.finalize_ty(ty_key)?.size)
	}

	pub fn align_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<u64> {
		Ok(self.finalize_ty(ty_key)?.align)
	}

	pub fn field_offsets_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<Ref<[u64]>> {
		let ty_key = ty_key.as_key();

		if self.get_ty(ty_key)?.is_structure() {
			Ok(Ref::map(self.finalize_ty(ty_key)?, |l| l.field_offsets.as_slice()))
		} else {
			Err(TyErr::ExpectedStructure(ty_key.as_key()).into())
		}
	}
}













#[derive(Debug)]
pub struct FunctionBuilder<'b> {
	builder: &'b mut Builder<'b>,

	function_key: FunctionKey,
	function: Function,

	active_block: Option<BlockKey>,
	insertion_cursor: InsertionCursor,
	active_src: Option<SrcAttribution>,
}



impl<'b> FunctionBuilder<'b> {
	pub fn new (builder: &'b mut Builder<'b>) -> Self {
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




	pub fn finalize (mut self) -> IrResult<KeyedMut<'b, Function>> {
		self.clear_active_block();

		let ty = self.generate_own_ty()?.as_key();

		let builder = self.builder;
		let mut function = self.function;
		let function_key = self.function_key;

		builder.ctx.functions
			.define(
				self.function_key,
				Function {
					ty,
					name: function.name.clone(),
					.. Function::default()
				}
			)
			.ok_or(IrErr::FunctionAlreadyDefined(function_key))?;

		let cfg = cfg_generator::generate(&function)?;
		let cfg = ty_checker::check(builder, cfg, &function)?;

		function.cfg = cfg;

		let mut slot = builder.get_function_mut(function_key)?;

		*slot = function;

		Ok(slot)
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



	pub fn generate_own_ty (&mut self) -> IrResult<TyManipulator> {
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

	pub fn pointer_ty<K: AsKey<TyKey>> (&mut self, target_ty: K) -> IrResult<TyManipulator> { self.builder.pointer_ty(target_ty) }
	pub fn array_ty<K: AsKey<TyKey>> (&mut self, length: u64, element_ty: K) -> IrResult<TyManipulator> { self.builder.array_ty(length, element_ty) }
	pub fn structure_ty (&mut self, field_tys: Vec<TyKey>) -> IrResult<TyManipulator> { self.builder.structure_ty(field_tys) }
	pub fn function_ty (&mut self, parameter_tys: Vec<TyKey>, result_ty: Option<TyKey>) -> IrResult<TyManipulator> { self.builder.function_ty(parameter_tys, result_ty) }

	pub fn get_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<Keyed<Ty>> { self.builder.get_ty(ty_key) }
	pub fn get_ty_mut<K: AsKey<TyKey>> (&mut self, ty_key: K) -> IrResult<KeyedMut<Ty>> { self.builder.get_ty_mut(ty_key) }

	pub fn get_global<K: AsKey<GlobalKey>> (&self, global_key: K) -> IrResult<Keyed<Global>> { self.builder.get_global(global_key) }
	pub fn get_global_mut<K: AsKey<GlobalKey>> (&mut self, global_key: K) -> IrResult<GlobalManipulator> { self.builder.get_global_mut(global_key) }

	pub fn get_function<K: AsKey<FunctionKey>> (&self, function_key: K) -> IrResult<Keyed<Function>> {
		let function_key = function_key.as_key();

		if function_key == self.function_key {
			return Ok(Keyed { key: function_key, value: &self.function })
		}

		self.builder.get_function(function_key)
	}

	pub fn get_function_mut<K: AsKey<FunctionKey>> (&mut self, function_key: K) -> IrResult<KeyedMut<Function>> {
		let function_key = function_key.as_key();

		if function_key == self.function_key {
			return Ok(KeyedMut { key: function_key, value: &mut self.function })
		}

		self.builder.get_function_mut(function_key)
	}

	pub fn finalize_ty<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<Ref<Layout>> { self.builder.finalize_ty(ty_key) }

	pub fn size_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<u64> { self.builder.size_of(ty_key) }
	pub fn align_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<u64> { self.builder.align_of(ty_key) }
	pub fn field_offsets_of<K: AsKey<TyKey>> (&self, ty_key: K) -> IrResult<Ref<[u64]>> { self.builder.field_offsets_of(ty_key) }



	pub fn make_local<K: AsKey<TyKey>> (&mut self, ty_key: K) -> LocalManipulator {
		let ty = ty_key.as_key();

		LocalManipulator(self.function.locals.insert(Local { ty, .. Local::default() }))
	}

	pub fn get_local<K: AsKey<LocalKey>> (&self, local_key: K) -> IrResult<Keyed<Local>> {
		let local_key = local_key.as_key();

		self.function.locals.get_keyed(local_key).ok_or(IrErr::InvalidLocalKey(local_key))
	}

	pub fn get_local_mut<K: AsKey<LocalKey>> (&mut self, local_key: K) -> IrResult<LocalManipulator> {
		let local_key = local_key.as_key();

		self.function.locals.get_keyed_mut(local_key).ok_or(IrErr::InvalidLocalKey(local_key)).map(LocalManipulator)
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


	pub fn get_param_index<K: AsKey<ParamKey>> (&self, param_key: K) -> IrResult<usize> {
		let param_key = param_key.as_key();

		self.function.param_order
			.iter()
			.enumerate()
			.find(|&(_, &pk)| pk == param_key)
			.map(|(i, _)| i)
			.ok_or(IrErr::InvalidParamKey(param_key))
	}

	pub fn get_param<K: AsKey<ParamKey>> (&self, param_key: K) -> IrResult<Keyed<Param>> {
		let param_key = param_key.as_key();

		self.function.param_data.get_keyed(param_key).ok_or(IrErr::InvalidParamKey(param_key))
	}

	pub fn get_param_mut<K: AsKey<ParamKey>> (&mut self, param_key: K) -> IrResult<ParamManipulator> {
		let param_key = param_key.as_key();

		self.function.param_data.get_keyed_mut(param_key).ok_or(IrErr::InvalidParamKey(param_key)).map(ParamManipulator)
	}




	pub fn append_block (&mut self, block: Block) -> BlockManipulator {
		let block = self.function.block_data.insert(block);
		self.function.block_order.push(block.as_key());
		BlockManipulator(block)
	}

	pub fn insert_block (&mut self, idx: usize, block: Block) -> IrResult<BlockManipulator> {
		if idx > self.function.block_order.len() { return Err(IrErr::InvalidBlockIndex(idx)) }

		let block = self.function.block_data.insert(block);

		self.function.block_order.insert(idx, block.as_key());

		Ok(BlockManipulator(block))
	}

	pub fn append_new_block (&mut self) -> BlockManipulator {
		self.append_block(Block::default())
	}

	pub fn insert_new_block (&mut self, idx: usize) -> IrResult<BlockManipulator> {
		self.insert_block(idx, Block::default())
	}

	pub fn remove_block<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrResult<Block> {
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


	pub fn move_block_to_start<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrResult {
		let block_key = block_key.as_key();

		let idx = self.get_block_index(block_key)?;

		self.function.block_order.remove(idx);
		self.function.block_order.insert(0, block_key);

		Ok(())
	}

	pub fn move_block_to_end<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrResult {
		let block_key = block_key.as_key();

		let idx = self.get_block_index(block_key)?;

		self.function.block_order.remove(idx);
		self.function.block_order.push(block_key);

		Ok(())
	}

	pub fn move_block_before<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, block_to_move: KA, destination_block: KB) -> IrResult {
		let block_to_move = block_to_move.as_key();
		let destination_block = destination_block.as_key();

		let idx_to_move = self.get_block_index(block_to_move)?;
		let destination_idx = self.get_block_index(destination_block)?;

		self.function.block_order.remove(idx_to_move);
		self.function.block_order.insert(destination_idx, block_to_move);

		Ok(())
	}

	pub fn move_block_after<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, block_to_move: KA, destination_block: KB) -> IrResult {
		let block_to_move = block_to_move.as_key();
		let destination_block = destination_block.as_key();

		let idx_to_move = self.get_block_index(block_to_move)?;
		let destination_idx = self.get_block_index(destination_block)?;

		self.function.block_order.remove(idx_to_move);
		self.function.block_order.insert(destination_idx + 1, block_to_move);

		Ok(())
	}

	pub fn swap_blocks<KA: AsKey<BlockKey>, KB: AsKey<BlockKey>> (&mut self, a: KA, b: KB) -> IrResult {
		let a = self.get_block_index(a)?;
		let b = self.get_block_index(b)?;

		self.function.block_order.swap(a, b);

		Ok(())
	}


	pub fn get_block_index<K: AsKey<BlockKey>> (&self, block_key: K) -> IrResult<usize> {
		let block_key = block_key.as_key();

		self.function.block_order
			.iter()
			.enumerate()
			.find(|&(_, &br)| br == block_key)
			.map(|(i, _)| i)
			.ok_or(IrErr::InvalidBlockKey(block_key))
	}

	pub fn get_block<K: AsKey<BlockKey>> (&self, block_key: K) -> IrResult<Keyed<Block>> {
		let block_key = block_key.as_key();
		self.function.block_data.get_keyed(block_key).ok_or(IrErr::InvalidBlockKey(block_key))
	}

	pub fn get_block_mut<K: AsKey<BlockKey>> (&mut self, block_key: K) -> IrResult<BlockManipulator> {
		let block_key = block_key.as_key();
		self.function.block_data.get_keyed_mut(block_key).ok_or(IrErr::InvalidBlockKey(block_key)).map(BlockManipulator)
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


	pub fn get_node (&self, idx: usize) -> IrResult<&Ir> {
		self.get_active_block().into_ref().ir.get(idx).ok_or(IrErr::InvalidNodeIndex(idx))
	}

	pub fn get_node_mut (&mut self, idx: usize) -> IrResult<IrManipulator> {
		self.get_active_block_mut().into_mut().ir.get_mut(idx).ok_or(IrErr::InvalidNodeIndex(idx)).map(IrManipulator)
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

	pub fn global_key<K: AsKey<GlobalKey>> (&mut self, key: K) -> IrManipulator {
		let key = key.as_key();

		self.write_node(IrData::GlobalKey(key))
	}

	pub fn function_key<K: AsKey<FunctionKey>> (&mut self, key: K) -> IrManipulator {
		let key = key.as_key();

		self.write_node(IrData::FunctionKey(key))
	}

	pub fn block_key<K: AsKey<BlockKey>> (&mut self, key: K) -> IrManipulator {
		let key = key.as_key();

		self.write_node(IrData::BlockKey(key))
	}

	pub fn param_key<K: AsKey<ParamKey>> (&mut self, key: K) -> IrManipulator {
		let key = key.as_key();

		self.write_node(IrData::ParamKey(key))
	}

	pub fn local_key<K: AsKey<LocalKey>> (&mut self, key: K) -> IrManipulator {
		let key = key.as_key();

		self.write_node(IrData::LocalKey(key))
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


	pub fn gep (&mut self, num_indices: u64) -> IrManipulator {
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

	pub fn switch (&mut self, case_blocks: Vec<(Constant, BlockKey)>) -> IrManipulator {
		self.write_node(IrData::Switch(case_blocks))
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


	pub fn duplicate (&mut self) -> IrManipulator {
		self.write_node(IrData::Duplicate)
	}

	pub fn discard (&mut self) -> IrManipulator {
		self.write_node(IrData::Discard)
	}


	pub fn unreachable (&mut self) -> IrManipulator {
		self.write_node(IrData::Unreachable)
	}
}