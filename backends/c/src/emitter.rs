#![allow(unused_variables)]

use std::borrow::Borrow;
#[allow(unused_imports)]
use {
	std::{
		cell::{Ref, RefCell, RefMut},
		collections::HashMap,
		fmt::{self, Write},
		io, ops,
		rc::{Rc, Weak},
	},
	uir_core::{
		block,
		with_block,
		builder::*,
		ir::*,
		support::slotmap::{AsKey, Key},
		ty::*,
	},
};

#[derive(Clone, Default)]
pub struct CString(Vec<u8>);

impl fmt::Display for CString {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", unsafe {
			std::str::from_utf8_unchecked(self.0.as_slice())
		})
	}
}

impl fmt::Display for CStr {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", unsafe { std::str::from_utf8_unchecked(&self.0) })
	}
}

impl CString {
	pub fn new() -> Self {
		Self::default()
	}

	pub fn ensure_ascii_non_null(s: &[u8]) -> bool {
		s.iter().find(|&&x| x == 0 || x > 128).is_none()
	}

	pub fn as_cstr(&self) -> &CStr {
		unsafe { &*(self.0.as_slice() as *const _ as *const _) }
	}

	pub fn write_cstr(&mut self, cstr: impl ToCStr) {
		self.write_str(cstr.to_cstr().as_str()).unwrap()
	}

	pub fn insert(&mut self, index: usize, value: u8) {
		self.0.insert(index, value)
	}

	pub fn concat(mut self, mut other: CString) -> Self {
		self.0.append(&mut other.0);
		self
	}
}

impl fmt::Write for CString {
	fn write_str(&mut self, s: &str) -> fmt::Result {
		self.0.extend_from_slice(s.to_cstr().as_bytes());
		Ok(())
	}
}

impl From<&String> for CString {
	fn from(s: &String) -> CString {
		assert!(CString::ensure_ascii_non_null(s.as_bytes()));
		CString(s.as_bytes().to_owned())
	}
}

impl From<String> for CString {
	fn from(s: String) -> CString {
		assert!(CString::ensure_ascii_non_null(s.as_bytes()));
		CString(s.into_bytes())
	}
}

impl<'a> From<&'a [u8]> for CString {
	fn from(s: &'a [u8]) -> CString {
		assert!(CString::ensure_ascii_non_null(s));
		CString(s.to_vec())
	}
}

impl<'a> From<&'a CStr> for CString {
	fn from(s: &'a CStr) -> CString {
		CString(s.as_bytes().to_vec())
	}
}

impl<'a> From<&'a str> for CString {
	fn from(s: &'a str) -> CString {
		assert!(CString::ensure_ascii_non_null(s.as_bytes()));
		CString(s.as_bytes().to_vec())
	}
}

impl From<CString> for String {
	fn from(c: CString) -> String {
		unsafe { String::from_utf8_unchecked(c.0) }
	}
}

impl ops::Deref for CString {
	type Target = CStr;
	fn deref(&self) -> &Self::Target {
		self.as_cstr()
	}
}

pub trait ToCString {
	fn to_cstring(&self) -> CString;
}
impl<T> ToCString for T
where
	T: ToString,
{
	fn to_cstring(&self) -> CString {
		self.to_string().into()
	}
}

pub trait ToCStr {
	fn to_cstr(&self) -> &CStr;
}

impl ToCStr for CString {
	fn to_cstr(&self) -> &CStr {
		self.as_cstr()
	}
}

impl ToCStr for &CString {
	fn to_cstr(&self) -> &CStr {
		self.as_cstr()
	}
}

impl ToCStr for CStr {
	fn to_cstr(&self) -> &CStr {
		self
	}
}

impl ToCStr for &CStr {
	fn to_cstr(&self) -> &CStr {
		self
	}
}

impl ToCStr for String {
	fn to_cstr(&self) -> &CStr {
		self.as_str().to_cstr()
	}
}

impl<'s> ToCStr for &String {
	fn to_cstr(&self) -> &CStr {
		CStr::from_str(self)
	}
}

impl<'s> ToCStr for str {
	fn to_cstr(&self) -> &CStr {
		CStr::from_str(self)
	}
}

impl<'s> ToCStr for &str {
	fn to_cstr(&self) -> &CStr {
		CStr::from_str(self)
	}
}

impl<'s> ToCStr for [u8] {
	fn to_cstr(&self) -> &CStr {
		CStr::from_bytes(self)
	}
}

impl<'s> ToCStr for &[u8] {
	fn to_cstr(&self) -> &CStr {
		CStr::from_bytes(self)
	}
}

pub struct CStr([u8]);
impl CStr {
	#[allow(clippy::should_implement_trait)]
	pub fn from_str(s: &str) -> &CStr {
		s.into()
	}
	/// # Safety
	/// See `CString::ensure_ascii_non_null`
	pub unsafe fn from_str_unchecked(s: &str) -> &CStr {
		&*(s as *const _ as *const _)
	}

	pub fn from_bytes(s: &[u8]) -> &CStr {
		s.into()
	}
	/// # Safety
	/// See `CString::ensure_ascii_non_null`
	pub unsafe fn from_bytes_unchecked(s: &[u8]) -> &CStr {
		&*(s as *const _ as *const _)
	}

	pub fn as_str(&self) -> &str {
		self.into()
	}
	pub fn as_bytes(&self) -> &[u8] {
		self.into()
	}
}

impl<'a> From<&'a str> for &'a CStr {
	fn from(s: &'a str) -> &'a CStr {
		assert!(CString::ensure_ascii_non_null(s.as_bytes()));
		unsafe { &*(s as *const _ as *const _) }
	}
}

impl<'a> From<&'a [u8]> for &'a CStr {
	fn from(s: &'a [u8]) -> &'a CStr {
		assert!(CString::ensure_ascii_non_null(s));
		unsafe { &*(s as *const _ as *const _) }
	}
}

impl<'a> From<&'a CStr> for &'a str {
	fn from(s: &'a CStr) -> &'a str {
		unsafe { &*(s as *const _ as *const _) }
	}
}

impl<'a> From<&'a CStr> for &'a [u8] {
	fn from(s: &'a CStr) -> &'a [u8] {
		unsafe { &*(s as *const _ as *const _) }
	}
}

#[macro_export]
macro_rules! c_str {
	($expr:expr) => {
		CStr::from_str($expr)
	};
}

#[derive(Clone)]
pub struct CData {
	pub body: CString,
	pub name: CString,
}
impl CData {
	pub fn new(body: CString, name: CString) -> CData {
		Self { body, name }
	}
}

#[macro_export]
macro_rules! cformat {
	($( $tt:tt )*) => { format!($( $tt )*).to_cstring() };
}

#[macro_export]
macro_rules! cwrite {
	($out:expr, $( $tt:tt )*) => { write!($out, $( $tt )*).unwrap() };
}

// #[derive(Default, Clone)]
// pub struct RcMut<T> (Rc<RefCell<T>>);

// impl<T> RcMut<T> {
// 	pub fn new (v: T) -> Self {
// 		Self(Rc::new(RefCell::new(v)))
// 	}

// 	pub fn borrow (&self) -> Ref<T> {
// 		self.0.borrow()
// 	}

// 	pub fn borrow_mut (&self) -> RefMut<T> {
// 		self.0.borrow_mut()
// 	}
// }

#[derive(Clone)]
pub struct CItem(Rc<CData>);

impl ops::Deref for CItem {
	type Target = CData;
	fn deref(&self) -> &CData {
		self.0.deref()
	}
}

impl CItem {
	pub fn new(body: impl Into<CString>, name: impl Into<CString>) -> Self {
		Self(Rc::new(CData::new(body.into(), name.into())))
	}
}

pub trait Interner: FnMut(&Context, &mut CString) + 'static {}
impl<F> Interner for F where F: FnMut(&Context, &mut CString) + 'static {}

pub trait Mangler: FnMut(&Context, &Ty, &mut CString) + 'static {}
impl<F> Mangler for F where F: FnMut(&Context, &Ty, &mut CString) + 'static {}

pub struct Emitter<'c> {
	pub ctx: &'c Context,
	pub state: EmitterState,
	pub type_body_out: Option<CString>,
	pub name_interner: Box<dyn Interner>,
	pub name_mangler: Box<dyn Mangler>,
}

#[derive(Default)]
pub struct EmitterState {
	pub types: HashMap<TyKey, CItem>,
	pub global_decls: HashMap<GlobalKey, CItem>,
	pub global_defs: HashMap<GlobalKey, CItem>,
	pub function_decls: HashMap<FunctionKey, CItem>,
	pub function_defs: HashMap<FunctionKey, CItem>,
}

impl<'c> Emitter<'c> {
	pub fn new(ctx: &'c Context, name_interner: impl Interner, name_mangler: impl Mangler) -> Self {
		Self {
			ctx,
			state: EmitterState::default(),
			type_body_out: None,
			name_interner: Box::new(name_interner) as Box<dyn Interner>,
			name_mangler: Box::new(name_mangler) as Box<dyn Mangler>,
		}
	}

	pub fn create_interned_name(&mut self, name: impl ToCString) -> CString {
		let mut name = name.to_cstring();
		self.intern_name(&mut name);
		name
	}

	pub fn create_mangled_name(&mut self, ty: &Ty, name: impl ToCString) -> CString {
		let mut name = name.to_cstring();
		self.mangle_name(ty, &mut name);
		name
	}

	pub fn intern_name(&mut self, name: &mut CString) {
		(self.name_interner)(self.ctx, name);
	}

	pub fn mangle_name(&mut self, ty: &Ty, name: &mut CString) {
		(self.name_mangler)(self.ctx, ty, name);
	}

	pub fn create_anon_id(&self, key: impl Key) -> impl fmt::Display {
		key.as_integer()
	}

	pub fn apply_given_prefix(prefix: &[u8], name: &mut CString) {
		for (i, &ch) in prefix.iter().enumerate() {
			name.insert(i, ch);
		}
	}

	pub fn create_sanitized_name(&mut self, name: impl ToCString) -> CString {
		let mut name = name.to_cstring();
		self.sanitize_name(&mut name);
		name
	}

	pub fn sanitize_name(&mut self, name: &mut CString) {
		const RESERVED_NAMES: &[&[u8]] = &[
			b"void",
			b"signed",
			b"unsigned",
			b"char",
			b"int",
			b"short",
			b"long",
			b"for",
			b"while",
			b"do",
			b"switch",
			b"static",
			b"inline",
			b"restricted",
			b"volatile",
			b"const",
			b"typedef",
			b"struct",
			b"union",
		];

		for &s in RESERVED_NAMES.iter() {
			if name.as_bytes() == s {
				Self::apply_given_prefix(b"user_", name);
				self.intern_name(name);
			}
		}
	}

	pub fn emit_constant(&mut self, constant: &Constant) -> (TyKey, CString) {
		match constant {
			&Constant::Null(ty_key) => (ty_key, cformat!("(({}) NULL)", self.emit_ty(ty_key).name)),

			Constant::Bool(bool) => (
				self.ctx.ty_dict.bool,
				cformat!(
					"(({}) {})",
					self.emit_primitive_ty(PrimitiveTy::Bool),
					(if *bool { 1 } else { 0 })
				),
			),

			Constant::SInt8(i8) => (
				self.ctx.ty_dict.sint8,
				cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::SInt8), i8),
			),

			Constant::SInt16(i16) => (
				self.ctx.ty_dict.sint16,
				cformat!(
					"(({}) {})",
					self.emit_primitive_ty(PrimitiveTy::SInt16),
					i16
				),
			),

			Constant::SInt32(i32) => (
				self.ctx.ty_dict.sint32,
				cformat!(
					"(({}) {})",
					self.emit_primitive_ty(PrimitiveTy::SInt32),
					i32
				),
			),

			Constant::SInt64(i64) => (
				self.ctx.ty_dict.sint64,
				cformat!(
					"(({}) {})",
					self.emit_primitive_ty(PrimitiveTy::SInt64),
					i64
				),
			),

			Constant::SInt128(i128) => (
				self.ctx.ty_dict.sint128,
				cformat!(
					"(({}) {})",
					self.emit_primitive_ty(PrimitiveTy::SInt128),
					i128
				),
			),

			Constant::UInt8(u8) => (
				self.ctx.ty_dict.uint8,
				cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::UInt8), u8),
			),

			Constant::UInt16(u16) => (
				self.ctx.ty_dict.uint16,
				cformat!(
					"(({}) {})",
					self.emit_primitive_ty(PrimitiveTy::UInt16),
					u16
				),
			),

			Constant::UInt32(u32) => (
				self.ctx.ty_dict.uint32,
				cformat!(
					"(({}) {})",
					self.emit_primitive_ty(PrimitiveTy::UInt32),
					u32
				),
			),

			Constant::UInt64(u64) => (
				self.ctx.ty_dict.uint64,
				cformat!(
					"(({}) {})",
					self.emit_primitive_ty(PrimitiveTy::UInt64),
					u64
				),
			),

			Constant::UInt128(u128) => (
				self.ctx.ty_dict.uint128,
				cformat!(
					"(({}) {})",
					self.emit_primitive_ty(PrimitiveTy::UInt128),
					u128
				),
			),

			Constant::Real32(f32) => (
				self.ctx.ty_dict.real32,
				cformat!(
					"(({}) {})",
					self.emit_primitive_ty(PrimitiveTy::Real32),
					f32
				),
			),

			Constant::Real64(f64) => (
				self.ctx.ty_dict.real64,
				cformat!(
					"(({}) {})",
					self.emit_primitive_ty(PrimitiveTy::Real64),
					f64
				),
			),

			&Constant::Aggregate(ty_key, ref agg_data) => {
				let ty = self.ctx.tys.get(ty_key).unwrap();
				let cty = self.emit_ty(ty_key);

				let mut body = cformat!("(({}) {{ ", cty.name);

				use ConstantAggregateData::*;
				match agg_data {
					Zeroed => {}

					CopyFill(elem) => {
						let (elem_ty_key, elem) = self.emit_constant(elem);
						let elem_ty = self.ctx.tys.get(elem_ty_key).unwrap();

						match &ty.data {
							TyData::Structure { field_tys } => {
								for (i, &field_ty) in field_tys.iter().enumerate() {
									self.emit_ty(field_ty);

									let field_ty = self.ctx.tys.get(field_ty).unwrap();
									assert!(field_ty.equivalent(elem_ty));

									cwrite!(body, "{}", elem);

									if i != field_tys.len() - 1 {
										cwrite!(body, ", ")
									}
								}
							}

							&TyData::Array { length, element_ty }
							| &TyData::Vector { length, element_ty } => {
								let element_ty = self.ctx.tys.get(element_ty).unwrap();
								assert!(element_ty.equivalent(elem_ty));

								for i in 0..length {
									cwrite!(body, "{}", elem);

									if i != length - 1 {
										cwrite!(body, ", ")
									}
								}
							}

							_ => unreachable!(),
						}
					}

					Indexed(indexed_vals) => {
						todo!()
					}

					Complete(vals) => {
						todo!()
					}

					Uninitialized => unreachable!(
						"uninitialized values should be handled at a higher emitter level"
					),
				}

				cwrite!(body, " }})");

				(ty_key, body)
			}
		}
	}

	pub fn emit_primitive_ty(&self, prim: PrimitiveTy) -> &'static CStr {
		c_str!(match prim {
			PrimitiveTy::Bool => "char",
			PrimitiveTy::SInt8 => "signed char",
			PrimitiveTy::SInt16 => "signed short",
			PrimitiveTy::SInt32 => "signed int",
			PrimitiveTy::SInt64 => "signed long",
			PrimitiveTy::SInt128 => "signed __int128",
			PrimitiveTy::UInt8 => "unsigned char",
			PrimitiveTy::UInt16 => "unsigned short",
			PrimitiveTy::UInt32 => "unsigned int",
			PrimitiveTy::UInt64 => "unsigned long",
			PrimitiveTy::UInt128 => "unsigned __int128",
			PrimitiveTy::Real32 => "float",
			PrimitiveTy::Real64 => "double",
		})
	}

	pub fn emit_ty(&mut self, ty_key: TyKey) -> CItem {
		if let Some(existing) = self.state.types.get(&ty_key) {
			return existing.clone();
		}

		let ty = self.ctx.tys.get(ty_key).unwrap();

		let user_name = ty
			.name
			.as_ref()
			.map(|name| self.emit_item_name(ty_key, ty, "ty", Some(name)));

		macro_rules! name {
			($def:expr) => { {
			 user_name.unwrap_or_else(|| $def)
			} };
		}

		let (body, name) = match &ty.data {
			TyData::Void => {
				let name = name!(self.create_interned_name("void"));
				(cformat!("typedef void {}", name), name)
			}

			TyData::Block => {
				let name = name!(self.create_interned_name("block_address"));
				(cformat!("typedef void* {}", name), name)
			}

			TyData::Primitive(prim) => {
				let def = self.emit_primitive_ty(*prim);
				let name = name!(prim.as_str().into());
				(cformat!("typedef {} {}", def, name), name)
			}

			TyData::Pointer { target_ty } => {
				let ctarget = self.emit_ty(*target_ty);

				let name = name!(self.create_interned_name(cformat!("ptr_{}", ctarget.name)));
				(cformat!("typedef {}* {}", ctarget.name, name), name)
			}

			TyData::Array { length, element_ty } => {
				let celem = self.emit_ty(*element_ty);

				let def = cformat!("struct {{ {}[{}] data; }}", celem.name, length);
				let name =
					name!(self.create_interned_name(cformat!("arr_{}_x_{}", celem.name, length)));

				(cformat!("typedef {} {}", def, name), name)
			}

			TyData::Vector { length, element_ty } => {
				let celem = self.emit_ty(*element_ty);

				let mut def = CString::from("struct { ");
				for i in 0..*length {
					cwrite!(def, "{} e{}; ", celem.name, i);
				}
				cwrite!(def, "}}");

				let name =
					name!(self.create_interned_name(cformat!("vec_{}_x_{}", celem.name, length)));

				(cformat!("typedef {} {}", def, name), name)
			}

			TyData::Structure { field_tys } => {
				let mut def = CString::from("struct {");
				for (i, &field_ty) in field_tys.iter().enumerate() {
					let cfield = self.emit_ty(field_ty);

					cwrite!(def, "\t{} f{};\n", cfield.name, i);
				}

				cwrite!(def, "}}");

				let name = name!(self
					.create_interned_name(cformat!("anon_struct{}", self.create_anon_id(ty_key))));

				(cformat!("typedef {} {}", def, name), name)
			}

			TyData::Function {
				parameter_tys,
				result_ty,
			} => {
				let mut def = CString::from("typedef ");

				let cresult = result_ty
					.map(|x| self.emit_ty(x).name.clone())
					.unwrap_or_else(|| "void".into());
				def.write_cstr(cresult);

				let name = name!(
					self.create_interned_name(cformat!("fn_ty{}", self.create_anon_id(ty_key)))
				);
				cwrite!(def, " (*{}) (", name);

				for (i, &param_ty) in parameter_tys.iter().enumerate() {
					let cparam = self.emit_ty(param_ty);

					def.write_cstr(&cparam.name);

					if i != parameter_tys.len() - 1 {
						def.write_cstr(", ");
					}
				}
				cwrite!(def, ")");

				(def, name)
			}
		};

		if let Some(type_body_out) = self.type_body_out.as_mut() {
			cwrite!(type_body_out, "{};\n", body);
		}

		let item = CItem::new(body, name);
		self.state.types.insert(ty_key, item.clone());
		item
	}

	pub fn emit_item_name(
		&mut self,
		key: impl Key,
		ty: &Ty,
		kind: &str,
		internal_name: Option<impl Into<CString>>,
	) -> CString {
		internal_name
			.map(Into::<CString>::into)
			.map(|mut name| {
				self.mangle_name(ty, &mut name);
				self.sanitize_name(&mut name);
				name
			})
			.unwrap_or_else(|| {
				self.create_interned_name(cformat!("anon_{}{}", kind, self.create_anon_id(key)))
			})
	}

	pub fn emit_global_decl(&mut self, global_key: GlobalKey) -> CItem {
		if let Some(existing) = self.state.global_decls.get(&global_key) {
			return existing.clone()
		}

		let global = self.ctx.globals.get(global_key).unwrap();

		let ty = self.ctx.tys.get(global.ty).unwrap();
		let cty = self.emit_ty(global.ty);

		let name = self.emit_item_name(global_key, ty, "global", global.name.as_ref());

		let body = cformat!("{} {}", cty.name, name);

		let item = CItem::new(body, name);
		self.state.global_decls.insert(global_key, item.clone());
		item
	}

	pub fn emit_global (&mut self, global_key: GlobalKey) -> CItem {
		if let Some(existing) = self.state.global_defs.get(&global_key) {
			return existing.clone()
		}

		let decl = self.emit_global_decl(global_key);
		let global = self.ctx.globals.get(global_key).unwrap();
		let ty = self.ctx.tys.get(global.ty).unwrap();

		let mut body = decl.body.clone();

		if let Some((init_ty, init)) = global
			.init
			.as_ref()
			.map(|constant| self.emit_constant(constant))
		{
			assert!(ty.equivalent(self.ctx.tys.get(init_ty).unwrap()));
			cwrite!(body, " = {}", init);
		}

		let item = CItem::new(body, decl.name.clone());
		self.state.global_defs.insert(global_key, item.clone());
		item
	}

	pub fn emit_var_name(
		&mut self,
		key: impl Key,
		kind: &str,
		name: Option<impl Into<CString>>,
	) -> CString {
		name.map(Into::<CString>::into)
			.unwrap_or_else(|| cformat!("{}{}", kind, self.create_anon_id(key)))
	}

	pub fn emit_function_decl(&mut self, function_key: FunctionKey) -> CItem {
		if let Some(existing) = self.state.function_decls.get(&function_key) {
			return existing.clone();
		}

		let function = self.ctx.functions.get(function_key).unwrap();

		let ty = self.ctx.tys.get(function.ty).unwrap();
		let cty = self.emit_ty(function.ty);

		let name = self.emit_item_name(function_key, ty, "function", function.name.as_ref());

		let mut body = CString::default();

		if let Some(ret_ty) = function.result {
			let ret_cty = self.emit_ty(ret_ty);

			body.write_cstr(&ret_cty.name);
		} else {
			body.write_cstr(c_str!("void"));
		}

		cwrite!(body, " {} (", name);

		for (i, &param_key) in function.param_order.iter().enumerate() {
			let param = function.param_data.get(param_key).unwrap();

			let cty = self.emit_ty(param.ty);
			let param_name = self.emit_var_name(param_key, "param", param.name.as_ref());
			cwrite!(body, "{} {}", cty.name, param_name);

			if i < function.param_order.len() - 1 {
				cwrite!(body, ", ");
			}
		}

		cwrite!(body, ")");

		let item = CItem::new(body, name);
		self.state.function_decls.insert(function_key, item.clone());
		item
	}

	pub fn emit_function(&mut self, function_key: FunctionKey) -> CItem {
		if let Some(existing) = self.state.function_defs.get(&function_key) {
			return existing.clone()
		}

		let decl = self.emit_function_decl(function_key);

		let name = decl.name.clone();


		let function = self.ctx.functions.get(function_key).unwrap();


		let mut block_names = HashMap::<BlockKey, CString>::default();
		let mut phi_nodes = HashMap::<BlockKey, Vec<CString>>::default();

		let mut phi_segment = CString::new();
		let mut block_segment = CString::new();

		for &block_key in function.block_order.iter() {
			let block = function.block_data.get(block_key).unwrap();

			let block_name = self.emit_var_name(block_key, "block", block.name.as_ref());
			block_names.insert(block_key, block_name.clone());

			if function.cfg.has_in_values(block_key) {
				let in_vals = function.cfg.get_in_values(block_key).unwrap();

				for (i, &in_val) in in_vals.iter().enumerate() {
					let cty = self.emit_ty(in_val);
					let name = self.create_interned_name(cformat!("phi_{}_{}", block_name, i));

					cwrite!(phi_segment, "\t{} {};\n", cty.name, name);

					phi_nodes.entry(block_key).or_default().push(name.clone());
				}
			}

			let mut cblock = cformat!("\t{}: {{\n", block_name);

			cwrite!(cblock, "\t}}\n");

			cwrite!(block_segment, "{}", cblock);
		}

		let def = cformat!("{{\n{}{}}}", phi_segment, block_segment);


		let item = CItem::new(cformat!("{} {}", decl.body, def), name);
		self.state.function_defs.insert(function_key, item.clone());
		item
	}


	pub fn emit_declaration (&mut self) -> CString {
		let mut globals = CString::new();
		let mut functions = CString::new();

		self.type_body_out = Some(CString::new());

		for &tkey in self.ctx.tys.keys() {
			if !self.state.types.contains_key(&tkey) {
				self.emit_ty(tkey);
			}
		}

		for &gkey in self.ctx.globals.keys() {
			cwrite!(globals, "{};\n", &self.emit_global_decl(gkey).body);
		}

		for &fkey in self.ctx.functions.keys() {
			cwrite!(functions, "{};\n", &self.emit_function_decl(fkey).body);
		}

		let tys = self.type_body_out.take().unwrap();

		tys.concat(globals).concat(functions)
	}

	pub fn emit_implementation (&mut self) -> CString {
		let mut globals = CString::new();
		let mut functions = CString::new();

		for &gkey in self.ctx.globals.keys() {
			cwrite!(globals, "{};\n", &self.emit_global(gkey).body);
		}

		for &fkey in self.ctx.functions.keys() {
			cwrite!(functions, "{}\n", &self.emit_function(fkey).body);
		}

		globals.concat(functions)
	}

	pub fn emit_all (&mut self) -> CString {
		cformat!("{}\n{}", self.emit_declaration(), self.emit_implementation())
	}
}

#[test]
fn test_emitter() {
	let mut ctx = Context::new();
	let mut builder = Builder::new(&mut ctx);

	let mut f = builder.create_function();

	let fib = f.get_own_function().as_key();

	f.set_name("fib");

	let s32t = f.sint32_ty().as_key();

	let n = f.append_param(s32t).set_name("n").as_key();

	f.set_return_ty(s32t);

	let entry = f.append_new_block().set_name("entry").as_key();
	let use_n = f.append_new_block().set_name("use_n").as_key();
	let recurse = f.append_new_block().set_name("recurse").as_key();
	let end = f.append_new_block().set_name("end").as_key();

	use BinaryOp::*;
	with_block!(f, entry => {
		f.param_ref(n);
		f.load();
		f.const_sint32(2);
		f.binary_op(Lt)
		 .set_name("predicate");

		f.cond_branch(use_n, recurse);
	});

	with_block!(f, use_n => {
		f.param_ref(n);
		f.load();

		f.branch(end);
	});

	with_block!(f, recurse => {
		f.param_ref(n);
		f.load();
		f.const_sint32(1);
		f.binary_op(Sub)
		 .set_name("n-1");
		f.function_ref(fib);
		f.call()
		 .set_name("fib_n-1");

		f.param_ref(n);
		f.load();
		f.const_sint32(2);
		f.binary_op(Sub)
		 .set_name("n-2");
		f.function_ref(fib);
		f.call()
		 .set_name("fib_n-2");

		f.binary_op(Add);

		f.branch(end);
	});

	with_block!(f, end => {
		f.phi(s32t)
		 .set_name("result");

		f.ret();
	});

	f.finalize();

	let mut e = Emitter::new(
		&ctx,
		|_ctx: &Context, name: &mut CString| name.insert(0, b'$'),
		|_ctx: &Context, _ty: &Ty, name: &mut CString| {},
	);

	let h = e.emit_all();

	println!("{}", h);
}
