#![allow(unused_variables)]
#[allow(unused_imports)]
use {
	std::{
		io, ops, fmt::{ self, Write },
		rc::{Rc, Weak},
		cell::{RefCell, Ref, RefMut},
		collections::HashMap,
	},
	uir_core::{
		support::{
			slotmap::{ Key, AsKey },
		},
		ir::*,
		ty::*,
		builder::*,
	},
};


#[derive(Clone, Default)]
pub struct CString(Vec<u8>);

impl fmt::Display for CString {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", unsafe { std::str::from_utf8_unchecked(self.0.as_slice()) })
	}
}

impl fmt::Display for CStr {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", unsafe { std::str::from_utf8_unchecked(&self.0) })
	}
}

impl CString {
	pub fn new () -> Self { Self::default() }

	pub fn ensure_ascii_non_null (s: &[u8]) -> bool {
		s.iter().find(|&&x| x == 0 || x > 128).is_none()
	}

	pub fn as_cstr (&self) -> &CStr {
		unsafe { &*(self.0.as_slice() as *const _ as *const _) }
	}

	pub fn write_cstr (&mut self, cstr: impl ToCStr) {
		self.write_str(cstr.to_cstr().as_str()).unwrap()
	}

	pub fn insert (&mut self, index: usize, value: u8) {
		self.0.insert(index, value)
	}
}

impl fmt::Write for CString {
	fn write_str (&mut self, s: &str) -> fmt::Result {
		self.0.extend_from_slice(s.to_cstr().as_bytes());
		Ok(())
	}
}


impl From<String> for CString {
	fn from (s: String) -> CString {
		assert!(CString::ensure_ascii_non_null(s.as_bytes()));
		CString(s.into_bytes())
	}
}

impl<'a> From<&'a [u8]> for CString {
	fn from (s: &'a [u8]) -> CString {
		assert!(CString::ensure_ascii_non_null(s));
		CString(s.to_vec())
	}
}

impl<'a> From<&'a CStr> for CString {
	fn from (s: &'a CStr) -> CString {
		CString(s.as_bytes().to_vec())
	}
}

impl<'a> From<&'a str> for CString {
	fn from (s: &'a str) -> CString {
		assert!(CString::ensure_ascii_non_null(s.as_bytes()));
		CString(s.as_bytes().to_vec())
	}
}

impl From<CString> for String {
	fn from (c: CString) -> String {
		unsafe { String::from_utf8_unchecked(c.0) }
	}
}

impl ops::Deref for CString {
	type Target = CStr;
	fn deref (&self) -> &Self::Target {
		self.as_cstr()
	}
}


pub trait ToCString {
	fn to_cstring (&self) -> CString;
}
impl<T> ToCString for T where T: ToString { fn to_cstring(&self) -> CString { self.to_string().into() } }


pub trait ToCStr {
	fn to_cstr (&self) -> &CStr;
}

impl ToCStr for CString {
	fn to_cstr (&self) -> &CStr {
		self.as_cstr()
	}
}

impl ToCStr for &CString {
	fn to_cstr (&self) -> &CStr {
		self.as_cstr()
	}
}

impl ToCStr for CStr {
	fn to_cstr (&self) -> &CStr {
		self
	}
}

impl ToCStr for &CStr {
	fn to_cstr (&self) -> &CStr {
		self
	}
}

impl ToCStr for String {
	fn to_cstr (&self) -> &CStr {
		self.as_str().to_cstr()
	}
}

impl<'s> ToCStr for &String {
	fn to_cstr (&self) -> &CStr {
		CStr::from_str(self)
	}
}

impl<'s> ToCStr for str {
	fn to_cstr (&self) -> &CStr {
		CStr::from_str(self)
	}
}

impl<'s> ToCStr for &str {
	fn to_cstr (&self) -> &CStr {
		CStr::from_str(self)
	}
}

impl<'s> ToCStr for [u8] {
	fn to_cstr (&self) -> &CStr {
		CStr::from_bytes(self)
	}
}

impl<'s> ToCStr for &[u8] {
	fn to_cstr (&self) -> &CStr {
		CStr::from_bytes(self)
	}
}

pub struct CStr([u8]);
impl CStr {
	#[allow(clippy::should_implement_trait)]
	pub fn from_str (s: &str) -> &CStr { s.into() }
	/// # Safety
	/// See `CString::ensure_ascii_non_null`
	pub unsafe fn from_str_unchecked (s: &str) -> &CStr { &*(s as *const _ as *const _) }

	pub fn from_bytes (s: &[u8]) -> &CStr { s.into() }
	/// # Safety
	/// See `CString::ensure_ascii_non_null`
	pub unsafe fn from_bytes_unchecked (s: &[u8]) -> &CStr { &*(s as *const _ as *const _) }

	pub fn as_str (&self) -> &str { self.into() }
	pub fn as_bytes (&self) -> &[u8] { self.into() }
}

impl<'a> From<&'a str> for &'a CStr {
	fn from (s: &'a str) -> &'a CStr {
		assert!(CString::ensure_ascii_non_null(s.as_bytes()));
		unsafe { &*(s as *const _ as *const _) }
	}
}

impl<'a> From<&'a [u8]> for &'a CStr {
	fn from (s: &'a [u8]) -> &'a CStr {
		assert!(CString::ensure_ascii_non_null(s));
		unsafe { &*(s as *const _ as *const _) }
	}
}

impl<'a> From<&'a CStr> for &'a str {
	fn from (s: &'a CStr) -> &'a str {
		unsafe { &*(s as *const _ as *const _) }
	}
}

impl<'a> From<&'a CStr> for &'a [u8] {
	fn from (s: &'a CStr) -> &'a [u8] {
		unsafe { &*(s as *const _ as *const _) }
	}
}


#[macro_export]
macro_rules! c_str {
	($expr:expr) => { CStr::from_str($expr) };
}

#[macro_export]
macro_rules! or_else { ($opt:expr , $def:expr) => { $opt.unwrap_or_else(|| $def) } }

#[derive(Clone)]
pub struct CData {
	pub value: CString,
	pub name: CString,
}
impl CData {
	pub fn new (value: CString, name: CString) -> CData { Self { value, name } }
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
	fn deref (&self) -> &CData { self.0.deref() }
}

impl CItem {
	pub fn new (value: impl Into<CString>, name: impl Into<CString>) -> Self {
		Self(Rc::new(CData::new(value.into(), name.into())))
	}
}




pub struct Emitter<'c> {
	pub ctx: &'c Context,
	pub state: EmitterState,
	pub name_interner: Box<dyn FnMut (&mut CString)>,
	pub name_mangler: Box<dyn FnMut (&Ty, &mut CString)>,
}

#[derive(Default)]
pub struct EmitterState {
	pub types: HashMap<TyKey, CItem>,
	pub globals: HashMap<GlobalKey, CItem>,
	pub functions: HashMap<FunctionKey, CItem>,
	pub anon_counter: usize,
}


impl<'c> Emitter<'c> {
	pub fn new (ctx: &'c Context, name_interner: impl FnMut (&mut CString) + 'static, name_mangler: impl FnMut (&Ty, &mut CString) + 'static) -> Self {
		Self {
			ctx,
			state: EmitterState::default(),
			name_interner: Box::new(name_interner) as Box<dyn FnMut (&mut CString)>,
			name_mangler: Box::new(name_mangler) as Box<dyn FnMut (&Ty, &mut CString)>,
		}
	}

	pub fn intern_name (&mut self, name: impl ToCString) -> CString {
		let mut name = name.to_cstring();
		(self.name_interner)(&mut name);
		name
	}

	pub fn mangle_name (&mut self, ty: &Ty, name: impl ToCString) -> CString {
		let mut name = name.to_cstring();
		(self.name_mangler)(ty, &mut name);
		name
	}

	pub fn create_anon_id (&self, key: impl Key) -> impl fmt::Display {
		key.as_integer()
	}


	pub fn emit_constant (&mut self, constant: &Constant) -> (TyKey, CString) {
		match constant {
			&Constant::Null(ty_key)
			=> (ty_key, cformat!("(({}) NULL)", self.emit_ty(ty_key).name)),

			Constant::Bool(bool)
			=> (self.ctx.ty_dict.bool, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::Bool), (if *bool { 1 } else { 0 }))),

			Constant::SInt8(i8)
			=> (self.ctx.ty_dict.sint8, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::SInt8), i8)),

			Constant::SInt16(i16)
			=> (self.ctx.ty_dict.sint16, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::SInt16), i16)),

			Constant::SInt32(i32)
			=> (self.ctx.ty_dict.sint32, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::SInt32), i32)),

			Constant::SInt64(i64)
			=> (self.ctx.ty_dict.sint64, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::SInt64), i64)),

			Constant::SInt128(i128)
			=> (self.ctx.ty_dict.sint128, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::SInt128), i128)),

			Constant::UInt8(u8)
			=> (self.ctx.ty_dict.uint8, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::UInt8), u8)),

			Constant::UInt16(u16)
			=> (self.ctx.ty_dict.uint16, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::UInt16), u16)),

			Constant::UInt32(u32)
			=> (self.ctx.ty_dict.uint32, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::UInt32), u32)),

			Constant::UInt64(u64)
			=> (self.ctx.ty_dict.uint64, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::UInt64), u64)),

			Constant::UInt128(u128)
			=> (self.ctx.ty_dict.uint128, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::UInt128), u128)),

			Constant::Real32(f32)
			=> (self.ctx.ty_dict.real32, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::Real32), f32)),

			Constant::Real64(f64)
			=> (self.ctx.ty_dict.real64, cformat!("(({}) {})", self.emit_primitive_ty(PrimitiveTy::Real64), f64)),

			&Constant::Aggregate(ty_key, ref agg_data) => {
				let ty = self.ctx.tys.get(ty_key).unwrap();
				let cty = self.emit_ty(ty_key);

				let mut body = cformat!("(({}) {{ ", cty.name);

				use ConstantAggregateData::*;
				match agg_data {
					Zeroed => { }

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

									if i != field_tys.len() - 1 { cwrite!(body, ", ") }
								}
							}

							| &TyData::Array { length, element_ty }
							| &TyData::Vector { length, element_ty }
							=> {
								let element_ty = self.ctx.tys.get(element_ty).unwrap();
								assert!(element_ty.equivalent(elem_ty));

								for i in 0..length {
									cwrite!(body, "{}", elem);

									if i != length - 1 { cwrite!(body, ", ") }
								}
							}

							_ => unreachable!()
						}
					}

					Indexed(indexed_vals) => { todo!() }

					Complete(vals) => { todo!() }

					Uninitialized => unreachable!("uninitialized values should be handled at a higher emitter level")
				}

				cwrite!(body, " }})");

				(ty_key, body)
			}
		}
	}



	pub fn emit_primitive_ty (&self, prim: PrimitiveTy) -> &'static CStr {
		c_str!(match prim {
			PrimitiveTy::Bool    => "char",
			PrimitiveTy::SInt8   => "signed char",
			PrimitiveTy::SInt16  => "signed short",
			PrimitiveTy::SInt32  => "signed int",
			PrimitiveTy::SInt64  => "signed long",
			PrimitiveTy::SInt128 => "signed __int128",
			PrimitiveTy::UInt8   => "unsigned char",
			PrimitiveTy::UInt16  => "unsigned short",
			PrimitiveTy::UInt32  => "unsigned int",
			PrimitiveTy::UInt64  => "unsigned long",
			PrimitiveTy::UInt128 => "unsigned __int128",
			PrimitiveTy::Real32  => "float",
			PrimitiveTy::Real64  => "double",
		})
	}


	pub fn emit_ty (&mut self, ty_key: TyKey) -> CItem {
		if let Some(existing) = self.state.types.get(&ty_key) {
			return existing.clone()
		}


		let ty = self.ctx.tys.get(ty_key).unwrap();

		let user_name = ty.name.as_ref().map(|n| n.to_cstring());

		macro_rules! name { ($def:expr) => { or_else!(user_name, $def) } }

		let (def, name) =
			match &ty.data {
				TyData::Void
				=> ("void".into(), name!(self.intern_name("void"))),


				TyData::Block
				=> ("void*".into(), name!(self.intern_name("block_address"))),

				TyData::Primitive(prim)
				=> (self.emit_primitive_ty(*prim).into(), name!(prim.as_str().into())),

				TyData::Pointer { target_ty }
				=> {
					let ctarget = self.emit_ty(*target_ty);

					(cformat!("{}*", ctarget.name), name!(cformat!("{}_{}", ctarget.name, self.intern_name("ptr"))))
				}

				TyData::Array { length, element_ty } => {
					let celem = self.emit_ty(*element_ty);

					(cformat!("struct {{ {}[{}] data; }}", celem.name, length), name!(cformat!("{}_{}{}", celem.name, self.intern_name("arr"), length)))
				}

				TyData::Vector { length, element_ty } => {
					let celem = self.emit_ty(*element_ty);

					let mut body = CString::from("struct { ");
					for i in 0..*length {
						cwrite!(body, "{} e{}; ", celem.name, i);
					}
					cwrite!(body, "}}");

					(body, name!(cformat!("{}_{}{}", celem.name, self.intern_name("vec"), length)))
				}

				TyData::Structure { field_tys } => {
					let mut body = CString::from("struct {");
					for (i, &field_ty) in field_tys.iter().enumerate() {
						let cfield = self.emit_ty(field_ty);

						cwrite!(body, "\t{} f{};\n", cfield.name, i);
					}

					cwrite!(body, "}}");

					(body, name!(self.intern_name(&cformat!("anon_struct{}", self.create_anon_id(ty_key)))))
				}

				TyData::Function { parameter_tys, result_ty } => {
					let mut body = CString::new();

					let cresult = result_ty.map(|x| self.emit_ty(x).name.clone()).unwrap_or_else(|| "void".into());
					body.write_cstr(cresult);

					let name = name!(self.intern_name(&cformat!("fn_ty{}", self.create_anon_id(ty_key))));
					cwrite!(body, " (*{}) (", name);

					for (i, &param_ty) in parameter_tys.iter().enumerate() {
						let cparam = self.emit_ty(param_ty);

						body.write_cstr(&cparam.name);

						if i != parameter_tys.len() - 1 {
							body.write_cstr(", ");
						}
					}
					cwrite!(body, ")");

					(body, name)
				}
			};

		let item = CItem::new(cformat!("typedef {} {};", def, name), name);
		self.state.types.insert(ty_key, item.clone());
		item
	}
}

#[test]
fn test_emitter () {
	let mut ctx = Context::new();
	let mut builder = Builder::new(&mut ctx);

	let s32 = builder.sint32_ty().as_key();
	let pty = builder.pointer_ty(s32).unwrap().as_key();


	let mut e = Emitter::new(&ctx, |val| val.insert(0, b'$'), |_ty, _basename| ());

	let (ty, constant) = e.emit_constant(&Constant::Null(pty));
	let cty = e.emit_ty(ty);
	println!("{:?} -> {} -> {}", ty, cty.value, constant);
}