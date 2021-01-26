use std::fmt;

use super::{
	ty::{ PrimitiveTy, Layout }
};

pub trait Target: fmt::Debug {
	fn get_primitive_layout (&self, ty: PrimitiveTy) -> Layout;
	fn get_word_size (&self) -> u64;
	fn get_pointer_layout (&self) -> Layout { Layout::scalar(self.get_word_size()) }
}

#[derive(Debug)]
pub struct X64Linux;

impl Target for X64Linux {
	fn get_primitive_layout (&self, ty: PrimitiveTy) -> Layout {
		use PrimitiveTy::*;

		match ty {
			Bool | SInt8 | UInt8 => Layout::scalar(1),
			SInt16 | UInt16 => Layout::scalar(2),
			SInt32 | UInt32 |	Real32 => Layout::scalar(4),
			UInt64 | SInt64 | Real64 => Layout::scalar(8),
			SInt128 | UInt128 => Layout::custom_scalar(16, 8), // TODO is this correct??
		}
	}

	fn get_word_size(&self) -> u64 {
		8
	}
}