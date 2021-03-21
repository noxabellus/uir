use std::{ any::Any, fmt };


use super::{
	ty::{ PrimitiveTy, Layout }
};

pub trait Target: fmt::Debug + Any {
	fn is_native (&self) -> bool;
	fn primitive_layout (&self, ty: PrimitiveTy) -> Layout;
	fn word_size (&self) -> u32;

	fn pointer_layout (&self) -> Layout { Layout::scalar(self.word_size()) }

	fn pointer_int (&self) -> PrimitiveTy {
		match self.pointer_layout().size_align() {
			x if x == self.primitive_layout(PrimitiveTy::UInt8  ).size_align() => PrimitiveTy::UInt8,
			x if x == self.primitive_layout(PrimitiveTy::UInt16 ).size_align() => PrimitiveTy::UInt16,
			x if x == self.primitive_layout(PrimitiveTy::UInt32 ).size_align() => PrimitiveTy::UInt32,
			x if x == self.primitive_layout(PrimitiveTy::UInt64 ).size_align() => PrimitiveTy::UInt64,
			x if x == self.primitive_layout(PrimitiveTy::UInt128).size_align() => PrimitiveTy::UInt128,
			_ => unreachable!("Target provided unsupported pointer Layout")
		}
	}

}






#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AMD64;

impl Target for AMD64 {
	fn is_native (&self) -> bool {
		NATIVE_TARGET == Self
	}

	fn primitive_layout (&self, ty: PrimitiveTy) -> Layout {
		use PrimitiveTy::*;

		match ty {
			Bool | SInt8 | UInt8 => Layout::scalar(1),
			SInt16 | UInt16 => Layout::scalar(2),
			SInt32 | UInt32 |	Real32 => Layout::scalar(4),
			UInt64 | SInt64 | Real64 => Layout::scalar(8),
			SInt128 | UInt128 => Layout::custom_scalar(16, 8), // TODO is this correct??
		}
	}

	fn word_size(&self) -> u32 { 8 }
}



macro_rules! create_native_target {
	($(
		[$meta:meta] $ident:ident
	)*) => {
		$(
			#[cfg($meta)]
			pub const NATIVE_TARGET: $ident = $ident;
		)*

		#[cfg(any($($meta),*))]
		impl Default for Box<dyn Target> {
			fn default () -> Self {
				Box::new(NATIVE_TARGET)
			}
		}

		#[cfg(not(any($($meta),*)))]
		impl Default for Box<dyn Target> {
			fn default () -> Self {
				panic!("No native target exists for the host platform, cannot default-initialize")
			}
		}
	};
}

create_native_target! {
	[target_arch = "aarch64"]
	AARCH64

	[all(target_family = "unix", target_arch = "x86_64")]
	AMD64

	[all(target_family = "unix", target_arch = "x86")]
	X86

	[all(target_family = "windows", target_arch = "x86_64")]
	WIN64

	[all(target_family = "windows", target_arch = "x86")]
	WIN32
}