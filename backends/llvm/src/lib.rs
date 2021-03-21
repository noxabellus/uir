#[macro_use]
pub mod wrapper;
pub use wrapper::{ LLVMType, LLVMValue, LLVMString, LLVMStr };

pub mod abi;

pub mod emitter;
pub use emitter::Emitter;

pub mod optimizer;
pub use optimizer::Optimizer;

#[cfg(feature = "jit")]
pub mod jit;
#[cfg(feature = "jit")]
pub use jit::Jit;

#[cfg(test)]
mod test;