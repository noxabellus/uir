#[macro_use]
pub mod wrapper;
pub use wrapper::{ LLVMType, LLVMValue, LLVMString, LLVMStr };

pub mod abi;

pub mod emitter;
pub use emitter::LLVMBackend;

#[cfg(test)]
mod test;