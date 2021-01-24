// #![allow(incomplete_features)]
// #![feature(specialization)]

pub mod slotmap;

pub mod src;
pub mod ty;
pub mod ir;


#[cfg(test)]
mod tests {
	#[test]
	fn it_works() {
		println!("hello world");
	}
}
