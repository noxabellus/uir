use std::{cell::Ref, ops::Deref};

pub fn flip_ref_opt_to_opt_ref<T> (r: Ref<Option<T>>) -> Option<Ref<T>> {
	match r.deref() {
		Some(_) => Some(Ref::map(r, |o| o.as_ref().unwrap())),
		None => None
	}
}


pub fn ref_and_then<'r, T, U: 'static, F: FnOnce (&T) -> Option<&U>> (r: Ref<'r, T>, f: F) -> Option<Ref<'r, U>> {
	match f(r.deref()) {
		Some(u) => {
			// SAFETY: we're discarding the compile-time managed borrow in the reference,
			// in favor of the runtime-managed borrow in the Ref
			let u = unsafe { std::mem::transmute::<&U, &'static U>(u) };

			Some(Ref::map(r, |_| u))
		}

		None => None
	}
}

pub fn assert<E> (cond: bool, err: E) -> Result<(), E> {
	if cond {
		Ok(())
	} else {
		Err(err)
	}
}



pub fn index_of<E: PartialEq, I: Iterator<Item = E>> (i: I, el: E) -> Option<usize> {
	i.enumerate()
	 .find(|(_, e)| el == *e)
	 .map(|(i, _)| i)
}


#[macro_export]
macro_rules! re_export {
	($($module:ident),* $(,)?) => { $(
		mod $module;
		pub use $module::*;
	),* };
}



pub fn make_buffer_with_indexed<T, F: FnMut (usize) -> T> (len: usize, mut f: F) -> Box<[T]> {
	let mut v = Vec::with_capacity(len);
	for i in 0..len { v.push(f(i)) }
	v.into_boxed_slice()
}

pub fn make_buffer_with<T, F: FnMut () -> T> (len: usize, mut f: F) -> Box<[T]> {
	make_buffer_with_indexed(len, move |_| f())
}

pub fn make_buffer_default<T: Default> (len: usize) -> Box<[T]> {
	make_buffer_with(len, T::default)
}

pub fn make_buffer_clone<T: Clone> (len: usize, init: &T) -> Box<[T]> {
	make_buffer_with(len, move || init.clone())
}

pub fn make_buffer_copy<T: Copy> (len: usize, init: T) -> Box<[T]> {
	make_buffer_with(len, move || init)
}



pub fn fill_buffer_with_indexed<T, F: FnMut (usize) -> T> (b: &mut [T], mut f: F) {
	b.iter_mut().enumerate().for_each(move |(i, e)| *e = f(i))
}

pub fn fill_buffer_with<T, F: FnMut () -> T> (b: &mut [T], mut f: F) {
	fill_buffer_with_indexed(b, move |_| f())
}

pub fn fill_buffer_default<T: Default> (b: &mut [T]) {
	fill_buffer_with(b, T::default)
}

pub fn fill_buffer_clone<T: Clone> (b: &mut [T], v: &T) {
	fill_buffer_with(b, move || v.clone())
}

pub fn fill_buffer_copy<T: Copy> (b: &mut [T], v: T) {
	fill_buffer_with(b, move || v)
}



use std::cmp::Ordering;
pub fn clamp<T: Ord> (x: T, a: T, b: T) -> T {
	match (x.cmp(&a), x.cmp(&b)) {
		(Ordering::Less, _) => a,
		(_, Ordering::Greater) => b,
		_ => x,
	}
}