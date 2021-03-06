use std::{
	cell::Ref,
	ops::Deref,
};

pub fn flip_ref_opt_to_opt_ref<T> (r: Ref<Option<T>>) -> Option<Ref<T>> {
	match r.deref() {
		Some(_) => Some(Ref::map(r, |o| o.as_ref().unwrap())),
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