use std::{iter::FromIterator, marker::PhantomData, vec::IntoIter};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Stack<T> {
	items: Vec<T>
}

impl<T> Default for Stack<T> { fn default () -> Self { Self { items: Vec::default() } } }


impl<T> Stack<T> {
	pub fn new () -> Self {
		Self::default()
	}

	pub fn with_capacity (capacity: usize) -> Self {
		Self { items: Vec::with_capacity(capacity) }
	}


	pub fn len (&self) -> usize {
		self.items.len()
	}

	pub fn is_empty (&self) -> bool {
		self.items.is_empty()
	}


	pub fn peek_at (&self, offset: usize) -> Option<&T> {
		if self.len() <= offset { return None }

		let index = self.len() - (offset + 1);

		self.items.get(index)
	}

	pub fn peek_at_mut (&mut self, offset: usize) -> Option<&mut T> {
		if self.len() <= offset { return None }

		let index = self.len() - (offset + 1);

		self.items.get_mut(index)
	}

	pub fn peek (&self) -> Option<&T> {
		self.items.last()
	}

	pub fn peek_mut (&mut self) -> Option<&mut T> {
		self.items.last_mut()
	}


	pub fn pop (&mut self) -> Option<T> {
		self.items.pop()
	}

	pub fn pop_n (&mut self, n: usize) -> bool {
		if self.len() < n { return false }

		unsafe { self.items.set_len(self.len() - n) }

		true
	}

	pub fn push (&mut self, item: T) {
		self.items.push(item)
	}

	pub fn as_slice (&self) -> &[T] {
		self.items.as_slice()
	}

	pub fn as_mut_slice (&mut self) -> &mut [T] {
		self.items.as_mut_slice()
	}

	pub fn duplicate (&mut self) -> bool
	where T: Clone
	{
		if let Some(top) = self.peek() {
			let top = top.clone();
			self.push(top);
			true
		} else {
			false
		}
	}

	pub fn iter (&self) -> Iter<T> {
		Iter::new(self.items.as_slice())
	}

	pub fn iter_mut (&mut self) -> IterMut<T> {
		IterMut::new(self.items.as_mut_slice())
	}

	pub fn into_inner (self) -> Vec<T> {
		self.items
	}

	pub fn from_inner (items: Vec<T>) -> Self {
		Self { items }
	}
}

pub struct Iter<'a, T> {
	ptr: *const T,
	end: *const T,
	_phantom: PhantomData<&'a T>
}

impl<'a, T> Iter<'a, T> {
	fn new (slice: &'a [T]) -> Self {
		let len = slice.len();
		let end = slice.as_ptr();

		let start = len.saturating_sub(1);

		let ptr = unsafe { end.add(start) };

		Self {
			ptr, end,
			_phantom: PhantomData
		}
	}
}

impl<'a, T> Iterator for Iter<'a, T> {
	type Item = &'a T;

	fn next (&mut self) -> Option<&'a T> {
		if self.ptr >= self.end {
			Some(unsafe {
				let res = self.ptr.as_ref();

				self.ptr = self.ptr.sub(1);

				res.unwrap()
			 })
		} else {
			None
		}
	}
}

pub struct IterMut<'a, T> {
	ptr: *mut T,
	end: *mut T,
	_phantom: PhantomData<&'a T>
}

impl<'a, T> IterMut<'a, T> {
	fn new (slice: &'a mut [T]) -> Self {
		let len = slice.len();
		let end = slice.as_mut_ptr();

		let start = len.saturating_sub(1);

		let ptr = unsafe { end.add(start) };

		Self {
			ptr, end,
			_phantom: PhantomData
		}
	}
}

impl<'a, T> Iterator for IterMut<'a, T> {
	type Item = &'a T;

	fn next (&mut self) -> Option<&'a T> {
		if self.ptr >= self.end {
			Some(unsafe {
				let res = self.ptr.as_ref();

				self.ptr = self.ptr.sub(1);

				res.unwrap()
			 })
		} else {
			None
		}
	}
}

impl<T> IntoIterator for Stack<T> {
	type Item = T;
	type IntoIter = IntoIter<T>;

	fn into_iter (self) -> IntoIter<T> {
		let mut inner = self.into_inner();
		inner.reverse();
		inner.into_iter()
	}
}

impl<T> FromIterator<T> for Stack<T> {
	fn from_iter<U: IntoIterator<Item = T>> (iter: U) -> Self {
		Self::from_inner(Vec::from_iter(iter))
	}
}


#[cfg(test)]
mod test {
	use super::Stack;

	#[test]
	fn test_stack () {
		let mut stack = Stack::new();

		stack.push(1);
		stack.push(2);
		stack.push(3);

		assert_eq!(stack.peek(), Some(&3));
		assert_eq!(stack.peek_at(0), Some(&3));
		assert_eq!(stack.peek_at(1), Some(&2));
		assert_eq!(stack.peek_at(2), Some(&1));

		let ok = vec![3, 2, 1];
		assert_eq!(stack.iter().copied().collect::<Vec<_>>(), ok);
		assert_eq!(stack.clone().into_iter().collect::<Vec<_>>(), ok);

		assert_eq!(vec![1, 2, 3].into_iter().collect::<Stack<_>>(), stack);
	}
}