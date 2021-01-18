use std::{ iter::Zip, slice::Iter as SliceIter, slice::IterMut as SliceIterMut };

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[derive(Copy)]
pub struct KeyData(u32, u32);
pub trait Key: Copy + Into<KeyData> + From<KeyData> { }
impl<T> Key for T where T: Copy + Into<KeyData> + From<KeyData> { }

#[macro_export]
macro_rules! slotmap_impl_key {
	($($ty:ty),+) => { $(
		impl Into<$crate::slotmap::KeyData> for $ty { fn into (self) -> $crate::slotmap::KeyData { self.0 } }
		impl From<$crate::slotmap::KeyData> for $ty { fn from (key: $crate::slotmap::KeyData) -> Self { Self(key) } }
	)+ };
}

#[macro_export]
macro_rules! slotmap_key_ty {
	(
		$(
			$(#[$meta:meta])*
			$vis:vis struct $name:ident;
		)+
	) => {
		$(
			$(#[$meta])*
			#[repr(transparent)]
			#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
			$vis struct $name($crate::slotmap::KeyData);
			$crate::slotmap_impl_key! { $name }
		)+
	};
}


#[derive(Debug)]
pub struct Slotmap<K: Key, V> {
	slots: Vec<(u32, usize)>,
	values: Vec<V>,
	keys: Vec<K>,
	free_list: Option<(usize, usize)>,
}

impl<K: Key, V> Default for Slotmap<K, V> {
	fn default () -> Self {
		Self {
			slots: Vec::default(),
			values: Vec::default(),
			keys: Vec::default(),
			free_list: None
		}
	}
}

impl<K: Key, V> Slotmap<K, V> {
	pub fn new () -> Self {
		Self::default()
	}

	pub fn with_capacity (cap: usize) -> Self {
		Self {
			slots: Vec::with_capacity(cap),
			values: Vec::with_capacity(cap),
			keys: Vec::with_capacity(cap),
			free_list: None,
		}
	}

	fn get_free_slot (&mut self) -> usize {
		if let Some((head, tail)) = &mut self.free_list {
			let slot_idx = *head;

			if *head != *tail {
				*head = self.slots[slot_idx].1;
			} else {
				self.free_list.take();
			}

			slot_idx
		} else {
			let slot_idx = self.slots.len();

			self.slots.push((0, 0));

			slot_idx
		}
	}

	pub fn get (&self, key: K) -> Option<&V> {
		let key = key.into();
		let slot = self.slots[key.1 as usize];

		if slot.0 == key.0 {
			Some(unsafe { self.values.get_unchecked(slot.1) })
		} else {
			None
		}
	}

	pub fn get_mut (&mut self, key: K) -> Option<&mut V> {
		let key = key.into();
		let slot = self.slots[key.1 as usize];

		if slot.0 == key.0 {
			Some(unsafe { self.values.get_unchecked_mut(slot.1) })
		} else {
			None
		}
	}

	pub fn insert (&mut self, val: V) -> K {
		let slot_idx = self.get_free_slot();

		let value_idx = self.values.len();
		self.slots[slot_idx].1 = value_idx;
		self.values.push(val);

		self.slots[slot_idx].1 = value_idx;

		let key = KeyData(self.slots[slot_idx].0, slot_idx as u32).into();

		self.keys.push(key);

		key
	}

	pub fn insert_with<F: FnOnce (K) -> V> (&mut self, f: F) -> K {
		let slot_idx = self.get_free_slot();
		let value_idx = self.values.len();
		self.slots[slot_idx].1 = value_idx;

		let key = KeyData(self.slots[slot_idx].0, slot_idx as u32).into();

		let val = f(key);

		self.values.push(val);
		self.keys.push(key);

		key
	}

	fn free_slot (&mut self, slot_idx: usize) {
		let slot = &mut self.slots[slot_idx];
		slot.0 += 1;

		if let Some((head, _)) = &mut self.free_list {
			slot.1 = *head;
			*head = slot_idx;
		} else {
			self.free_list.replace((slot_idx, slot_idx));
		}
	}

	pub fn remove (&mut self, key: K) -> Option<V> {
		let KeyData(generation, slot_idx) = key.into();
		let slot_idx = slot_idx as usize;
		let slot = self.slots[slot_idx];

		if self.slots[slot_idx].0 != generation { return None }

		let value_idx = slot.1;

		self.free_slot(slot_idx);

		self.keys.swap_remove(value_idx);
		self.slots[self.keys[value_idx].into().1 as usize].1 = value_idx;

		Some(self.values.swap_remove(value_idx))
	}

	pub fn iter (&self) -> Zip<SliceIter<K>, SliceIter<V>> {
		self.keys.iter().zip(self.values.iter())
	}

	pub fn iter_mut (&mut self) -> Zip<SliceIter<K>, SliceIterMut<V>> {
		self.keys.iter().zip(self.values.iter_mut())
	}
}