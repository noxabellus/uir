use std::{collections::HashMap, hash::Hash, ops, slice, vec};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[derive(Copy)]
pub struct KeyData(u32, u32);
pub trait Key: Copy + Eq + Hash + Into<KeyData> + From<KeyData> { }
impl<T> Key for T where T: Copy + Eq + Hash + Into<KeyData> + From<KeyData> { }

pub trait AsKey<K: Key> {
	fn as_key (&self) -> K;
}

impl<K: Key> AsKey<K> for K {
	fn as_key (&self) -> K { *self }
}

impl<K: Key> AsKey<K> for &K {
	fn as_key (&self) -> K { **self }
}

impl<K: Key> AsKey<K> for &mut K {
	fn as_key (&self) -> K { **self }
}


pub trait Keyable {
	type Key: Key;
}


#[derive(Debug)]
pub struct Keyed<'a, D: Keyable> {
	pub key: D::Key,
	pub value: &'a D,
}

impl<'a, D: Keyable> Clone for Keyed<'a, D> {
	fn clone (&self) -> Self {
		Self {
			key: self.key,
			value: self.value,
		}
	}
}

impl<'a, D: Keyable> Copy for Keyed<'a, D> { }

impl<'a, D: Keyable> Keyed<'a, D> {
	pub fn into_ref (self) -> &'a D {
		self.value
	}
}

impl<'a, D: Keyable> AsRef<D> for Keyed<'a, D> {
	fn as_ref (&self) -> &D { self.value }
}

impl<'a, D: Keyable> AsKey<D::Key> for Keyed<'a, D> {
	fn as_key (&self) -> D::Key { self.key }
}

impl<'a, D: Keyable> ops::Deref for Keyed<'a, D> {
	type Target = D;
	fn deref (&self) -> &Self::Target { self.value }
}


#[derive(Debug)]
pub struct KeyedMut<'a, D: Keyable> {
	pub key: D::Key,
	pub value: &'a mut D,
}

impl<'a, D: Keyable> KeyedMut<'a, D> {
	pub fn into_keyed (self) -> Keyed<'a, D> {
		Keyed { key: self.key, value: self.value }
	}

	pub fn into_ref (self) -> &'a D {
		self.value
	}

	pub fn into_mut (self) -> &'a mut D {
		self.value
	}
}

impl<'a, D: Keyable> AsRef<D> for KeyedMut<'a, D> {
	fn as_ref (&self) -> &D { self.value }
}

impl<'a, D: Keyable> AsMut<D> for KeyedMut<'a, D> {
	fn as_mut (&mut self) -> &mut D { self.value }
}

impl<'a, D: Keyable> AsKey<D::Key> for KeyedMut<'a, D> {
	fn as_key (&self) -> D::Key { self.key }
}

impl<'a, D: Keyable> ops::Deref for KeyedMut<'a, D> {
	type Target = D;
	fn deref (&self) -> &Self::Target { self.value }
}

impl<'a, D: Keyable> ops::DerefMut for KeyedMut<'a, D> {
	fn deref_mut (&mut self) -> &mut Self::Target { self.value }
}


#[macro_export]
macro_rules! slotmap_impl_key {
	($($ty:ty),+) => { $(
		impl From<$ty> for $crate::slotmap::KeyData { fn from (t: $ty) -> $crate::slotmap::KeyData { t.0 } }
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
			#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
			$vis struct $name($crate::slotmap::KeyData);
			$crate::slotmap_impl_key! { $name }
		)+
	};
}

#[macro_export]
macro_rules! slotmap_keyable {
	(
		$(
			$(#[$meta:meta])*
			$(impl <$($template:tt)*>)? $tyname:ident $(<$($generics:tt)*>)?
		),+ $(,)?
	) => {
		$(
			$crate::paste! {
				$crate::slotmap_key_ty! {
					$($meta)*
					pub struct [<$tyname Key>];
				}

				impl $(<$($template)*>)? $crate::slotmap::Keyable for $tyname $(<$($generics)*>)? {
					type Key = [<$tyname Key>];
				}
			}
		)+
	};
}



#[derive(Debug, Clone)]
pub struct Slotmap<K: Key, V: Keyable<Key = K>> {
	slots: Vec<(u32, usize)>,
	values: Vec<Option<V>>,
	keys: Vec<K>,
	free_list: Option<(usize, usize)>,
}

impl<K: Key, V: Keyable<Key = K>> Default for Slotmap<K, V> {
	fn default () -> Self {
		Self {
			slots: Vec::default(),
			values: Vec::default(),
			keys: Vec::default(),
			free_list: None
		}
	}
}

impl<K: Key, V: Keyable<Key = K>> Slotmap<K, V> {
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


	pub fn len (&self) -> usize {
		self.values.len()
	}

	pub fn is_empty (&self) -> bool {
		self.values.is_empty()
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

			self.slots.push((1, 0));

			slot_idx
		}
	}

	pub fn get_index (&self, key: K) -> Option<usize> {
		let key = key.into();
		let slot = self.slots[key.1 as usize];

		if slot.0 == key.0 {
			Some(slot.1)
		} else {
			None
		}
	}

	pub fn get (&self, key: K) -> Option<&V> {
		self.get_index(key).and_then(move |idx| {
			unsafe { self.values.get_unchecked(idx) }.as_ref()
		})
	}

	pub fn get_mut (&mut self, key: K) -> Option<&mut V> {
		self.get_index(key).and_then(move |idx| {
			unsafe { self.values.get_unchecked_mut(idx) }.as_mut()
		})
	}

	pub fn get_keyed (&self, key: K) -> Option<Keyed<'_, V>> {
		self.get(key).map(|value| Keyed { key, value })
	}

	pub fn get_keyed_mut (&mut self, key: K) -> Option<KeyedMut<'_, V>> {
		self.get_mut(key).map(|value| KeyedMut { key, value })
	}

	pub fn insert (&mut self, val: V) -> KeyedMut<'_, V> {
		let slot_idx = self.get_free_slot();

		let value_idx = self.values.len();
		self.slots[slot_idx].1 = value_idx;
		self.values.push(Some(val));

		self.slots[slot_idx].1 = value_idx;

		let key = KeyData(self.slots[slot_idx].0, slot_idx as u32).into();

		self.keys.push(key);

		KeyedMut { key, value: unsafe { self.values.get_unchecked_mut(value_idx) }.as_mut().unwrap() }
	}

	pub fn insert_with<F: FnOnce (K) -> V> (&mut self, f: F) -> KeyedMut<'_, V> {
		let slot_idx = self.get_free_slot();
		let value_idx = self.values.len();
		self.slots[slot_idx].1 = value_idx;

		let key = KeyData(self.slots[slot_idx].0, slot_idx as u32).into();

		let val = f(key);

		self.values.push(Some(val));
		self.keys.push(key);

		KeyedMut { key, value: unsafe { self.values.get_unchecked_mut(value_idx) }.as_mut().unwrap() }
	}

	pub fn reserve (&mut self) -> K {
		let slot_idx = self.get_free_slot();

		let value_idx = self.values.len();
		self.slots[slot_idx].1 = value_idx;
		self.values.push(None);

		self.slots[slot_idx].1 = value_idx;

		let key = KeyData(self.slots[slot_idx].0, slot_idx as u32).into();

		self.keys.push(key);

		key
	}

	pub fn define (&mut self, key: K, val: V) -> Option<KeyedMut<V>> {
		let key = key.into();
		let slot = self.slots[key.1 as usize];

		if slot.0 == key.0 {
			let slot = unsafe { self.values.get_unchecked_mut(slot.1) };

			if slot.is_none() {
				slot.replace(val);
				return Some(KeyedMut { key: key.into(), value: slot.as_mut().unwrap() })
			}
		}

		None
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

		self.values.swap_remove(value_idx)
	}

	pub fn iter (&self) -> PairIter<'_, K, V> {
		PairIter(self.keys.iter(), self.values.iter())
	}

	pub fn iter_mut (&mut self) -> PairIterMut<'_, K, V> {
		PairIterMut(self.keys.iter(), self.values.iter_mut())
	}

	pub fn keys (&self) -> slice::Iter<'_, K> {
		self.keys.iter()
	}

	pub fn values (&self) -> ValueIter<'_, V> {
		ValueIter(self.values.iter())
	}

	pub fn values_mut (&mut self) -> ValueIterMut<'_, V> {
		ValueIterMut(self.values.iter_mut())
	}

	pub fn collapse (self) -> CollapsedSlotmap<K, V> {
		let mut map = HashMap::default();
		let mut vec = Vec::default();

		for (k, v) in self.into_iter() {
			let i = vec.len();
			map.insert(k, i);
			vec.push(v);
		}

		CollapsedSlotmap {
			map,
			values: vec.into_boxed_slice()
		}
	}

	pub fn collapse_cloned (&self) -> CollapsedSlotmap<K, V>
	where V: Clone
	{
		let mut map = HashMap::default();
		let mut vec = Vec::default();

		for (&k, v) in self.iter() {
			let i = vec.len();
			map.insert(k, i);
			vec.push(v.clone());
		}

		CollapsedSlotmap {
			map,
			values: vec.into_boxed_slice()
		}
	}

	pub fn predict_collapse (&self) -> SlotmapCollapsePredictor<'_, K, V> {
		let mut key_to_idx = HashMap::default();
		let mut idx_to_key = Vec::default();

		for (i, (&k, _)) in self.iter().enumerate() {
			key_to_idx.insert(k, i);
			idx_to_key.push(k);
		}

		SlotmapCollapsePredictor {
			key_to_idx,
			idx_to_key,
			base: self
		}
	}
}




#[derive(Debug, Clone)]
pub struct CollapsedSlotmap<K: Key, V: Keyable<Key = K>> {
	map: HashMap<K, usize>,
	values: Box<[V]>
}

impl<K: Key, V: Keyable<Key = K>> ops::Deref for CollapsedSlotmap<K, V> {
	type Target = [V];
	fn deref (&self) -> &[V] { self.values.as_ref() }
}

impl<K: Key, V: Keyable<Key = K>> ops::DerefMut for CollapsedSlotmap<K, V> {
	fn deref_mut (&mut self) -> &mut [V] { self.values.as_mut() }
}

impl<K: Key, V: Keyable<Key = K>> CollapsedSlotmap<K, V> {
	pub fn get_index (&self, k: K) -> Option<usize> {
		self.map.get(&k).copied()
	}

	pub fn get_by_key (&self, k: K) -> Option<&V> {
		self.get_index(k).and_then(move |idx| self.values.get(idx))
	}

	pub fn get_by_key_mut (&mut self, k: K) -> Option<&mut V> {
		self.get_index(k).and_then(move |idx| self.values.get_mut(idx))
	}

	pub fn into_inner (self) -> Box<[V]> {
		self.values
	}
}


#[derive(Debug, Clone)]
pub struct SlotmapCollapsePredictor<'s, K: Key, V: Keyable<Key = K>> {
	key_to_idx: HashMap<K, usize>,
	idx_to_key: Vec<K>,
	base: &'s Slotmap<K, V>
}

impl<'s, K: Key, V: Keyable<Key = K>> SlotmapCollapsePredictor<'s, K, V> {
	pub fn get_index (&self, k: K) -> Option<usize> {
		self.key_to_idx.get(&k).copied()
	}

	pub fn get_key (&self, idx: usize) -> Option<K> {
		self.idx_to_key.get(idx).copied()
	}

	pub fn len (&self) -> usize {
		self.key_to_idx.len()
	}

	pub fn is_empty (&self) -> bool {
		self.key_to_idx.is_empty()
	}

	pub fn get_value (&self, k: K) -> Option<&V> {
		self.base.get(k)
	}

	pub fn get_value_keyed (&self, k: K) -> Option<Keyed<'_, V>> {
		self.base.get_keyed(k)
	}

	pub fn get_value_by_index (&self, idx: usize) -> Option<&V> {
		self.get_value(self.get_key(idx)?)
	}

	pub fn iter (&self) -> slice::Iter<'_, K> {
		self.idx_to_key.iter()
	}
}


pub struct ValueIter<'a, V> (slice::Iter<'a, Option<V>>);

impl<'a, V> Iterator for ValueIter<'a, V> {
	type Item = &'a V;
	fn next (&mut self) -> Option<&'a V> {
		match self.0.next() {
			Some(Some(x)) => Some(x),
			Some(None) => self.next(),
			None => None
		}
	}
}


pub struct ValueIterMut<'a, V: Keyable> (slice::IterMut<'a, Option<V>>);

impl<'a, V: Keyable> Iterator for ValueIterMut<'a, V> {
	type Item = &'a mut V;
	fn next (&mut self) -> Option<&'a mut V> {
		match self.0.next() {
			Some(x) => x.as_mut(),
			None => None
		}
	}
}

pub struct PairIter<'a, K: Key, V: Keyable<Key = K>> (slice::Iter<'a, K>, slice::Iter<'a, Option<V>>);

impl<'a, K: Key, V: Keyable<Key = K>> Iterator for PairIter<'a, K, V> {
	type Item = (&'a K, &'a V);
	fn next (&mut self) -> Option<Self::Item> {
		let key = self.0.next()?;
		match self.1.next() {
			Some(Some(val)) => Some((key, val)),
			Some(None) => self.next(),
			None => None
		}
	}
}

pub struct PairIterMut<'a, K: Key, V: Keyable<Key = K>> (slice::Iter<'a, K>, slice::IterMut<'a, Option<V>>);

impl<'a, K: Key, V: Keyable<Key = K>> Iterator for PairIterMut<'a, K, V> {
	type Item = (&'a K, &'a mut V);
	fn next (&mut self) -> Option<Self::Item> {
		let key = self.0.next()?;
		match self.1.next() {
			Some(Some(val)) => Some((key, val)),
			Some(None) => self.next(),
			None => None
		}
	}
}


pub struct IntoIter<K: Key, V: Keyable<Key = K>> (vec::IntoIter<K>, vec::IntoIter<Option<V>>);

impl<K: Key, V: Keyable<Key = K>> Iterator for IntoIter<K, V> {
	type Item = (K, V);
	fn next (&mut self) -> Option<Self::Item> {
		let key = self.0.next()?;
		match self.1.next() {
			Some(Some(val)) => Some((key, val)),
			Some(None) => self.next(),
			None => None
		}
	}
}

impl<K: Key, V: Keyable<Key = K>> IntoIterator for Slotmap<K, V> {
	type Item = (K, V);
	type IntoIter = IntoIter<K, V>;

	fn into_iter (self) -> Self::IntoIter {
		IntoIter(self.keys.into_iter(), self.values.into_iter())
	}
}