use std::{
	mem::take,
	collections::HashMap,
};

use support::slotmap::AsKey;

use super::{
	ty::TyKey,
	ir::BlockKey,
};

#[derive(Debug, Clone, Default)]
pub struct Cfg {
	in_values: HashMap<BlockKey, Vec<TyKey>>,
	in_edges: HashMap<BlockKey, Vec<BlockKey>>,

	out_edges: HashMap<BlockKey, Vec<BlockKey>>,
	out_values: HashMap<BlockKey, Vec<TyKey>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CfgErr {
	ExistingOutEdge(BlockKey, BlockKey),
	ExistingInEdge(BlockKey, BlockKey),
	InvalidEdge(BlockKey, BlockKey),
	MissingOutEdge(BlockKey),
	MissingInEdge(BlockKey),
}

pub type CfgResult<T = ()> = Result<T, CfgErr>;

impl Cfg {
	fn insert_unique (v: &mut Vec<BlockKey>, k: BlockKey) -> Option<()> {
		if !v.contains(&k) { v.push(k); Some(()) }
		else { None }
	}

	fn remove_unique (v: &mut Vec<BlockKey>, k: BlockKey) -> Option<()> {
			v
				.iter()
				.enumerate()
				.find(|&(_, &ik)| ik == k)
				.map(|(idx, _)| idx)
				.map(|idx| { v.remove(idx); })
	}



	pub fn add_edge<FK: AsKey<BlockKey>, TK: AsKey<BlockKey>> (&mut self, from: FK, to: TK) -> CfgResult {
		let (from, to) = (from.as_key(), to.as_key());

		Self::insert_unique(
			self.out_edges.entry(from).or_default(),
			to
		).ok_or(CfgErr::ExistingOutEdge(from, to))?;

		self.out_values.entry(from).or_default();

		Self::insert_unique(
			self.in_edges.entry(to).or_default(),
			from
		).ok_or(CfgErr::ExistingInEdge(from, to))?;

		self.in_values.entry(to).or_default();

		Ok(())
	}

	pub fn remove_edge<FK: AsKey<BlockKey>, TK: AsKey<BlockKey>> (&mut self, from: FK, to: TK) -> CfgResult {
		let (from, to) = (from.as_key(), to.as_key());

		let outs = {
			self.out_edges
				.get_mut(&from)
				.and_then(|outs| {
					Self::remove_unique(outs, to)
						.map(|_| outs)
				})
				.ok_or(CfgErr::InvalidEdge(from, to))?
		};

		if outs.is_empty() {
			self.out_edges.remove(&from);
			self.out_values.remove(&from);
		}

		let ins = {
			self.in_edges
				.get_mut(&to)
				.and_then(|ins| {
					Self::remove_unique(ins, from)
						.map(|_| ins)
				})
				.ok_or(CfgErr::InvalidEdge(from, to))?
		};

		if ins.is_empty() {
			self.in_edges.remove(&to);
			self.in_values.remove(&to);
		}

		Ok(())
	}

	pub fn has_edge<FK: AsKey<BlockKey>, TK: AsKey<BlockKey>> (&mut self, from: FK, to: TK) -> bool {
		let (from, to) = (from.as_key(), to.as_key());

		if let Some(outs) = self.out_edges.get(&from) {
			outs.contains(&to)
		} else {
			false
		}
	}



	pub fn num_predecessors<K: AsKey<BlockKey>> (&self, block_key: K) -> usize {
		let block_key = block_key.as_key();

		self.in_edges.get(&block_key).map(|ins| ins.len()).unwrap_or(0)
	}

	pub fn has_predecessors<K: AsKey<BlockKey>> (&self, block_key: K) -> bool {
		self.num_predecessors(block_key) > 0
	}

	pub fn get_predecessors<K: AsKey<BlockKey>> (&self, block_key: K) -> CfgResult<&[BlockKey]> {
		let block_key = block_key.as_key();

		let ins = self.in_edges.get(&block_key).ok_or(CfgErr::MissingInEdge(block_key))?;

		Ok(ins.as_slice())
	}



	pub fn num_successors<K: AsKey<BlockKey>> (&self, block_key: K) -> usize {
		let block_key = block_key.as_key();

		self.out_edges.get(&block_key).map(|outs| outs.len()).unwrap_or(0)
	}

	pub fn has_successors<K: AsKey<BlockKey>> (&self, block_key: K) -> bool {
		self.num_successors(block_key) > 0
	}

	pub fn get_successors<K: AsKey<BlockKey>> (&self, block_key: K) -> CfgResult<&[BlockKey]> {
		let block_key = block_key.as_key();

		let outs = self.out_edges.get(&block_key).ok_or(CfgErr::MissingOutEdge(block_key))?;

		Ok(outs.as_slice())
	}



	pub fn set_in_values<K: AsKey<BlockKey>> (&mut self, block_key: K, values: Vec<TyKey>) -> CfgResult<Vec<TyKey>> {
		let block_key = block_key.as_key();

		if self.in_edges.contains_key(&block_key) {
			Ok(self.in_values.insert(block_key, values).unwrap_or_default())
		} else {
			Err(CfgErr::MissingInEdge(block_key))
		}
	}

	pub fn add_in_value<KB: AsKey<BlockKey>, KT: AsKey<TyKey>> (&mut self, block_key: KB, ty_key: KT) -> CfgResult {
		let (block_key, ty_key) = (block_key.as_key(), ty_key.as_key());

		let vals = self.in_values.get_mut(&block_key).ok_or(CfgErr::MissingInEdge(block_key))?;

		vals.push(ty_key);

		Ok(())
	}

	pub fn clear_in_values<K: AsKey<BlockKey>> (&mut self, block_key: K) -> CfgResult<Vec<TyKey>> {
		let block_key = block_key.as_key();

		let vals = self.in_values.get_mut(&block_key).ok_or(CfgErr::MissingInEdge(block_key))?;

		Ok(take(vals))
	}

	pub fn num_in_values<K: AsKey<BlockKey>> (&self, block_key: K) -> usize {
		let block_key = block_key.as_key();

		self.in_values.get(&block_key).map(|ins| ins.len()).unwrap_or(0)
	}

	pub fn has_in_values<K: AsKey<BlockKey>> (&self, block_key: K) -> bool {
		self.num_in_values(block_key) > 0
	}

	pub fn get_in_values<K: AsKey<BlockKey>> (&self, block_key: K) -> CfgResult<&[TyKey]> {
		let block_key = block_key.as_key();

		let vals = self.in_values.get(&block_key).ok_or(CfgErr::MissingInEdge(block_key))?;

		Ok(vals.as_slice())
	}



	pub fn set_out_values<K: AsKey<BlockKey>> (&mut self, block_key: K, values: Vec<TyKey>) -> CfgResult<Vec<TyKey>> {
		let block_key = block_key.as_key();

		if self.out_edges.contains_key(&block_key) {
			Ok(self.out_values.insert(block_key, values).unwrap_or_default())
		} else {
			Err(CfgErr::MissingOutEdge(block_key))
		}
	}

	pub fn add_out_value<KB: AsKey<BlockKey>, KT: AsKey<TyKey>> (&mut self, block_key: KB, ty_key: KT) -> CfgResult {
		let (block_key, ty_key) = (block_key.as_key(), ty_key.as_key());

		let vals = self.out_values.get_mut(&block_key).ok_or(CfgErr::MissingOutEdge(block_key))?;

		vals.push(ty_key);

		Ok(())
	}

	pub fn clear_out_values<K: AsKey<BlockKey>> (&mut self, block_key: K) -> CfgResult<Vec<TyKey>> {
		let block_key = block_key.as_key();

		let vals = self.out_values.get_mut(&block_key).ok_or(CfgErr::MissingOutEdge(block_key))?;

		Ok(take(vals))
	}

	pub fn num_out_values<K: AsKey<BlockKey>> (&self, block_key: K) -> usize {
		let block_key = block_key.as_key();

		self.out_values.get(&block_key).map(|outs| outs.len()).unwrap_or(0)
	}

	pub fn has_out_values<K: AsKey<BlockKey>> (&self, block_key: K) -> bool {
		self.num_out_values(block_key) > 0
	}

	pub fn get_out_values<K: AsKey<BlockKey>> (&self, block_key: K) -> CfgResult<&[TyKey]> {
		let block_key = block_key.as_key();

		let vals = self.out_values.get(&block_key).ok_or(CfgErr::MissingOutEdge(block_key))?;

		Ok(vals.as_slice())
	}
}