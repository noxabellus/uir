use super::{
	builder::{ IrErr, IrResult },
	ir::{ Function, BlockKey },
	cfg::Cfg,
};


fn walk_block (function: &Function, cfg: &mut Cfg, block_key: BlockKey) -> IrResult {
	let block = function.block_data.get(block_key).ok_or(IrErr::InvalidBlockKey(block_key))?;

	let mut iter = block.ir.iter().enumerate();

	while let Some((i, node)) = iter.next() {
		if node.is_terminator() {
			node.for_each_edge(|to| cfg.add_edge(block_key, to))?;

			if iter.next().is_some() {
				return Err(IrErr::NodeAfterTerminator(block_key, i))
			}
		}
	}

	Ok(())
}

pub fn generate (function: &Function) -> IrResult<Cfg> {
	let mut cfg = Cfg::default();

	for &block_ref in function.block_order.iter() {
		walk_block(function, &mut cfg, block_ref)?;
	}

	Ok(cfg)
}