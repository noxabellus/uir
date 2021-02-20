use super::{
	builder::{ Builder, Locate, IrErrData, FunctionResult, FunctionErrLocation, IrResult },
	ir::{ Function, FunctionKey, BlockKey },
	cfg::{ Cfg, CfgErr },
};


fn walk_block (function: &Function, cfg: &mut Cfg, block_key: BlockKey) -> FunctionResult {
	let block = function.block_data.get(block_key).ok_or_else(||
		IrErrData::InvalidBlockKey(block_key)
			.at(FunctionErrLocation::Root)
	)?;

	if block.ir.is_empty() {
		return Err(IrErrData::EmptyBlock(block_key).at(FunctionErrLocation::Block(block_key)))
	}

	let mut iter = block.ir.iter().enumerate();
	let mut phi_closed = false;

	while let Some((i, node)) = iter.next() {
		if node.is_phi() {
			if phi_closed {
				return Err(
					CfgErr::PhiNotAtTop.to_ir()
						.at(FunctionErrLocation::Node(block_key, i))
				)
			}
		} else {
			phi_closed = true;

			if node.is_terminator() {
				node.for_each_edge(|to| cfg.add_edge(block_key, to)).map_err(|e|
					e.to_ir()
						.at(FunctionErrLocation::Node(block_key, i))
				)?;

				if let Some((i, _)) = iter.next() {
					return Err(
						CfgErr::NodeAfterTerminator.to_ir()
							.at(FunctionErrLocation::Node(block_key, i))
					)
				}
			}
		}
	}

	Ok(())
}

pub fn generate (builder: &mut Builder, function_key: FunctionKey) -> IrResult<Cfg> {
	let mut cfg = Cfg::default();

	let function = builder.get_function(function_key).unwrap().into_ref();

	for &block_key in function.block_order.iter() {
		walk_block(function, &mut cfg, block_key).at(function_key)?;
	}

	Ok(cfg)
}