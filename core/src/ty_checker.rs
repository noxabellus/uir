use support::{
	stack::Stack,
};


use super::{
	ir::*,
	cfg::*,
	ty::*,
	builder::*,
};


#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TyErr {
	ExpectedTy(TyKey, TyKey),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TyCkErr {
	TyErr(TyErr),
	IrErr(IrErr),
}

impl From<TyErr> for TyCkErr {
	fn from (e: TyErr) -> TyCkErr { TyCkErr::TyErr(e) }
}

impl From<IrErr> for TyCkErr {
	fn from (e: IrErr) -> TyCkErr { TyCkErr::IrErr(e) }
}

pub type TyCkResult<T = ()> = Result<T, TyCkErr>;

pub struct TyChecker<'r, 'b, 'c> {
	pub builder: &'r FunctionBuilder<'b>,
	pub cfg: &'c mut Cfg,
	pub stack: Stack<TyKey>,
}


impl<'r, 'b, 'c> TyChecker<'r, 'b, 'c> {
	pub fn new (builder: &'r FunctionBuilder<'b>, cfg: &'c mut Cfg) -> Self {
		Self {
			builder, cfg,
			stack: Stack::default()
		}
	}

	pub fn check_constant (&mut self, idx: usize, constant: &Constant) -> TyCkResult {
		use Constant::*;

		match constant {
			Null
			=> { }

			Bool(bool)
			=> { }

			SInt8(i8)
			=> { }

			SInt16(i16)
			=> { }

			SInt32(i32)
			=> { }

			SInt64(i64)
			=> { }

			SInt128(i128)
			=> { }

			UInt8(u8)
			=> { }

			UInt16(u16)
			=> { }

			UInt32(u32)
			=> { }

			UInt64(u64)
			=> { }

			UInt128(u128)
			=> { }

			Real32(f32)
			=> { }

			Real64(f64)
			=> { }

			Aggregate(tykey, vec_u64, vec_constant)
			=> { }
		}

		Ok(())
	}

	pub fn check_const_node (&mut self, idx: usize, constant: &ConstIr) -> TyCkResult {
		todo!()
	}

	pub fn check_node (&mut self, idx: usize, node: &Ir) -> TyCkResult {
		use IrData::*;

		match &node.data {
			Constant(constant)
			=> { }

			BuildAggregate(tykey, vec_u64)
			=> { }

			GlobalKey(globalkey)
			=> { }

			FunctionKey(functionkey)
			=> { }

			BlockKey(blockkey)
			=> { }

			ParamKey(paramkey)
			=> { }

			LocalKey(localkey)
			=> { }

			Phi(tykey)
			=> { }

			BinaryOp(binaryop)
			=> { }

			UnaryOp(unaryop)
			=> { }

			CastOp(castop, tykey)
			=> { }

			Gep
			=> { }

			StaticGep(vec_u64)
			=> { }

			Load
			=> { }

			Store
			=> { }

			Branch(blockkey)
			=> { }

			CondBranch(ablockkey, bblockkey)
			=> { }

			Switch(vec_constir_blockkey)
			=> { }

			ComputedBranch(vec_blockkey)
			=> { }

			Call
			=> { }

			Ret
			=> { }

			Duplicate
			=> { }

			Discard
			=> { }

			Unreachable
			=> { }
		}

		Ok(())
	}

	pub fn check_block (&mut self, block: BlockKey) -> TyCkResult {
		let block = self.builder.get_block(block)?;

		for (i, node) in block.ir.iter().enumerate() {
			self.check_node(i, node)?;
		}

		Ok(())
	}

	pub fn check_function (&mut self) -> TyCkResult {
		for &block_ref in self.builder.function.block_order.iter() {
			self.check_block(block_ref)?;
		}

		Ok(())
	}
}


pub fn check<'b, 'c> (builder: &FunctionBuilder<'b>, cfg: &'c mut Cfg) -> TyCkResult {
	let mut state = TyChecker::new(builder, cfg);

	state.check_function()
}