pub mod src;
pub mod ty;
pub mod cfg;
pub mod target;
pub mod ir;
pub mod ty_checker;
pub mod cfg_generator;
pub mod builder;
pub mod builder_macros;


#[cfg(test)]
mod test {
	use std::{fs::{create_dir_all, write}, path::PathBuf};

	use support::slotmap::*;
	use super::{
		ir::*,
		builder::*,
		target,
		with_block,
	};
	use BinaryOp::*;

	#[test]
	fn function_builder () -> IrResult {
		let mut context = Context::with_target(target::X64Linux);
		let mut builder = Builder::new(&mut context);
		let mut f = FunctionBuilder::new(&mut builder);

		let s32t = f.sint32_ty().as_key();

		let a = f.append_param(s32t).set_name("a").as_key();
		let b = f.append_param(s32t).set_name("b").as_key();

		f.set_return_ty(s32t);

		with_block!(f, "entry" => {
			f.param_key(a);
			f.load();

			f.param_key(b);
			f.load();

			f.binary_op(Add)
			 .set_name("result");

			f.ret();
		});

		let function = f.finalize()?;

		let mut path: PathBuf = [ "..", "local", "log" ].iter().collect();
		create_dir_all(&path).unwrap();
		path.push("add.dbg");
		write(&path, format!("{:#?}", function)).unwrap();

		Ok(())
	}
}