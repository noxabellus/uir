pub mod src;
pub mod ty;
pub mod cfg;
pub mod target;
pub mod ir;
pub mod ty_checker;
pub mod cfg_generator;
pub mod builder;
pub mod builder_macros;
pub mod printer;


#[cfg(test)]
mod test {
	use std::{fs::{create_dir_all, write}, path::PathBuf};

	use support::slotmap::*;
	use super::{
		ir::*,
		builder::*,
		target,
		with_block,
		printer::PrinterState,
	};
	use BinaryOp::*;

	#[test]
	fn function_builder () -> IrResult {
		let mut context = Context::with_target(target::X64Linux);
		let mut builder = Builder::new(&mut context);
		let mut f = FunctionBuilder::new(&mut builder);

		f.set_name("add");

		let s32t = f.sint32_ty().as_key();

		let a = f.append_param(s32t).set_name("a").as_key();
		let b = f.append_param(s32t).set_name("b").as_key();

		f.set_return_ty(s32t);

		with_block!(f, "entry" => {
			f.param_ref(a);
			f.load();

			f.param_ref(b);
			f.load();

			f.binary_op(Add)
			 .set_name("result");

			f.ret();
		});

		let function = f.finalize()?.as_key();

		let mut path: PathBuf = [ "..", "local", "log" ].iter().collect();
		create_dir_all(&path).unwrap();
		path.push("add.ir");
		let ps = PrinterState::with_function(&context, context.functions.get(function).unwrap());
		let output = format!("{}", ps.print_own_function());
		write(&path, &output).unwrap();
		println!("{}", &output);

		Ok(())
	}
}