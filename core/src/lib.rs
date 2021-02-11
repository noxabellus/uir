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
	fn add () -> IrResult {
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


	#[test]
	fn fib () -> IrResult {
		let mut context = Context::with_target(target::X64Linux);
		let mut builder = Builder::new(&mut context);
		let mut f = FunctionBuilder::new(&mut builder);

		let fib = f.get_own_function().as_key();

		f.set_name("fib");

		let s32t = f.sint32_ty().as_key();

		let n = f.append_param(s32t).set_name("n").as_key();

		f.set_return_ty(s32t);

		let entry = f.append_new_block().set_name("entry").as_key();
		let use_n = f.append_new_block().set_name("use_n").as_key();
		let recurse = f.append_new_block().set_name("recurse").as_key();
		let end = f.append_new_block().set_name("end").as_key();

		with_block!(f, entry => {
			f.param_ref(n);
			f.load();
			f.const_sint32(2);
			f.binary_op(Lt)
			 .set_name("predicate");

			f.cond_branch(use_n, recurse);
		});

		with_block!(f, use_n => {
			f.param_ref(n);
			f.load();
			f.branch(end);
		});

		with_block!(f, recurse => {
			f.param_ref(n);
			f.load();
			f.const_sint32(1);
			f.binary_op(Sub)
			 .set_name("n-1");
			f.function_ref(fib);
			f.call()
			 .set_name("fib(n-1)");

			f.param_ref(n);
			f.load();
			f.const_sint32(2);
			f.binary_op(Sub)
			 .set_name("n-2");
			f.function_ref(fib);
			f.call()
			 .set_name("fib(n-2)");

			f.binary_op(Add);
			f.branch(end);
		});

		with_block!(f, end => {
			f.phi(s32t)
			 .set_name("result");

			f.ret();
		});

		let function = f.finalize()?.as_key();

		let mut path: PathBuf = [ "..", "local", "log" ].iter().collect();
		create_dir_all(&path).unwrap();
		path.push("fib.ir");
		let ps = PrinterState::with_function(&context, context.functions.get(function).unwrap());
		let output = format!("{}", ps.print_own_function());
		write(&path, &output).unwrap();
		println!("{}", &output);

		Ok(())
	}

	#[test]
	fn function_builder () -> IrResult {
		add()?;
		fib()?;
		Ok(())
	}
}