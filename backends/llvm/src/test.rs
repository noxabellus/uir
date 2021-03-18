
use {
	std::{
		io::Write,
		path::PathBuf,
		fs::create_dir_all,
	},
	uir_core::{
		support::slotmap::*,
		ir::*,
		builder::*,
		printer::*,
		target,
		with_block,
	},
	BinaryOp::*,
	crate::{
		LLVMBackend
	},
};

#[test]
fn test_full () -> IrResult {

	let log_path: PathBuf = [ "..", "..", "local", "log" ].iter().collect();
	create_dir_all(&log_path).unwrap();

	let mut ir_path = log_path.clone();
	ir_path.push("fib.ir");

	let mut llpath = log_path;
	llpath.push("fib.ll");



	let mut context = Context::with_target(target::AMD64);
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

	let (function, result) = f.finalize();
	let function = function.as_key();

	let ir_src = std::fs::File::create(ir_path).unwrap();
	write!(&ir_src, "{}", PrinterState::new(&context).with_result(result).print_function(function)).unwrap();



	let backend = LLVMBackend::new(context).unwrap();
	let llfunc = backend.emit_function_body(function);

	let llsrc = std::fs::File::create(llpath).unwrap();
	write!(&llsrc, "{:?}", llfunc).unwrap();


	Ok(())
}