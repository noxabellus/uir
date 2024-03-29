use std::collections::HashMap;

use llvm_sys::{
	analysis::{LLVMVerifierFailureAction::*},
};

use {
	// std::{
	// 	sync::atomic::{ Ordering, AtomicBool },
	// 	path::PathBuf,
	// 	fs::create_dir_all,
	// },
	uir_core::{
		support::slotmap::*,
		ir::*,
		ty::*,
		builder::*,
		printer::*,
		target,
		block,
		with_block,
		structure_ty,
		aggregate_const,
	},
	BinaryOp::*,
	crate::{
		Emitter,
		Optimizer,
		Jit,
		wrapper::*,
	},
};


// fn llvm_from_c (c_code: &str) -> LLVMModuleRef {
// 	use std::process::{ Command, Stdio };
// 	use std::io::Write;

// 	// clang -xc -c -emit-llvm -o- -
// 	let mut clang =
// 		Command::new("clang")
// 			.arg("-xc")
// 			.arg("-c")
// 			.arg("-emit-llvm")
// 			// .arg("-O3")
// 			.arg("-o-")
// 			.arg("-")
// 			.stdin(Stdio::piped())
// 			.stdout(Stdio::piped())
// 			.spawn()
// 			.unwrap();

// 	// echo $c_code | clang -xc -c -emit-llvm -o- -
// 	clang.stdin.as_mut().unwrap().write_all(c_code.as_bytes()).unwrap();

// 	// clang_output=$(echo $c_code | clang -xc -c -emit-llvm -o- -)
// 	let clang_output = clang.wait_with_output().unwrap().stdout;

// 	llvm_from_bitcode(&clang_output)
// }

// fn llvm_from_bitcode (bit_code: &[u8]) -> LLVMModuleRef {
// 	use std::mem::MaybeUninit;

// 	unsafe {
// 		let context = LLVMContextCreate(); // TODO: this is a memory leak
// 		let mut module = MaybeUninit::uninit();

// 		let buff = LLVMCreateMemoryBufferWithMemoryRange(bit_code.as_ptr() as *const _, bit_code.len() as _, llvm_str!("bitcode").as_ptr(), LLVM_FALSE);
// 		assert!(llvm_sys::bitreader::LLVMParseBitcodeInContext2(context, buff, module.as_mut_ptr()) == LLVM_OK, "Cannot load bitcode module");
// 		LLVMDisposeMemoryBuffer(buff);

// 		module.assume_init()
// 	}
// }

// fn llvm_from_text (ir_code: &str) -> LLVMModuleRef {
// 	use std::process::{ Command, Stdio };
// 	use std::io::Write;

// 	// llvm-as
// 	let mut llvm_as =
// 		Command::new("llvm-as")
// 			.stdin(Stdio::piped())
// 			.stdout(Stdio::piped())
// 			.spawn()
// 			.unwrap();

// 	// echo $ir_code | llvm_as
// 	llvm_as.stdin.as_mut().unwrap().write_all(ir_code.as_bytes()).unwrap();

// 	// llvm_as_output=$(echo $ir_code | llvm-as)
// 	let llvm_as_output = llvm_as.wait_with_output().unwrap().stdout;

// 	llvm_from_bitcode(&llvm_as_output)
// }

// fn get_log_path (file: &str) -> PathBuf {
// 	static X: AtomicBool = AtomicBool::new(false);

// 	let mut path: PathBuf = [ "..", "..", "local", "log" ].iter().collect();

// 	if !X.load(Ordering::Relaxed) {
// 		create_dir_all(&path).unwrap();
// 		X.store(true, Ordering::Relaxed);
// 	}

// 	path.push(file);

// 	path
// }






#[test]
fn vector_types () {
	let mut context = Context::with_target(target::AMD64);
	let mut builder = Builder::new(&mut context);

	let bool = builder.bool_ty().as_key();
	let r32 = builder.real32_ty().as_key();
	let r32x2 = builder.vector_ty(2, r32).unwrap().as_key();


	let mut f = builder.create_function();

	f.set_name("compare_vector");
	let a = f.append_param(r32x2).set_name("a").as_key();
	let b = f.append_param(r32x2).set_name("b").as_key();
	f.set_return_ty(bool);

	block!(f, entry {
		f.param_ref(a);
		f.load();
		f.param_ref(b);
		f.load();
		f.binary_op(Eq);
		f.ret();
	});

	let ucompare_vector = f.finalize().map(FunctionManipulator::into_key).unwrap_rich(&builder.ctx);

	let pstate = PrinterState::new(&context);
	let mut emitter = Emitter::new(&context).unwrap();

	let llfunction = emitter.emit_function(ucompare_vector);

	println!("{}", pstate.print_function(ucompare_vector));
	println!("{:#?}", llfunction);

	llfunction.verify_function(LLVMAbortProcessAction);


	let mut optimizer = Optimizer::with_level(&emitter, 3);
	assert!(optimizer.optimize(llfunction), "failed to optimize");
	println!("optimized ir:\n{:#?}", llfunction);


	let mut jit = Jit::new(&mut emitter);
	let compare_vector = jit.get_function(llvm_str!("compare_vector"));
	assert!(!compare_vector.is_null());
	let compare_vector: extern "C" fn ((f32, f32), (f32, f32)) -> bool = unsafe { std::mem::transmute(compare_vector) };

	assert_eq!(dbg!(compare_vector((1., 2.), (1., 2.))), true);
	assert_eq!(dbg!(compare_vector((256., 10245122.), (256., 10245122.))), true);
	assert_eq!(dbg!(compare_vector((2., 1.), (1., 2.))), false);
	assert_eq!(dbg!(compare_vector((10245122., 256.), (256., 10245122.))), false);
}





#[test]
fn compare_fn_ptr () {
	let mut context = Context::with_target(target::AMD64);
	let mut builder = Builder::new(&mut context);

	let bool = builder.bool_ty().as_key();
	let r32 = builder.real32_ty().as_key();
	let fty = builder.function_ty(vec![ r32, r32 ], Some(bool)).unwrap().into_key();


	let mut f = builder.create_function();

	f.set_name("compare_fn_ptr");
	let a = f.append_param(fty).set_name("a").as_key();
	let b = f.append_param(fty).set_name("b").as_key();
	f.set_return_ty(bool);

	block!(f, entry {
		f.param_ref(a);
		f.load();
		f.param_ref(b);
		f.load();
		f.binary_op(Eq);
		f.ret();
	});

	let ucompare_fn_ptr = f.finalize().map(FunctionManipulator::into_key).unwrap_rich(&builder.ctx);


	let mut f = builder.create_function();

	f.set_name("r32_eq");
	let a = f.append_param(r32).set_name("a").as_key();
	let b = f.append_param(r32).set_name("b").as_key();
	f.set_return_ty(bool);

	block!(f, entry {
		f.param_ref(a);
		f.load();
		f.param_ref(b);
		f.load();
		f.binary_op(Eq);
		f.ret();
	});

	let ur32_eq = f.finalize().map(FunctionManipulator::into_key).unwrap_rich(&builder.ctx);


	let mut f = builder.create_function();

	f.set_name("r32_ne");
	let a = f.append_param(r32).set_name("a").as_key();
	let b = f.append_param(r32).set_name("b").as_key();
	f.set_return_ty(bool);

	block!(f, entry {
		f.param_ref(a);
		f.load();
		f.param_ref(b);
		f.load();
		f.binary_op(Ne);
		f.ret();
	});

	let ur32_ne = f.finalize().map(FunctionManipulator::into_key).unwrap_rich(&builder.ctx);



	let mut f = builder.create_function();

	f.set_name("exec");
	f.set_return_ty(bool);

	block!(f, entry {
		f.function_ref(ur32_eq);
		f.function_ref(ur32_ne);
		f.function_ref(ucompare_fn_ptr);
		f.call();
		f.ret();
	});

	let uexec = f.finalize().map(FunctionManipulator::into_key).unwrap_rich(&builder.ctx);




	let pstate = PrinterState::new(&context);
	let mut emitter = Emitter::new(&context).unwrap();

	for &ufunction in [
		ucompare_fn_ptr,
		ur32_eq,
		ur32_ne,
		uexec,
	].iter() {
		let llfunction = emitter.emit_function(ufunction);

		println!("{}", pstate.print_function(ufunction));
		println!("{:#?}", llfunction);

		llfunction.verify_function(LLVMAbortProcessAction);
	}



	let mut jit = Jit::new(&mut emitter);

	let exec = jit.get_function(llvm_str!("exec"));
	assert!(!exec.is_null());
	let exec: extern "C" fn () -> bool = unsafe { std::mem::transmute(exec) };

	assert_eq!(exec(), false);


	let compare_fn_ptr = jit.get_function(llvm_str!("compare_fn_ptr"));
	assert!(!compare_fn_ptr.is_null());
	type FnTy = extern "C" fn (f32, f32) -> bool;

	let compare_fn_ptr: extern "C" fn (FnTy, FnTy) -> bool = unsafe { std::mem::transmute(compare_fn_ptr) };

	extern "C" fn ne (x: f32, y: f32) -> bool { x != y }
	extern "C" fn eq (x: f32, y: f32) -> bool { x == y }

	assert_eq!(dbg!(compare_fn_ptr(ne, eq)), false);
	assert_eq!(dbg!(compare_fn_ptr(ne, ne)), true);
	assert_eq!(dbg!(compare_fn_ptr(eq, eq)), true);
}





#[test]
fn get_set_element () {
	let mut context = Context::with_target(target::AMD64);
	let mut builder = Builder::new(&mut context);
	let mut f = FunctionBuilder::new(&mut builder);

	let r32 = f.real32_ty().as_key();

	let v2f = structure_ty!(f, v2f {
		r32, r32,
	}).as_key();

	f.set_name("v2f_mul");

	let a = f.append_param(v2f).set_name("a").as_key();
	let b = f.append_param(v2f).set_name("b").as_key();

	f.set_return_ty(v2f);

	block!(f, entry {
		f.constant(Constant::Aggregate(v2f, ConstantAggregateData::Zeroed));

		f.param_ref(a);
		f.load();
		f.duplicate(0);

		f.get_element(0).set_name("a.0");

		f.param_ref(b);
		f.load();
		f.duplicate(0);

		f.get_element(0).set_name("b.0");
		f.swap(1);
		f.swap(2);
		f.swap(1);

		f.binary_op(Add).set_name("a.0+b.0");
		f.swap(1);
		f.swap(3);
		f.swap(1);

		f.set_element(0).set_name("ret_val");
		f.swap(2);
		f.swap(1);

		f.get_element(1).set_name("a.1");
		f.swap(1);
		f.get_element(1).set_name("b.1");
		f.binary_op(Add).set_name("a.1+b.1");

		f.set_element(1).set_name("ret_val");

		f.ret();
	});

	let function = f.finalize().map(FunctionManipulator::into_key).unwrap_rich(&context);

	let pstate = PrinterState::new(&context);
	println!("{}\n{}", pstate.print_ty(v2f), pstate.print_function(function));

	let mut emitter = Emitter::new(&context).unwrap();
	let llv2f = emitter.emit_ty(v2f);
	let llfunction = emitter.emit_function(function);

	println!("{:#?}\n{:#?}", llv2f, llfunction);

	llfunction.verify_function(LLVMAbortProcessAction);
}


#[test]
fn optimize_get_set_element () {
	let mut context = Context::with_target(target::AMD64);
	let mut builder = Builder::new(&mut context);
	let mut f = FunctionBuilder::new(&mut builder);

	let r32 = f.real32_ty().as_key();

	let v2f = structure_ty!(f, v2f {
		r32, r32,
	}).as_key();

	f.set_name("v2f_mul");

	let a = f.append_param(v2f).set_name("a").as_key();
	let b = f.append_param(v2f).set_name("b").as_key();

	f.set_return_ty(v2f);

	block!(f, entry {
		f.constant(Constant::Aggregate(v2f, ConstantAggregateData::Zeroed));

		f.param_ref(a);
		f.load();
		f.duplicate(0);

		f.get_element(0).set_name("a.0");

		f.param_ref(b);
		f.load();
		f.duplicate(0);

		f.get_element(0).set_name("b.0");
		f.swap(1);
		f.swap(2);
		f.swap(1);

		f.binary_op(Add).set_name("a.0+b.0");
		f.swap(1);
		f.swap(3);
		f.swap(1);

		f.set_element(0).set_name("ret_val");
		f.swap(2);
		f.swap(1);

		f.get_element(1).set_name("a.1");
		f.swap(1);
		f.get_element(1).set_name("b.1");
		f.binary_op(Add).set_name("a.1+b.1");

		f.set_element(1).set_name("ret_val");

		f.ret();
	});

	let function = f.finalize().map(FunctionManipulator::into_key).unwrap_rich(&context);

	let pstate = PrinterState::new(&context);
	println!("{}\n{}", pstate.print_ty(v2f), pstate.print_function(function));

	let mut emitter = Emitter::new(&context).unwrap();
	let llv2f = emitter.emit_ty(v2f);
	let llfunction = emitter.emit_function(function);
	println!("{:#?}\n{:#?}", llv2f, llfunction);
	llfunction.verify_function(LLVMAbortProcessAction);

	let mut optimizer = Optimizer::with_level(&emitter, 3);
	assert!(optimizer.optimize(llfunction), "failed to optimize");
	println!("optimized ir:\n{:#?}", llfunction);
}


#[test]
fn fib () {
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
		 .set_name("fib_n-1");

		f.param_ref(n);
		f.load();
		f.const_sint32(2);
		f.binary_op(Sub)
		 .set_name("n-2");
		f.function_ref(fib);
		f.call()
		 .set_name("fib_n-2");

		f.binary_op(Add);

		f.branch(end);
	});

	with_block!(f, end => {
		f.phi(s32t)
		 .set_name("result");

		f.ret();
	});

	let function = f.finalize().map(FunctionManipulator::into_key).unwrap_rich(&context);
	println!("{}", PrinterState::new(&context).print_function(function));


	let mut emitter = Emitter::new(&context).unwrap();
	let llfunc = emitter.emit_function(function);
	println!("{:?}", llfunc);

	llfunc.verify_function(LLVMAbortProcessAction);
}


#[test]
fn jit_fib () {
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
		 .set_name("fib_n-1");

		f.param_ref(n);
		f.load();
		f.const_sint32(2);
		f.binary_op(Sub)
		 .set_name("n-2");
		f.function_ref(fib);
		f.call()
		 .set_name("fib_n-2");

		f.binary_op(Add)
		 .set_name("sum");

		f.branch(end);
	});

	with_block!(f, end => {
		f.phi(s32t)
		 .set_name("result");

		f.ret();
	});

	let function = f.finalize().map(FunctionManipulator::into_key).unwrap_rich(&context);
	println!("{}", PrinterState::new(&context).print_function(function));


	let mut emitter = Emitter::new(&context).unwrap();
	let llfunction = emitter.emit_function(function);
	println!("{:?}", llfunction);
	llfunction.verify_function(LLVMAbortProcessAction);

	let mut optimizer = Optimizer::with_level(&emitter, 3);
	assert!(optimizer.optimize(llfunction), "failed to optimize");
	println!("optimized ir:\n{:#?}", llfunction);

	let mut jit = Jit::new(&mut emitter);

	let fib = jit.get_function(llvm_str!("fib"));
	assert!(fib != std::ptr::null(), "Failed to compile function");
	let fib = unsafe { std::mem::transmute::<_, extern "C" fn (i32) -> i32>(fib) };

	fn nat_fib (n: i32) -> i32 {
		if n < 2 { n }
		else { nat_fib(n-1) + nat_fib(n-2) }
	}

	let n = 17;
	let t = nat_fib(n);
	let x = fib(n);


	println!("nat_fib({}) = {}", n, t);
	println!("fib({}) = {}", n, x);
	assert_eq!(t, x);
}


#[test]
fn structures () {
	// let ir_path = get_log_path("structures.ir");
	// let llpath = get_log_path("structures.ll");

	let mut context = Context::with_target(target::AMD64);
	let mut builder = Builder::new(&mut context);


	// TODO: test smaller values
	// let s8  = builder.sint8_ty().as_key();
	// let s16 = builder.sint16_ty().as_key();
	let s32 = builder.sint32_ty().as_key();
	let s64 = builder.sint64_ty().as_key();
	let r32 = builder.real32_ty().as_key();
	let r64 = builder.real64_ty().as_key();


	let s32x2 = structure_ty!(builder, "s32x2" => {
		s32, s32
	}).as_key();

	let s32x4  = structure_ty!(builder, "s32x4" => {
		s32, s32, s32, s32
	}).as_key();

	let s32x8  = structure_ty!(builder, "s32x8" => {
		s32, s32, s32, s32, s32, s32, s32, s32
	}).as_key();


	let s64x2 = structure_ty!(builder, "s64x2" => {
		s64, s64
	}).as_key();

	let s64x4  = structure_ty!(builder, "s64x4" => {
		s64, s64, s64, s64
	}).as_key();

	let s64x8  = structure_ty!(builder, "s64x8" => {
		s64, s64, s64, s64, s64, s64, s64, s64
	}).as_key();


	let r32x2 = structure_ty!(builder, "r32x2" => {
		r32, r32
	}).as_key();

	let r32x4  = structure_ty!(builder, "r32x4" => {
		r32, r32, r32, r32
	}).as_key();

	let r32x8  = structure_ty!(builder, "r32x8" => {
		r32, r32, r32, r32, r32, r32, r32, r32
	}).as_key();


	let r64x2 = structure_ty!(builder, "r64x2" => {
		r64, r64
	}).as_key();

	let r64x4  = structure_ty!(builder, "r64x4" => {
		r64, r64, r64, r64
	}).as_key();

	let r64x8  = structure_ty!(builder, "r64x8" => {
		r64, r64, r64, r64, r64, r64, r64, r64
	}).as_key();


	let const_s32x2 = aggregate_const!(s32x2 => Complete {
		1i32, 2i32,
	});

	let const_s32x4 = aggregate_const!(s32x4 => Complete {
		1i32, 3i32, 3i32, 7i32,
	});

	let const_s32x8 = aggregate_const!(s32x8 => Complete {
		4i32, 3i32, 2i32, 1i32, 9i32, 8i32, 7i32, 6i32,
	});


	let const_s64x2 = aggregate_const!(s64x2 => Complete {
		1i64, 2i64,
	});

	let const_s64x4 = aggregate_const!(s64x4 => Complete {
		1i64, 3i64, 3i64, 7i64,
	});

	let const_s64x8 = aggregate_const!(s64x8 => Complete {
		4i64, 3i64, 2i64, 1i64, 9i64, 8i64, 7i64, 6i64,
	});


	let const_r32x2 = aggregate_const!(r32x2 => Complete {
		1f32, 2f32,
	});

	let const_r32x4 = aggregate_const!(r32x4 => Complete {
		1f32, 3f32, 3f32, 7f32,
	});

	let const_r32x8 = aggregate_const!(r32x8 => Complete {
		4f32, 3f32, 2f32, 1f32, 9f32, 8f32, 7f32, 6f32,
	});


	let const_r64x2 = aggregate_const!(r64x2 => Complete {
		1f64, 2f64,
	});

	let const_r64x4 = aggregate_const!(r64x4 => Complete {
		1f64, 3f64, 3f64, 7f64,
	});

	let const_r64x8 = aggregate_const!(r64x8 => Complete {
		4f64, 3f64, 2f64, 1f64, 9f64, 8f64, 7f64, 6f64,
	});


	let global_s32x2 = builder.create_global(s32x2, Some(const_s32x2)).map(into_key).unwrap_rich(builder.ctx);
	let global_s32x4 = builder.create_global(s32x4, Some(const_s32x4)).map(into_key).unwrap_rich(builder.ctx);
	let global_s32x8 = builder.create_global(s32x8, Some(const_s32x8)).map(into_key).unwrap_rich(builder.ctx);

	let global_s64x2 = builder.create_global(s64x2, Some(const_s64x2)).map(into_key).unwrap_rich(builder.ctx);
	let global_s64x4 = builder.create_global(s64x4, Some(const_s64x4)).map(into_key).unwrap_rich(builder.ctx);
	let global_s64x8 = builder.create_global(s64x8, Some(const_s64x8)).map(into_key).unwrap_rich(builder.ctx);

	let global_r32x2 = builder.create_global(r32x2, Some(const_r32x2)).map(into_key).unwrap_rich(builder.ctx);
	let global_r32x4 = builder.create_global(r32x4, Some(const_r32x4)).map(into_key).unwrap_rich(builder.ctx);
	let global_r32x8 = builder.create_global(r32x8, Some(const_r32x8)).map(into_key).unwrap_rich(builder.ctx);

	let global_r64x2 = builder.create_global(r64x2, Some(const_r64x2)).map(into_key).unwrap_rich(builder.ctx);
	let global_r64x4 = builder.create_global(r64x4, Some(const_r64x4)).map(into_key).unwrap_rich(builder.ctx);
	let global_r64x8 = builder.create_global(r64x8, Some(const_r64x8)).map(into_key).unwrap_rich(builder.ctx);

	// let ir_src = std::fs::File::create(ir_path).unwrap();
	println!("{}", PrinterState::new(&builder.ctx).print_self());

	{
		let mut emitter = Emitter::new(&builder.ctx).unwrap();

		emitter.emit_global(global_s32x2);
		emitter.emit_global(global_s32x4);
		emitter.emit_global(global_s32x8);

		emitter.emit_global(global_s64x2);
		emitter.emit_global(global_s64x4);
		emitter.emit_global(global_s64x8);

		emitter.emit_global(global_r32x2);
		emitter.emit_global(global_r32x4);
		emitter.emit_global(global_r32x8);

		emitter.emit_global(global_r64x2);
		emitter.emit_global(global_r64x4);
		emitter.emit_global(global_r64x8);

		// let llsrc = std::fs::File::create(llpath).unwrap();
		println!( "{}", emitter.ll);
	}


	for &ty in &[
		s32x2, s32x4, s32x8,
		s64x2, s64x4, s64x8,
		r32x2, r32x4, r32x8,
		r64x2, r64x4, r64x8,
	] {
		let mut f = builder.create_function();

		let fn_name = format!("returns_{}", f.get_ty(ty).unwrap().into_ref().name.as_deref().unwrap_or("anon"));
		f.set_name(fn_name);
		// f.append_param(ty);
		f.set_return_ty(ty);

		block!(f, "entry" {
			if let TyData::Structure { field_tys } = &f.get_ty(ty).unwrap().data {
				let field_tys = field_tys.clone(); // TODO: this really is a borrow checker fail, but is there any way to make this better?

				for (i, &field_ty) in field_tys.iter().enumerate() {
					let value = f.get_ty(field_ty).unwrap().const_from_int(i).unwrap();

					f.constant(value);
				}
			} else { unreachable!() }

			f.build_aggregate(ty, AggregateData::Complete);
			f.ret();
		});


		let BuilderResult { value: function, error } = f.finalize().map(FunctionManipulator::into_key);

		let printer = PrinterState::new(&builder.ctx).with_possible_error(error);

		println!("{}\n{}", printer.print_ty(ty), printer.print_function(function));

		let mut emitter = Emitter::new(&builder.ctx).unwrap();
		let llfunction = emitter.emit_function(function);

		println!("{:#?}\n{:#?}", emitter.emit_ty(ty), llfunction);

		llfunction.verify_function(LLVMAbortProcessAction);
	}


	for &ty in &[
		s32x2, s32x4, s32x8,
		s64x2, s64x4, s64x8,
		r32x2, r32x4, r32x8,
		r64x2, r64x4, r64x8,
	] {
		let mut f = builder.create_function();

		let fn_name = format!("{}_product", f.get_ty(ty).unwrap().into_ref().name.as_deref().unwrap_or("anon"));
		f.set_name(fn_name);
		let param = f.append_param(ty).as_key();

		block!(f, "entry" {
			if let TyData::Structure { field_tys } = &f.get_ty(ty).unwrap().data {
				let mut field_tys = field_tys.clone(); // TODO: this really is a borrow checker fail, but is there any way to make this better?

				let first = field_tys.remove(0);
				f.set_return_ty(first);

				f.param_ref(param);
				f.const_uint32(0);
				f.const_uint32(0);
				f.gep(2);
				f.load();

				for (i, _) in field_tys.into_iter().enumerate() {
					f.param_ref(param);
					f.const_uint32(0);
					f.const_uint32(i as u32 + 1);
					f.gep(2);
					f.load();

					f.binary_op(BinaryOp::Mul);
				}
			} else { unreachable!() }

			f.ret();
		});


		let BuilderResult { value: function, error } = f.finalize().map(FunctionManipulator::into_key);

		let printer = PrinterState::new(&builder.ctx).with_possible_error(error);

		println!("{}\n{}", printer.print_ty(ty), printer.print_function(function));

		let mut emitter = Emitter::new(&builder.ctx).unwrap();
		let llfunction = emitter.emit_function(function);

		println!("{:#?}\n{:#?}", emitter.emit_ty(ty), llfunction);

		llfunction.verify_function(LLVMAbortProcessAction);
	}
}




#[test]
fn structures_jit () {
	let mut context = Context::with_target(target::AMD64);
	let mut builder = Builder::new(&mut context);

	let r32 = builder.real32_ty().as_key();
	let r64 = builder.real64_ty().as_key();


	let r32x2 = structure_ty!(builder, "r32x2" => {
		r32, r32
	}).as_key();

	let r32x4  = structure_ty!(builder, "r32x4" => {
		r32, r32, r32, r32
	}).as_key();

	let r32x8  = structure_ty!(builder, "r32x8" => {
		r32, r32, r32, r32, r32, r32, r32, r32
	}).as_key();


	let r64x2 = structure_ty!(builder, "r64x2" => {
		r64, r64
	}).as_key();

	let r64x4  = structure_ty!(builder, "r64x4" => {
		r64, r64, r64, r64
	}).as_key();

	let r64x8  = structure_ty!(builder, "r64x8" => {
		r64, r64, r64, r64, r64, r64, r64, r64
	}).as_key();



	#[repr(C)]
	#[derive(Debug, PartialEq, Clone, Copy)]
	#[allow(non_camel_case_types)]
	struct r32x2 {
		x: f32,
		y: f32,
	}

	#[repr(C)]
	#[derive(Debug, PartialEq, Clone, Copy)]
	#[allow(non_camel_case_types)]
	struct r32x4 {
		x: f32,
		y: f32,
		z: f32,
		w: f32,
	}

	#[repr(C)]
	#[derive(Debug, PartialEq, Clone, Copy)]
	#[allow(non_camel_case_types)]
	struct r32x8 {
		x0: f32,
		y0: f32,
		z0: f32,
		w0: f32,
		x1: f32,
		y1: f32,
		z1: f32,
		w1: f32,
	}

	#[repr(C)]
	#[derive(Debug, PartialEq, Clone, Copy)]
	#[allow(non_camel_case_types)]
	struct r64x2 {
		x: f64,
		y: f64,
	}

	#[repr(C)]
	#[derive(Debug, PartialEq, Clone, Copy)]
	#[allow(non_camel_case_types)]
	struct r64x4 {
		x: f64,
		y: f64,
		z: f64,
		w: f64,
	}

	#[repr(C)]
	#[derive(Debug, PartialEq, Clone, Copy)]
	#[allow(non_camel_case_types)]
	struct r64x8 {
		x0: f64,
		y0: f64,
		z0: f64,
		w0: f64,
		x1: f64,
		y1: f64,
		z1: f64,
		w1: f64,
	}



	let mut ret_tests = HashMap::<TyKey, fn (*const())>::new();

	ret_tests.insert(r32x2, |func| {
		let func: extern "C" fn () -> r32x2 = unsafe { std::mem::transmute(func) };

		assert_eq!(dbg!(func()), r32x2 { x: 0., y: 1. });
	});

	ret_tests.insert(r32x4, |func| {
		let func: extern "C" fn () -> r32x4 = unsafe { std::mem::transmute(func) };

		assert_eq!(dbg!(func()), r32x4 { x: 0., y: 1., z: 2., w: 3. });
	});

	ret_tests.insert(r32x8, |func| {
		let func: extern "C" fn () -> r32x8 = unsafe { std::mem::transmute(func) };

		assert_eq!(dbg!(func()), r32x8 { x0: 0., y0: 1., z0: 2., w0: 3., x1: 4., y1: 5., z1: 6., w1: 7. });
	});


	ret_tests.insert(r64x2, |func| {
		let func: extern "C" fn () -> r64x2 = unsafe { std::mem::transmute(func) };

		assert_eq!(dbg!(func()), r64x2 { x: 0., y: 1. });
	});

	ret_tests.insert(r64x4, |func| {
		let func: extern "C" fn () -> r64x4 = unsafe { std::mem::transmute(func) };

		assert_eq!(dbg!(func()), r64x4 { x: 0., y: 1., z: 2., w: 3. });
	});

	ret_tests.insert(r64x8, |func| {
		let func: extern "C" fn () -> r64x8 = unsafe { std::mem::transmute(func) };

		assert_eq!(dbg!(func()), r64x8 { x0: 0., y0: 1., z0: 2., w0: 3., x1: 4., y1: 5., z1: 6., w1: 7. });
	});

	for &ty in &[
		r32x2, r32x4, r32x8,
		r64x2, r64x4, r64x8,
	] {
		let mut f = builder.create_function();

		let fn_name = format!("returns_{}", f.get_ty(ty).unwrap().into_ref().name.as_deref().unwrap_or("anon"));

		f.set_name(&fn_name);
		f.set_return_ty(ty);

		block!(f, "entry" {
			if let TyData::Structure { field_tys } = &f.get_ty(ty).unwrap().data {
				let field_tys = field_tys.clone(); // TODO: this really is a borrow checker fail, but is there any way to make this better?

				for (i, &field_ty) in field_tys.iter().enumerate() {
					let value = f.get_ty(field_ty).unwrap().const_from_int(i).unwrap();

					f.constant(value);
				}
			} else { unreachable!() }

			f.build_aggregate(ty, AggregateData::Complete);
			f.ret();
		});


		let BuilderResult { value: function, error } = f.finalize().map(FunctionManipulator::into_key);

		let printer = PrinterState::new(&builder.ctx).with_possible_error(error);

		println!("{}\n{}", printer.print_ty(ty), printer.print_function(function));

		let mut emitter = Emitter::new(&builder.ctx).unwrap();
		let llfunction = emitter.emit_function(function);

		println!("{:#?}\n{:#?}", emitter.emit_ty(ty), llfunction);

		llfunction.verify_function(LLVMAbortProcessAction);

		let mut optimizer = Optimizer::with_level(&emitter, 3);

		optimizer.optimize(llfunction);
		println!("optimized ir:\n{:#?}", optimizer.module().inner());


		let mut jit = Jit::new(&mut emitter);

		let llfn_name = LLVMString::from(fn_name);
		let func = jit.get_function(llfn_name);
		assert!(!func.is_null());
		ret_tests[&ty](func);
	}


	let mut ret_tests = HashMap::<TyKey, fn (*const())>::new();

	#[allow(clippy::float_cmp)] {
		ret_tests.insert(r32x2, |func| {
			type FnTy = extern "C" fn (r32x2) -> f32;

			let func: FnTy = unsafe { std::mem::transmute(func) };

			let input = r32x2 { x: 2., y: 3. };

			let nat_func = |v: r32x2| -> f32 { v.x * v.y };

			let func_output = func(input);
			let nat_func_output = nat_func(input);

			println!("input: {:?}", input);
			println!("uir:\t{}", func_output);
			println!("nat:\t{}", nat_func_output);

			assert_eq!(func_output, nat_func_output);
		});

		ret_tests.insert(r32x4, |func| {
			type FnTy = extern "C" fn (r32x4) -> f32;

			let func: FnTy = unsafe { std::mem::transmute(func) };

			let input = r32x4 { x: 2., y: 3., z: 4., w: 5. };

			let nat_func = |v: r32x4| -> f32 { v.x * v.y * v.z * v.w };

			let func_output = func(input);
			let nat_func_output = nat_func(input);

			println!("input: {:?}", input);
			println!("uir:\t{}", func_output);
			println!("nat:\t{}", nat_func_output);

			assert_eq!(func_output, nat_func_output);
		});

		ret_tests.insert(r32x8, |func| {
			type FnTy = extern "C" fn (r32x8) -> f32;

			let func: FnTy = unsafe { std::mem::transmute(func) };

			let input = r32x8 { x0: 2., y0: 3., z0: 4., w0: 5., x1: 6., y1: 7., z1: 8., w1: 9. };

			let nat_func = |v: r32x8| -> f32 { v.x0 * v.y0 * v.z0 * v.w0 * v.x1 * v.y1 * v.z1 * v.w1 };

			let func_output = func(input);
			let nat_func_output = nat_func(input);

			println!("input: {:?}", input);
			println!("uir:\t{}", func_output);
			println!("nat:\t{}", nat_func_output);

			assert_eq!(func_output, nat_func_output);
		});


		ret_tests.insert(r64x2, |func| {
			type FnTy = extern "C" fn (r64x2) -> f64;

			let func: FnTy = unsafe { std::mem::transmute(func) };

			let input = r64x2 { x: 2., y: 3. };

			let nat_func = |v: r64x2| -> f64 { v.x * v.y };

			let func_output = func(input);
			let nat_func_output = nat_func(input);

			println!("input: {:?}", input);
			println!("uir:\t{}", func_output);
			println!("nat:\t{}", nat_func_output);

			assert_eq!(func_output, nat_func_output);
		});

		ret_tests.insert(r64x4, |func| {
			type FnTy = extern "C" fn (r64x4) -> f64;

			let func: FnTy = unsafe { std::mem::transmute(func) };

			let input = r64x4 { x: 2., y: 3., z: 4., w: 5. };

			let nat_func = |v: r64x4| -> f64 { v.x * v.y * v.z * v.w };

			let func_output = func(input);
			let nat_func_output = nat_func(input);

			println!("input: {:?}", input);
			println!("uir:\t{}", func_output);
			println!("nat:\t{}", nat_func_output);

			assert_eq!(func_output, nat_func_output);
		});

		ret_tests.insert(r64x8, |func| {
			type FnTy = extern "C" fn (r64x8) -> f64;

			let func: FnTy = unsafe { std::mem::transmute(func) };

			let input = r64x8 { x0: 2., y0: 3., z0: 4., w0: 5., x1: 6., y1: 7., z1: 8., w1: 9. };

			let nat_func = |v: r64x8| -> f64 { v.x0 * v.y0 * v.z0 * v.w0 * v.x1 * v.y1 * v.z1 * v.w1 };

			let func_output = func(input);
			let nat_func_output = nat_func(input);

			println!("input: {:?}", input);
			println!("uir:\t{}", func_output);
			println!("nat:\t{}", nat_func_output);

			assert_eq!(func_output, nat_func_output);
		});
	}



	for &ty in &[
		r32x2, r32x4, r32x8,
		r64x2, r64x4, r64x8,
	] {
		let mut f = builder.create_function();

		let fn_name = format!("{}_product", f.get_ty(ty).unwrap().into_ref().name.as_deref().unwrap_or("anon"));
		f.set_name(&fn_name);
		let param = f.append_param(ty).as_key();

		block!(f, "entry" {
			if let TyData::Structure { field_tys } = &f.get_ty(ty).unwrap().data {
				let mut field_tys = field_tys.clone(); // TODO: this really is a borrow checker fail, but is there any way to make this better?

				let first = field_tys.remove(0);
				f.set_return_ty(first);

				f.param_ref(param);
				f.const_uint32(0);
				f.const_uint32(0);
				f.gep(2);
				f.load();

				for (i, _) in field_tys.into_iter().enumerate() {
					f.param_ref(param);
					f.const_uint32(0);
					f.const_uint32(i as u32 + 1);
					f.gep(2);
					f.load();

					f.binary_op(BinaryOp::Mul);
				}
			} else { unreachable!() }

			f.ret();
		});


		let BuilderResult { value: function, error } = f.finalize().map(FunctionManipulator::into_key);

		let printer = PrinterState::new(&builder.ctx).with_possible_error(error);

		println!("{}\n{}", printer.print_ty(ty), printer.print_function(function));

		let mut emitter = Emitter::new(&builder.ctx).unwrap();
		let llfunction = emitter.emit_function(function);

		println!("{:#?}\n{:#?}", emitter.emit_ty(ty), llfunction);

		llfunction.verify_function(LLVMAbortProcessAction);


		let mut optimizer = Optimizer::with_level(&emitter, 3);
		optimizer.optimize(llfunction);
		println!("optimized ir:");
		// unsafe { LLVMDumpModule(optimizer.module().inner()) }

		if let Some(ret_test) = ret_tests.get(&ty) {
			let mut jit = Jit::new(&mut emitter);

			let llfn_name = LLVMString::from(fn_name);
			let func = jit.get_function(llfn_name);
			assert!(!func.is_null());
			ret_test(func);
		} else {
			println!("SKIPPING TEST");
		}
	}
}



// #[test]
// fn hacky_abi_test () {

//     use uir_core::{builder, ir, support::slotmap::AsKey};

// 	macro_rules! build_c_abi_str {
// 		(%MAIN% $name:ident ($( $field_name:ident : $field_ty:ident ),*)) => {
// 			concat!("int main () {\n",
// 				"\tint $counter = 0;\n",
// 				$( "\t",stringify!($field_ty)," ",stringify!($field_name)," = (",stringify!($field_ty),") ++$counter;\n", )*
// 				"\tfn_direct_",stringify!($name),"(",stringify!($($field_name),*),");\n",
// 				"\tfn_struct_",stringify!($name),"((",stringify!($name),") { ",stringify!($($field_name),*)," });\n",
// 				"\treturn 0;\n",
// 			"}\n")
// 		};
// 		(%BASE%) => {
// r#"typedef void void_ty;
// typedef char bool;
// typedef float real32_ty;
// typedef double real64_ty;
// typedef char sint8_ty;
// typedef short sint16_ty;
// typedef int sint32_ty;
// typedef long sint64_ty;
// typedef unsigned char uint8_ty;
// typedef unsigned short uint16_ty;
// typedef unsigned int uint32_ty;
// typedef unsigned long uint64_ty;
// "#
// 		};
// 		( $name:ident ($( $field_name:ident : $field_ty:ident ),*) ) => {
// 			concat!(
// 				build_c_abi_str!(%BASE%),
// 				"typedef struct {\n",
// 					$( "\t",stringify!($field_ty)," ",stringify!($field_name),";\n", )*
// 				"} ", stringify!($name),";\n",
// 				"extern ",build_c_abi_str!(%GET_TY% $name ($($field_name)*))," fn_direct_",stringify!($name),"(",stringify!($($field_ty),*),");\n",
// 				"extern ",stringify!($name)," fn_struct_",stringify!($name), "(", stringify!($name), ");\n",
// 				build_c_abi_str!(%MAIN% $name ($( $field_name : $field_ty ),*))
// 			)
// 		};

// 		(%GET_TY% $struct_name:ident ()) => { "void" };
// 		(%GET_TY% $struct_name:ident ($single:ident)) => { stringify!($single) };
// 		(%GET_TY% $struct_name:ident ($first:ident $($more:ident)+)) => { stringify!($struct_name) };
// 	}

// 	macro_rules! build_abi_tests {
// 		( $(
// 			$name:ident ($( $field_name:ident : $field_ty:ident ),*)
// 		)* ) => { {
// 			$( {
// 				let mut ctx = ir::Context::new();
// 				let mut builder = builder::Builder::new(&mut ctx);

// 				let tys = &[ 	$( builder.$field_ty().as_key() ),* ];
// 				let struct_ty = builder.structure_ty(tys.to_vec()).unwrap().set_name(stringify!($name)).as_key();

// 				let struct_function_ty = builder.function_ty(vec! [ struct_ty ], Some(struct_ty)).unwrap().as_key();
// 				let mut emitter = Emitter::new(&ctx).unwrap();

// 				let ll_struct_function_user_ty = emitter.emit_ty(struct_function_ty);
// 				let struct_function_abi = emitter.abi_info(ll_struct_function_user_ty);
// 				let ll_struct_function_ty = struct_function_abi.lltype;

// 				let ll_struct_function = LLVMValue::create_function(emitter.module.inner(), ll_struct_function_ty, llvm_str!(concat!("fn_struct_", stringify!($name))));
// 				struct_function_abi.apply_attributes(emitter.ll.ctx, ll_struct_function);

// 				let ll_mod = llvm_from_c(build_c_abi_str!($name ($( $field_name : $field_ty ),*)));

// 				let truth_ll_struct_function = LLVMValue::get_function(ll_mod, llvm_str!(concat!("fn_struct_", stringify!($name))));
// 				let truth_ll_struct_function_ty = LLVMType::of(truth_ll_struct_function);

// 				println!("struct abi: {:#?}", struct_function_abi);
// 				println!();
// 				println!("got: {:#?}\nexpected: {:#?}", ll_struct_function, truth_ll_struct_function);
// 				println!();
// 				println!("got: {}\nexpected: {}", ll_struct_function_ty, truth_ll_struct_function_ty);
// 				assert!(truth_ll_struct_function_ty.equivalent(ll_struct_function_ty));
// 			} )*
// 		} };
// 	}



// 	fn build_abi_tests () {
// 		build_abi_tests! {
// 			i32_2(x: sint32_ty, y: sint32_ty)
// 			i64_2(x: sint64_ty, y: sint64_ty)
// 			i32_4(x: sint32_ty, y: sint32_ty, z: sint32_ty, w: sint32_ty)
// 			i64_4(x: sint64_ty, y: sint64_ty, z: sint64_ty, w: sint64_ty)
// 			i32_i16(x: sint32_ty, y: sint16_ty)
// 			i16_i32(x: sint16_ty, y: sint32_ty)
// 			i16_4(x: sint16_ty, y: sint16_ty, z: sint16_ty, w: sint16_ty)
// 			i16_8(x0: sint16_ty, y0: sint16_ty, z0: sint16_ty, w0: sint16_ty, x1: sint16_ty, y1: sint16_ty, z1: sint16_ty, w1: sint16_ty)
// 			f32_2(x: real32_ty, y: real32_ty)
// 			f32_4(x: real32_ty, y: real32_ty, z: real32_ty, w: real32_ty)
// 			f64_2(x: real64_ty, y: real64_ty)
// 			f64_4(x: real64_ty, y: real64_ty, z: real32_ty, w: real32_ty)
// 		}
// 	}

// 	build_abi_tests()
// }