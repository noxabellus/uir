use llvm_sys::analysis::{LLVMVerifierFailureAction::*};

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

	let mut optimizer = Optimizer::with_level(&mut emitter, 3);
	assert!(optimizer.optimize(llfunction), "failed to optimize");
	println!("optimized ir:\n{:#?}", llfunction);
}


#[test]
fn fib () -> IrResult {
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


	Ok(())
}


#[test]
#[cfg(feature = "jit")]
fn jit_fib () -> IrResult {
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
	};

	let n = 17;
	let t = nat_fib(n);
	let x = fib(n);


	println!("nat_fib({}) = {}", n, t);
	println!("fib({}) = {}", n, x);
	assert_eq!(t, x);

	Ok(())
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

					f.binary_op(BinaryOp::Add);
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
fn hacky_abi_test () {

	use llvm_sys::bit_reader::LLVMParseBitcodeInContext2;
    use uir_core::{builder, ir, support::slotmap::AsKey};

	macro_rules! build_c_abi_str {
		(%MAIN% $name:ident ($( $field_name:ident : $field_ty:ident ),*)) => {
			concat!("int main () {\n",
				"\tint $counter = 0;\n",
				$( "\t",stringify!($field_ty)," ",stringify!($field_name)," = (",stringify!($field_ty),") ++$counter;\n", )*
				"\tfn_direct_",stringify!($name),"(",stringify!($($field_name),*),");\n",
				"\tfn_struct_",stringify!($name),"((",stringify!($name),") { ",stringify!($($field_name),*)," });\n",
				"\treturn 0;\n",
			"}\n")
		};
		(%BASE%) => {
r#"typedef void void_ty;
typedef char bool;
typedef float real32_ty;
typedef double real64_ty;
typedef char sint8_ty;
typedef short sint16_ty;
typedef int sint32_ty;
typedef long sint64_ty;
typedef unsigned char uint8_ty;
typedef unsigned short uint16_ty;
typedef unsigned int uint32_ty;
typedef unsigned long uint64_ty;
"#
		};
		( $name:ident ($( $field_name:ident : $field_ty:ident ),*) ) => {
			concat!(
				build_c_abi_str!(%BASE%),
				"typedef struct {\n",
					$( "\t",stringify!($field_ty)," ",stringify!($field_name),";\n", )*
				"} ", stringify!($name),";\n",
				"extern ",build_c_abi_str!(%GET_TY% $name ($($field_name)*))," fn_direct_",stringify!($name),"(",stringify!($($field_ty),*),");\n",
				"extern ",stringify!($name)," fn_struct_",stringify!($name), "(", stringify!($name), ");\n",
				build_c_abi_str!(%MAIN% $name ($( $field_name : $field_ty ),*))
			)
		};

		(%GET_TY% $struct_name:ident ()) => { "void" };
		(%GET_TY% $struct_name:ident ($single:ident)) => { stringify!($single) };
		(%GET_TY% $struct_name:ident ($first:ident $($more:ident)+)) => { stringify!($struct_name) };
	}

	macro_rules! build_abi_tests {
		( $(
			$name:ident ($( $field_name:ident : $field_ty:ident ),*)
		)* ) => { {
			$( {
				let mut ctx = ir::Context::new();
				let mut builder = builder::Builder::new(&mut ctx);

				let tys = &[ 	$( builder.$field_ty().as_key() ),* ];
				let struct_ty = builder.structure_ty(tys.to_vec()).unwrap().set_name(stringify!($name)).as_key();

				let struct_function_ty = builder.function_ty(vec! [ struct_ty ], Some(struct_ty)).unwrap().as_key();
				let mut emitter = Emitter::new(&ctx).unwrap();

				let ll_struct_function_user_ty = emitter.emit_ty(struct_function_ty);
				let struct_function_abi = emitter.abi_info(ll_struct_function_user_ty);
				let ll_struct_function_ty = struct_function_abi.lltype;

				let ll_struct_function = LLVMValue::create_function(emitter.module.inner(), ll_struct_function_ty, llvm_str!(concat!("fn_struct_", stringify!($name))));
				struct_function_abi.apply_attributes(emitter.ll.ctx, ll_struct_function);

				let ll_mod = llvm_from_c(build_c_abi_str!($name ($( $field_name : $field_ty ),*)));

				let truth_ll_struct_function = LLVMValue::get_function(ll_mod, llvm_str!(concat!("fn_struct_", stringify!($name))));
				let truth_ll_struct_function_ty = LLVMType::of(truth_ll_struct_function);

				println!("struct abi: {:#?}", struct_function_abi);
				println!();
				println!("got: {:#?}\nexpected: {:#?}", ll_struct_function, truth_ll_struct_function);
				println!();
				println!("got: {}\nexpected: {}", ll_struct_function_ty, truth_ll_struct_function_ty);
				assert!(truth_ll_struct_function_ty.equivalent(ll_struct_function_ty));
			} )*
		} };
	}




	fn llvm_from_c (c_code: &str) -> LLVMModuleRef {
		// echo "int main () { return 1; }" | clang -xc -c -emit-llvm -o- - | llvm-dis
		use std::process::{ Command, Stdio };
		use std::io::Write;
		use std::mem::MaybeUninit;
		let mut clang =
			Command::new("clang")
				.arg("-xc")
				.arg("-c")
				.arg("-emit-llvm")
				.arg("-o-")
				.arg("-")
				.stdin(Stdio::piped())
				.stdout(Stdio::piped())
				.spawn()
				.unwrap();

		clang.stdin.as_mut().unwrap().write_all(c_code.as_bytes()).unwrap();

		let clang_output = clang.wait_with_output().unwrap().stdout;

		unsafe {
			let context = LLVMContextCreate();
			let mut module = MaybeUninit::uninit();

			let buff = LLVMCreateMemoryBufferWithMemoryRange(clang_output.as_ptr() as *const _, clang_output.len() as _, llvm_str!("harness bitcode").as_ptr(), LLVM_FALSE);
			assert!(LLVMParseBitcodeInContext2(context, buff, module.as_mut_ptr()) == LLVM_OK, "Cannot load bitcode harness module");
			LLVMDisposeMemoryBuffer(buff);

			module.assume_init()
		}
	}

	fn build_abi_tests () {
		build_abi_tests! {
			i32_2(x: sint32_ty, y: sint32_ty)
			i64_2(x: sint64_ty, y: sint64_ty)
			i32_4(x: sint32_ty, y: sint32_ty, z: sint32_ty, w: sint32_ty)
			i64_4(x: sint64_ty, y: sint64_ty, z: sint64_ty, w: sint64_ty)
			i32_i16(x: sint32_ty, y: sint16_ty)
			i16_i32(x: sint16_ty, y: sint32_ty)
			i16_4(x: sint16_ty, y: sint16_ty, z: sint16_ty, w: sint16_ty)
			i16_8(x0: sint16_ty, y0: sint16_ty, z0: sint16_ty, w0: sint16_ty, x1: sint16_ty, y1: sint16_ty, z1: sint16_ty, w1: sint16_ty)
			f32_2(x: real32_ty, y: real32_ty)
			f32_4(x: real32_ty, y: real32_ty, z: real32_ty, w: real32_ty)
			f64_2(x: real64_ty, y: real64_ty)
			f64_4(x: real64_ty, y: real64_ty, z: real32_ty, w: real32_ty)
		}
	}

	build_abi_tests()
}