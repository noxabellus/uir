use llvm_sys::analysis::{LLVMVerifierFailureAction::*};

use {
	std::{
		sync::atomic::{ Ordering, AtomicBool },
		io::Write,
		path::PathBuf,
		fs::create_dir_all,
	},
	uir_core::{
		support::slotmap::*,
		ir::*,
		ty::*,
		builder::*,
		printer::*,
		target,
		block,
	},
	BinaryOp::*,
	crate::{
		LLVMBackend,
	},
};


fn get_log_path (file: &str) -> PathBuf {
	static X: AtomicBool = AtomicBool::new(false);

	let mut path: PathBuf = [ "..", "..", "local", "log" ].iter().collect();

	if !X.load(Ordering::Relaxed) {
		create_dir_all(&path).unwrap();
		X.store(true, Ordering::Relaxed);
	}

	path.push(file);

	path
}

#[test]
fn fib () -> IrResult {
	let ir_path = get_log_path("fib.ir");
	let llpath = get_log_path("fib.ll");


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

	block!(f, entry => {
		f.param_ref(n);
		f.load();
		f.const_sint32(2);
		f.binary_op(Lt)
		 .set_name("predicate");

		f.cond_branch(use_n, recurse);
	});

	block!(f, use_n => {
		f.param_ref(n);
		f.load();

		f.branch(end);
	});

	block!(f, recurse => {
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

	block!(f, end => {
		f.phi(s32t)
		 .set_name("result");

		f.ret();
	});

	let BuilderResult { value: function, error } = f.finalize();
	let function = function.as_key();

	let ir_src = std::fs::File::create(ir_path).unwrap();
	write!(&ir_src, "{}", PrinterState::new(&context).with_error(error).print_function(function)).unwrap();



	let backend = LLVMBackend::new(&context).unwrap();
	let llfunc = backend.emit_function_body(function);
	llfunc.verify_function(LLVMAbortProcessAction);

	let llsrc = std::fs::File::create(llpath).unwrap();
	write!(&llsrc, "{:?}", llfunc).unwrap();


	Ok(())
}


macro_rules! structure_ty {
	($b:expr, $name:expr => { $( $field_ty:expr ),* }) => { {
		let s = $b.empty_structure_ty().set_name($name).as_key();
		let body = vec![
			$( $field_ty.as_key() ),*
		];
		$b.set_structure_ty_body(s, body).unwrap()
	} };
}

macro_rules! structure_const {
	($ty:expr => $kind:ident $( $( $tt:tt )+ )?) => {
		Constant::Aggregate($ty.as_key(), ConstantAggregateData::$kind $( ( structure_const!(%BODY% $( $tt )+) ) )?)
	};

	(%BODY% { $( $index:expr => $value:expr ),+ $(,)? }) => {
		vec![
			$( ($index, $value.into()) ),+
		]
	};

	(%BODY% { $( $value:expr ),+ $(,)? }) => {
		vec![
			$( $value.into() ),+
		]
	};

	(%BODY% $value:expr) => {
		Box::new($value.into())
	};
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


	let const_s32x2 = structure_const!(s32x2 => Complete {
		1i32, 2i32,
	});

	let const_s32x4 = structure_const!(s32x4 => Complete {
		1i32, 3i32, 3i32, 7i32,
	});

	let const_s32x8 = structure_const!(s32x8 => Complete {
		4i32, 3i32, 2i32, 1i32, 9i32, 8i32, 7i32, 6i32,
	});


	let const_s64x2 = structure_const!(s64x2 => Complete {
		1i64, 2i64,
	});

	let const_s64x4 = structure_const!(s64x4 => Complete {
		1i64, 3i64, 3i64, 7i64,
	});

	let const_s64x8 = structure_const!(s64x8 => Complete {
		4i64, 3i64, 2i64, 1i64, 9i64, 8i64, 7i64, 6i64,
	});


	let const_r32x2 = structure_const!(r32x2 => Complete {
		1f32, 2f32,
	});

	let const_r32x4 = structure_const!(r32x4 => Complete {
		1f32, 3f32, 3f32, 7f32,
	});

	let const_r32x8 = structure_const!(r32x8 => Complete {
		4f32, 3f32, 2f32, 1f32, 9f32, 8f32, 7f32, 6f32,
	});


	let const_r64x2 = structure_const!(r64x2 => Complete {
		1f64, 2f64,
	});

	let const_r64x4 = structure_const!(r64x4 => Complete {
		1f64, 3f64, 3f64, 7f64,
	});

	let const_r64x8 = structure_const!(r64x8 => Complete {
		4f64, 3f64, 2f64, 1, 9f64, 8f64, 7f64, 6f64,
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
		let backend = LLVMBackend::new(&builder.ctx).unwrap();

		backend.emit_global(global_s32x2);
		backend.emit_global(global_s32x4);
		backend.emit_global(global_s32x8);

		backend.emit_global(global_s64x2);
		backend.emit_global(global_s64x4);
		backend.emit_global(global_s64x8);

		backend.emit_global(global_r32x2);
		backend.emit_global(global_r32x4);
		backend.emit_global(global_r32x8);

		backend.emit_global(global_r64x2);
		backend.emit_global(global_r64x4);
		backend.emit_global(global_r64x8);

		// let llsrc = std::fs::File::create(llpath).unwrap();
		println!( "{}", backend.ll);
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

		let printer = PrinterState::new(&builder.ctx).with_error(error);

		println!("{}\n{}", printer.print_ty(ty), printer.print_function(function));

		let backend = LLVMBackend::new(&builder.ctx).unwrap();
		let llfunction = backend.emit_function_body(function);

		println!("{:#?}\n{:#?}", backend.emit_ty(ty), llfunction);

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

		let printer = PrinterState::new(&builder.ctx).with_error(error);

		println!("{}\n{}", printer.print_ty(ty), printer.print_function(function));

		let backend = LLVMBackend::new(&builder.ctx).unwrap();
		let llfunction = backend.emit_function_body(function);

		println!("{:#?}\n{:#?}", backend.emit_ty(ty), llfunction);

		llfunction.verify_function(LLVMAbortProcessAction);
	}
}