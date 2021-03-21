#[macro_export]
macro_rules! block {
	($f:expr , $block_name:literal $body:block) => {
		$crate::block!($f, $block_name => $body)
	};

	($f:expr , $block_name:ident $body:block) => {
		$crate::block!($f, stringify!($block_name) => $body)
	};

	($f:expr , $block_name:expr => $body:block) => { {
		let block = {
			$f.append_new_block()
				.set_name($block_name)
				.as_key()
		};

		$crate::with_block!($f, block => $body)
	} };
}

#[macro_export]
macro_rules! with_block {
	($f:expr , $block:expr => $body:expr) => ({
		$f.set_active_block($block);
		$body;
		$f.clear_active_block()
	});
}

#[macro_export]
macro_rules! structure_ty {
	($b:expr , $name:expr => { $( $field_ty:expr ),* $(,)? }) => ({
		let s = $b.empty_structure_ty().set_name($name).as_key();
		let body = vec![
			$( $field_ty.as_key() ),*
		];
		$b.set_structure_ty_body(s, body).unwrap()
	});

	($b:expr , $name:ident { $( $field_ty:expr ),* $(,)? }) => ({
		$crate::structure_ty!($b, stringify!($name) => { $( $field_ty ),* })
	});
}

#[macro_export]
macro_rules! aggregate_const {
	($ty:expr => $kind:ident $( $( $tt:tt )+ )?) => {
		Constant::Aggregate($ty.as_key(), ConstantAggregateData::$kind $( ( aggregate_const!(%BODY% $( $tt )+) ) )?)
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