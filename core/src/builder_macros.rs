#[macro_export]
macro_rules! with_block {
	($f:expr, $block_name:literal => $body:expr) => {
		{
			let block = {
				$f.append_new_block()
					.set_name($block_name)
					.as_key()
			};

			$crate::with_block!($f, block => $body)
		}
	};

	($f:expr , $block:expr => $body:expr) => {
		{
			$f.set_active_block($block);
			$body;
			$f.clear_active_block()
		}
	};
}