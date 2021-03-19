#[macro_export]
macro_rules! block {
	($f:expr , $block_name:literal $body:block) => {
		{
			let block = {
				$f.append_new_block()
					.set_name($block_name)
					.as_key()
			};

			$crate::block!($f, block => $body)
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