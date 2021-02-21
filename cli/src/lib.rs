use std::env;

#[derive(Debug)]
pub enum OptErr {
	RequiresOperand,
	UnknownArg(String),
	UnparseableArgData(String),
}


pub type OptResult = Result<(), OptErr>;

pub trait OptData<'s> {
	fn process (&mut self, input: &mut env::Args) -> OptResult;
}

impl<'s> OptData<'s> for String {
	fn process (&mut self, input: &mut env::Args) -> OptResult {
		let value = input.next().ok_or(OptErr::RequiresOperand)?;

		self.clear();
		self.push_str(&value);

		Ok(())
	}
}

impl<'s> OptData<'s> for bool {
	fn process (&mut self, _input: &mut env::Args) -> OptResult {
		*self = !*self;
		Ok(())
	}
}


#[macro_export]
macro_rules! impl_opt_data_via_parse {
	($($ty:ty),* $(,)?) => { $(
		impl<'s> $crate::OptData<'s> for $ty {
			fn process (&mut self, input: &mut ::std::env::Args) -> $crate::OptResult {
				let value = input.next().ok_or($crate::OptErr::RequiresOperand)?;

				*self = (&value).parse().map_err(|_| $crate::OptErr::UnparseableArgData(value))?;

				Ok(())
			}
		} )*
	};
}

impl_opt_data_via_parse! {
	u8, u16, u32, u64, u128, usize,
	i8, i16, i32, i64, i128, isize,
	f32, f64
}



pub struct Opt<'d, 's> {
	pub data: &'d mut dyn OptData<'s>,
	pub name: &'s str,
	pub short: &'s str,
	pub long: &'s str,
	pub description: &'s str,
}

impl<'d, 's> Opt<'d, 's> {
	fn try_parse (&mut self, arg: &str, input: &mut env::Args) -> Option<OptResult> {
		if arg.starts_with("--")
		&& &arg[2..] == self.long {
			return Some(self.data.process(input))
		}

		if arg.starts_with('-')
		&& &arg[1..] == self.short {
			return Some(self.data.process(input))
		}

		None
	}

	fn dump (&self) {
		println!("{} : -{} / --{}\n{}", self.name, self.short, self.long, self.description)
	}
}


pub type CliResult = Result<(), (OptErr, usize)>;


pub struct Cli<'d, 's> (pub Vec<Opt<'d, 's>>);

impl<'d, 's> Cli<'d, 's> {
	pub fn new (opts: Vec<Opt<'d, 's>>) -> Self {
		if cfg!(debug_assertions) {
			for opt in opts.iter() {
				assert_ne!(opt.name, "help");
				assert_ne!(opt.long, "help");
				assert_ne!(opt.short, "h");
			}
		}

		Self(opts)
	}

	pub fn parse (&mut self, mut args: env::Args) -> CliResult {
		let mut i = 0;

		'args: while let Some(arg) = args.next() {
			if arg == "-h" || arg == "--help" {
				self.dump();
				i += 1;
				continue
			}

			for opt in self.0.iter_mut() {
				match opt.try_parse(&arg, &mut args) {
					None => continue,
					Some(Ok(_)) => {
						i += 1;
						continue 'args
					},
					Some(Err(e)) => return Err((e, i))
				}
			}

			// if we make it here no opt succeeded in parsing the current input
			if (arg.starts_with("--") && arg.len() > 2)
			|| (arg.starts_with('-') && arg.len() > 1) {
				return Err((OptErr::UnknownArg(arg), i))
			}

			break
		}

		Ok(())
	}

	pub fn dump (&mut self) {
		println!("help : -h / --help\nPrint this help message");
		self.0.iter().for_each(Opt::dump)
	}
}


pub const fn const_str_eq (a: &'static str, b: &'static str) -> bool {
	if a.len() != b.len() { return false }

	let mut i = 0usize;

	let a = a.as_bytes();
	let b = b.as_bytes();

	loop {
		if a[i] != b[i] { return false }
		i += 1;
		if i == a.len() { return true }
	}
}


#[macro_export]
macro_rules! cli {
	($(
		$name:ident = -$short:ident --$long:ident : $description:literal
	)*) => {
		$crate::Cli::new(vec![
			$(
				{
					macro_rules! static_assert {
						($cond:expr) => { let _ = [(); 0 - (!($cond) as usize)]; };
					}

					static_assert!(!$crate::const_str_eq(stringify!($name), "help"));
					static_assert!(!$crate::const_str_eq(stringify!($short), "h"));
					static_assert!(!$crate::const_str_eq(stringify!($long), "help"));

					$crate::Opt {
						data: &mut $name,
						name: stringify!($name),
						short: stringify!($short),
						long: stringify!($long),
						description: $description
					}
				}
			), *
		])
	}
}