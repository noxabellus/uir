use std::{ fmt, env };

#[derive(Debug)]
pub enum OptErr {
	RequiresOperand,
	InvalidHelpArg,
	UnknownArg(String),
	UnparseableArgData(String),
}

impl fmt::Display for OptErr {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		match self {
			OptErr::RequiresOperand => write!(f, "This option requires a data argument to follow it, but none was found"),
			OptErr::InvalidHelpArg => write!(f, "Help option must be passed as the first and only argument"),
			OptErr::UnknownArg(arg) => write!(f, "Argument {} is not recognized", arg),
			OptErr::UnparseableArgData(arg) => write!(f, "The data for this argument ({}) was unparseable", arg),
		}
	}
}


pub type OptResult<T = ()> = Result<T, OptErr>;

pub trait OptData<'s> {
	fn process (&mut self, arg: &str, input: &mut env::Args) -> OptResult;

	fn dump (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl<'s> fmt::Display for &dyn OptData<'s> {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		self.dump(f)
	}
}

impl<'s> OptData<'s> for String {
	fn process (&mut self, mut arg_data: &str, input: &mut env::Args) -> OptResult {
		if !arg_data.is_empty() {
			if arg_data.starts_with('=')
			&& arg_data.len() > 1 {
				arg_data = &arg_data[1..];
			}

			self.clear();
			self.push_str(&arg_data);
		} else {
			let value = input.next().ok_or(OptErr::RequiresOperand)?;

			self.clear();
			self.push_str(&value);
		}

		Ok(())
	}

	fn dump (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "\"{}\"", self)
	}
}

impl<'s> OptData<'s> for bool {
	fn process (&mut self, arg_data: &str, _input: &mut env::Args) -> OptResult {
		if !arg_data.is_empty() {
			return Err(OptErr::UnparseableArgData(arg_data.to_owned()))
		}

		*self = !*self;

		Ok(())
	}

	fn dump (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "{}", if *self { "enabled" } else { "disabled" })
	}
}


#[macro_export]
macro_rules! impl_opt_data_via_parse_and_display {
	($($ty:ty),* $(,)?) => { $(
		impl<'s> $crate::OptData<'s> for $ty {
			fn process (&mut self, mut arg_data: &str, input: &mut ::std::env::Args) -> $crate::OptResult {
				if !arg_data.is_empty() {
					if arg_data.starts_with('=')
					&& arg_data.len() > 1 {
						arg_data = &arg_data[1..];
					}

					*self = arg_data.parse().map_err(|_| $crate::OptErr::UnparseableArgData(arg_data.to_owned()))?;
				} else {
					let value = input.next().ok_or(OptErr::RequiresOperand)?;

					*self = (&value).parse().map_err(|_| $crate::OptErr::UnparseableArgData(value))?;
				}

				Ok(())
			}

			fn dump (&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
				fmt::Display::fmt(self, f)
			}
		} )*
	};
}

impl_opt_data_via_parse_and_display! {
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
		&& arg[2..].starts_with(self.long) {
			return Some(self.data.process(&arg[2 + self.long.len()..], input))
		}

		if arg.starts_with('-')
		&& arg[1..].starts_with(self.short) {
			return Some(self.data.process(&arg[1 + self.short.len()..], input))
		}

		None
	}

	fn dump (&self) {
		println!("{} : -{} / --{}\n{} (Default: {})\n", self.name, self.short, self.long, self.description, &*self.data)
	}
}


pub struct CliErr(pub usize, pub OptErr);

impl CliErr {
	pub fn dump (&self) {
		eprintln!("{}", self);
	}
}

impl fmt::Display for CliErr {
	fn fmt (&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "Error with command line argument {}: {}", self.0, self.1)
	}
}

pub enum CliResult {
	Ok {
		positional: Vec<String>,
		pass_through: Option<Vec<String>>
	},
	RequestExit,
	Err(CliErr),
}


pub struct Cli<'d, 's> (pub &'d mut [Opt<'d, 's>]);

impl<'d, 's> Cli<'d, 's> {
	pub fn new (opts: &'d mut [Opt<'d, 's>]) -> Self {
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

		let mut positional = vec![];

		'args: while let Some(arg) = args.next() {
			dbg!(&arg);

			let bytes = arg.as_bytes();

			if (bytes.len() > 2 && bytes.starts_with(b"--"))
			|| (bytes.len() > 1 && bytes[0] == b'-' && bytes[1] != b'-') {
				if arg == "-h" || arg == "--help" {
					if i == 0 {
						self.dump();

						if args.next().is_some() {
							println!("Remaining args ignored ...");
						}

						return CliResult::RequestExit
					} else {
						return CliResult::Err(CliErr(i, OptErr::InvalidHelpArg))
					}
				}

				for opt in self.0.iter_mut() {
					match opt.try_parse(&arg, &mut args) {
						None => continue,
						Some(Ok(_)) => {
							i += 1;
							continue 'args
						},
						Some(Err(e)) => return CliResult::Err(CliErr(i, e))
					}
				}

				// if we make it here no opt succeeded in parsing the current input
				return CliResult::Err(CliErr(i, OptErr::UnknownArg(arg)))
			} else if arg == "--" {
				let pass_through = Some(args.collect());

				return CliResult::Ok {
					positional,
					pass_through
				}
			}

			positional.push(arg);
		}

		CliResult::Ok {
			positional,
			pass_through: None
		}
	}

	pub fn dump (&mut self) {
		println!("help : -h / --help\nPrint this help message\n");
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
		$name:ident : -$short:ident / --$long:ident
		$description:literal
	)*) => {
		$crate::Cli::new(&mut [
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