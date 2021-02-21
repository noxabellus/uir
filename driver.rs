use cli::{ cli, CliResult };


fn main () {
	let mut x = String::from("not x");
	let mut y = String::from("sometimes y");
	let mut z = false;
	let mut w = 0isize;

	let mut args = std::env::args();
	let _path = args.next().unwrap();

	match cli! {
		x : -x / --extra_x
		"Sets the value of x"

		y : -y / --extra_y
		"Sets the value of y"

		z : -z / --extra_z
		"Sets the z flag"

		w : -w / --extra_w
		"Sets the w value"
	}.parse(args) {
		CliResult::Ok => {
			println!("\nparsed args:\n x: {}, y: {}, z: {}, w: {}", x, y, z, w);
		}

		CliResult::RequestExit => {
			std::process::exit(0);
		}

		CliResult::Err(err) => {
			err.dump();
			std::process::exit(1);
		}
	}
}