use cli::{ cli, CliResult };


fn main () -> CliResult {
	let mut x = String::from("");
	let mut y = String::from("");
	let mut z = false;
	let mut w = 0isize;

	let mut args = std::env::args();
	let _path = args.next().unwrap();

	(cli! {
		x = -x --extra_x : "Sets the value of x"
		y = -y --extra_y : "Sets the value of y"
		z = -z --extra_z : "Sets the z flag"
		w = -w --extra_w : "Sets the w value"
	}).parse(args)?;

	println!("\nparsed args:\n x: {}, y: {}, z: {}, w: {}", x, y, z, w);

	Ok(())
}