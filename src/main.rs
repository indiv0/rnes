#![cfg_attr(feature="clippy", feature(plugin))]
#![cfg_attr(feature="clippy", plugin(clippy))]

extern crate rnes;

use std::env;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;
use rnes::ROM;

// The name of the program being executed.
const PROGRAM_NAME: &str = "rnes";

fn main() {
    // Retrieve the arguments passed to the program.
    let mut args = env::args();

    // Parse the arguments passed to the program.
    let program_name = args.next();
    let program_name = program_name
        .as_ref()
        .map(|s| &s[..])
        .unwrap_or(PROGRAM_NAME);
    let rom_path_str = args.next();

    // If a ROM filepath was provided, attempt to parse the ROM cartridge at the
    // specified location.
    let path = rom_path_str
        .ok_or_else(|| { usage(program_name); panic!(); });
    let path = path
        .as_ref()
        .map(|s| Path::new(s))
        .unwrap();

    // Ensure that the path exists.
    if !path.exists() {
        panic!("Specified path does not exist: {:?}", path);
    }

    // Ensure that the path points to a file.
    if !path.is_file() {
        panic!("Specified path does not point to a file: {:?}", path);
    }

    // Open the file with a buffered reader.
    let file = File::open(path)
        .expect(&format!("Failed to open file: {:?}", path));
    let mut reader = BufReader::new(file);

    // Parse the file contents into a NES `ROM`.
    let rom = ROM::load(&mut reader)
        .expect("Failed to parse ROM");
    println!("Parsed ROM. Header: {}", rom.header());
}

/// Print out program usage information.
fn usage(name: &str) {
    println!("Usage: {} [FILE]", name);
}
