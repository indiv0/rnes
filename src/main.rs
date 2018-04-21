#![deny(
    missing_debug_implementations, single_use_lifetime, trivial_casts, trivial_numeric_casts,
    unsafe_code, unused_extern_crates, unused_import_braces, unused_qualifications, unused_results,
    variant_size_differences
)]
#![cfg_attr(feature = "clippy", feature(plugin))]
#![cfg_attr(feature = "clippy", plugin(clippy))]

extern crate rnes;

use rnes::{CPU, NROM, ROM};
use std::env;
use std::fs::File;
use std::io::BufReader;
use std::path::Path;

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
    let path = rom_path_str.ok_or_else(|| {
        usage(program_name);
        panic!();
    });
    let path = path.as_ref().map(|s| Path::new(s)).unwrap();

    // Ensure that the path exists.
    if !path.exists() {
        panic!("Specified path does not exist: {:?}", path);
    }

    // Ensure that the path points to a file.
    if !path.is_file() {
        panic!("Specified path does not point to a file: {:?}", path);
    }

    // Open the file with a buffered reader.
    let file = File::open(path).expect(&format!("Failed to open file: {:?}", path));
    let mut reader = BufReader::new(file);

    // Parse the file contents into a NES `ROM`.
    let rom = ROM::load(&mut reader).expect("Failed to parse ROM");
    println!("Parsed ROM. Header: {}", rom.header());

    let _mapper = NROM::new(rom);
    let mut cpu = CPU::new();

    run(&mut cpu);
}

fn run(cpu: &mut CPU) {
    // TODO: perhaps reset CPU here (e.g. a, x, y, etc. to 0)?
    loop {
        cpu.step();
    }
}

/// Print out program usage information.
fn usage(name: &str) {
    println!("Usage: {} [FILE]", name);
}
