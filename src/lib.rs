#![deny(
    single_use_lifetime, trivial_casts, trivial_numeric_casts, unsafe_code, unused_extern_crates,
    unused_import_braces, unused_qualifications, variant_size_differences
)]
#![cfg_attr(feature = "clippy", feature(plugin))]
#![cfg_attr(feature = "clippy", plugin(clippy))]
#![cfg_attr(feature = "nightly", feature(test))]

#[macro_use]
extern crate nom;

mod apu;
mod cpu;
mod instruction;
mod mapper;
mod memory;
mod opcode;
mod rom;
mod util;

pub use cpu::CPU;
pub use instruction::{AddressingMode, Instruction};
pub use mapper::{mapper_from_rom, Mapper, NROM};
pub use memory::{Memory, NESMemory};
pub use opcode::Opcode;
pub use rom::{Header, Mirroring, TvSystem, ROM};
