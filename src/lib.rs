#![cfg_attr(feature="clippy", feature(plugin))]
#![cfg_attr(feature="clippy", plugin(clippy))]

#[macro_use]
extern crate nom;

mod cpu;
mod instruction;
mod memory;
mod opcode;
mod rom;
mod util;

pub use cpu::CPU;
pub use instruction::{AddressingMode, Instruction};
pub use memory::{Memory, NESMemory};
pub use opcode::Opcode;
pub use rom::{parse_rom, Header, Mirroring, ROM, TvSystem};
