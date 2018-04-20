#![cfg_attr(feature="clippy", feature(plugin))]
#![cfg_attr(feature="clippy", plugin(clippy))]
#![cfg_attr(feature="nightly", feature(test))]

#[macro_use]
extern crate nom;

mod cpu;
mod instruction;
mod mapper;
mod memory;
mod opcode;
mod rom;
mod util;

pub use cpu::CPU;
pub use instruction::{AddressingMode, Instruction};
pub use mapper::NROM;
pub use memory::{Memory, NESMemory};
pub use opcode::Opcode;
pub use rom::{Header, Mirroring, ROM, TvSystem};
