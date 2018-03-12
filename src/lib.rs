#![cfg_attr(feature="clippy", feature(plugin))]
#![cfg_attr(feature="clippy", plugin(clippy))]

mod cpu;
mod instruction;
mod memory;
mod opcode;

pub use cpu::CPU;
pub use instruction::{AddressingMode, Instruction};
pub use memory::{Memory, NESMemory};
pub use opcode::Opcode;
