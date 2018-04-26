mod nrom;

use self::MemoryType::{CHRRAM, CHRROM, PRGRAM, PRGROM};
use memory::Address;
use rom::ROM;
use std::u8;

pub use self::nrom::NROM;

#[derive(Clone, Debug)]
pub enum MemoryType {
    CHRRAM(usize, Vec<u8>),
    CHRROM(usize, Vec<u8>),
    PRGRAM(usize, Vec<u8>),
    PRGROM(usize, Vec<u8>),
}

impl MemoryType {
    fn len(&self) -> usize {
        match self {
            CHRRAM(len, _mem) | CHRROM(len, _mem) | PRGRAM(len, _mem) | PRGROM(len, _mem) => *len,
        }
    }
}

// TODO: perhaps replace this with the `Memory` trait?
trait Fetch {
    fn fetch(&self, address: Address) -> u8;
}

// TODO: perhaps replace this with the `Memory` trait?
trait Store {
    fn store(&mut self, address: Address, value: u8) -> u8;
}

impl Fetch for MemoryType {
    fn fetch(&self, address: Address) -> u8 {
        match self {
            CHRRAM(_len, mem) | CHRROM(_len, mem) | PRGRAM(_len, mem) | PRGROM(_len, mem) => {
                mem[address as usize]
            }
        }
    }
}

impl Store for MemoryType {
    fn store(&mut self, address: Address, value: u8) -> u8 {
        match self {
            CHRRAM(_len, mem) | PRGRAM(_len, mem) => {
                let old_value = mem[address as usize];
                mem[address as usize] = value;
                old_value
            }
            CHRROM(_len, mem) | PRGROM(_len, mem) => mem[address as usize],
        }
    }
}

/// Trait for 16-bit addressed memory management operations on a memory mapper.
///
/// This trait allows for basic 16-bit memory functionality.
/// For example, this trait allows you to store and fetch values at specified
/// memory addresses in the PRG ROM/RAM and/or CHR ROM/RAM.
///
/// If the requested is not mapped (i.e. there are no devices active for the address), `None` is returned to indicate as such.
pub trait Mapper {
    /// Fetches the value at the specified memory address.
    ///
    /// Returns `None` if no devices are active for the address.
    fn fetch(&self, _address: Address) -> Option<u8> {
        return None;
    }

    /// Stores the value at the specified memory address and returns the previously stored value.
    ///
    /// Writing to ROM will result in a no-op.
    fn store(&mut self, _address: Address, _value: u8) -> u8;
}

/// Returns a memory mapper, constructed based on the detailed provided in the
/// specified ROM.
pub fn mapper_from_rom(rom: ROM) -> impl Mapper {
    match rom.header.mapper() {
        0x00 => NROM::new(rom),
        mapper_id => panic!("Unsupported mapper ID: {}", mapper_id),
    }
}
