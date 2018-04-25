// The size of the NES memory (64 KB).
const MEM_SIZE: usize = 0x1_0000;

// Address pairs corresponding to memory region boundaries.
const ADDR_RANGE_RAM_START: Address = 0x0000;
const ADDR_RANGE_RAM_END: Address = 0x07FF;
const _ADDR_RANGE_RAM_MIRRORS_0_START: Address = 0x0800;
const _ADDR_RANGE_RAM_MIRRORS_0_END: Address = 0x0FFF;
const _ADDR_RANGE_RAM_MIRRORS_1_START: Address = 0x1000;
const _ADDR_RANGE_RAM_MIRRORS_1_END: Address = 0x17FF;
const _ADDR_RANGE_RAM_MIRRORS_2_START: Address = 0x1800;
const ADDR_RANGE_RAM_MIRRORS_2_END: Address = 0x1FFF;
const ADDR_RANGE_PPU_START: Address = 0x2000;
const _ADDR_RANGE_PPU_END: Address = 0x2007;
const _ADDR_RANGE_PPU_MIRRORS_START: Address = 0x2008;
const ADDR_RANGE_PPU_MIRRORS_END: Address = 0x3FFF;
const ADDR_RANGE_APU_0_START: Address = 0x4000;
const ADDR_RANGE_APU_0_END: Address = 0x4017;
const ADDR_RANGE_APU_1_START: Address = 0x4018;
const ADDR_RANGE_APU_1_END: Address = 0x401F;
const ADDR_RANGE_CART_START: Address = 0x4020;
const ADDR_RANGE_CART_END: Address = 0xFFFF;

// Sizes of each of the memory region boundaries.
const MEM_SIZE_RAM: u16 = 0x0800;
const _MEM_SIZE_RAM_MIRROR: u16 = 0x0800; // these are repeated 3 times
const _MEM_SIZE_PPU: u16 = 0x0008;
const _MEM_SIZE_PPU_MIRROR: u16 = 0x0008; // these are repeated many times
const _MEM_SIZE_APU_0: u16 = 0x0018;
const _MEM_SIZE_APU_1: u16 = 0x0008;
const _MEM_SIZE_CART: u16 = 0xBFE0;

/// A memory address.
pub type Address = u16;

/// Trait for 16-bit addressed memory management operations.
///
/// This trait allows for basic 16-bit memory functionality.
/// For example, this trait allows you to store and fetch values at specified
/// memory addresses.
pub trait Memory {
    /// Resets the entire memory space to zero.
    fn reset(&mut self);

    /// Fetches the value at the specified memory address.
    fn fetch(&mut self, address: Address) -> u8;

    /// Stores the value at the specified memory address and returns the
    /// previously stored value.
    fn store(&mut self, address: Address, value: u8) -> u8;
}

/// An implementation of the NES CPU memory.
///
/// # Memory Map
///
/// | Address Range | Size    | Device                                                                       |
/// |---------------|---------|------------------------------------------------------------------------------|
/// | `$0000-$07FF` | `$0800` | 2 KB internal RAM                                                            |
/// | `$0800-$0FFF` | `$0800` | Mirrors of `$0000-$07FF`                                                     |
/// | `$1000-$17FF` | `$0800` | (same as above)                                                              |
/// | `$1800-$1FFF` | `$0800` | (same as above)                                                              |
/// | `$2000-$2007` | `$0008` | NES PPU registers                                                            |
/// | `$2008-$3FFF` | `$1FF8` | Mirrors of `$2000-$2007` (repeats every 8 bytes)                             |
/// | `$4000-$4017` | `$0018` | NES APU and I/O registers                                                    |
/// | `$4018-$401F` | `$0008` | APU and I/O functionality that is normally disabled                          |
/// | `$4020-$5FFF` | `$1FE0` | Expansion ROM (used with Nintendo's MMC5 to expand the capabilities of VRAM) |
/// | `$6000-$7FFF` | `$2000` | SRAM (Save Ram used to save data between game plays)                         |
/// | `$8000-$FFFF` | `$8000` | PRG-ROM                                                                      |
///
/// ## Internal RAM
///
/// The NES has 2 KB of internal RAM at `$0000-$0800`.
/// This is an example allocation strategy for the RAM:
///
/// | Address Range | Size   | What can go there                                                      |
/// |---------------|--------|------------------------------------------------------------------------|
/// | `$0000-$000F` | 16 B   | Local variables and function arguments                                 |
/// | `$0010-$00FF` | 240 B  | Global variables accessed most often, including certain pointer tables |
/// | `$0100-$019F` | 160 B  | Data to be copied to nametable during next vertical blank              |
/// | `$01A0-$01FF` | 96 B   | Stack                                                                  |
/// | `$0200-$02FF` | 256 B  | Data to be copied to OAM during next vertical blank                    |
/// | `$0300-$03FF` | 256 B  | Variables used by sound player, and possible other variables           |
/// | `$0400-$07FF` | 1024 B | Arrays and less-often-accessed global variables                        |
///
/// There are two special pages in the internal RAM, the zero page and the
/// stack.
///
/// ### Zero Page
///
/// The "zero page" or "direct page" lies at `$0000-$00FF` (256 B).
/// This page is utilized by several special addressing modes which allow for
/// shorter/quicker instructions or allow indirect access to memory.
///
/// ### Stack Page
///
/// The "stack page" lies at `$0100-01FF`.
///
/// ## ROM & Save/Work RAM
///
/// Common boards and iNES mappers address ROM and Save/Work RAM in this format:
///
/// * `$6000-$7FFF` - Battery Backed Save or Work RAM
/// * `$8000-$FFFF` - Usual ROM, commonly with Mapper Registers
///
/// ## Interrupt Vectors
///
/// The CPU expects the following interrupt vectors:
///
/// * `$FFFA-FFFB` - NMI vector
/// * `$FFFC-FFFD` - Reset vector
/// * `$FFFE-FFFF` - IRQ/BRK vector
#[derive(Clone)]
pub struct NESMemory {
    /// Stores the 2 KB of NES RAM.
    ram: [u8; MEM_SIZE_RAM as usize],

    /// The last value read from the bus.
    ///
    /// This value is returned when the CPU attempts to read from an address which has no devices active. This is known as [open bus behaviour][open-bus-behaviour].
    ///
    /// [open-bus-behaviour]: https://wiki.nesdev.com/w/index.php/Open_bus_behavior "Open bus behaviour"
    last: u8,
}

impl NESMemory {
    /// Constructs a new `NESMemory`.
    pub fn new() -> Self {
        Self {
            ram: [0; MEM_SIZE_RAM as usize],
            // TODO: verify that the open bus value after initialization is 0x00.
            last: 0x00,
        }
    }
}

impl Default for NESMemory {
    fn default() -> Self {
        Self::new()
    }
}

impl Memory for NESMemory {
    fn reset(&mut self) {
        self.ram = [0; MEM_SIZE_RAM as usize];
    }

    fn fetch(&mut self, address: Address) -> u8 {
        assert!((address as usize) < MEM_SIZE);

        let value = match address {
            ADDR_RANGE_RAM_START..=ADDR_RANGE_RAM_MIRRORS_2_END => {
                self.ram[(address & ADDR_RANGE_RAM_END) as usize]
            }
            ADDR_RANGE_PPU_START..=ADDR_RANGE_PPU_MIRRORS_END => {
                // FIXME: actually communicate with the PPU here.
                panic!(
                    "PPU not implemented; memory read attempt at: {:#4X}",
                    address
                );
            }
            ADDR_RANGE_APU_0_START..=ADDR_RANGE_APU_0_END => {
                // FIXME: actually communicate with the APU here.
                panic!(
                    "APU/IO not implemented; memory read attempt at: {:#4X}",
                    address
                );
            }
            ADDR_RANGE_APU_1_START..=ADDR_RANGE_APU_1_END => {
                // FIXME: implement CPU test mode.
                panic!(
                    "CPU test mode not implemented; memory read attempt at: {:#4x}",
                    address
                );
            }
            ADDR_RANGE_CART_START..=ADDR_RANGE_CART_END => {
                // FIXME: implement cartridge memory access, don't just assume open bus behaviour.
                self.last
            }
            _ => unreachable!(),
        };

        self.last = value;
        value
    }

    fn store(&mut self, address: Address, value: u8) -> u8 {
        assert!((address as usize) < MEM_SIZE);

        match address {
            ADDR_RANGE_RAM_START..=ADDR_RANGE_RAM_MIRRORS_2_END => {
                let address = (address & ADDR_RANGE_RAM_END) as usize;

                let previous = self.ram[address];
                self.ram[address] = value;
                previous
            }
            ADDR_RANGE_PPU_START..=ADDR_RANGE_PPU_MIRRORS_END => {
                // FIXME: actually communicate with the PPU here.
                panic!(
                    "PPU not implemented; memory write attempt at: {:#4X}",
                    address
                );
            }
            ADDR_RANGE_APU_0_START..=ADDR_RANGE_APU_0_END => {
                // FIXME: actually communicate with the APU here.
                panic!(
                    "APU/IO not implemented; memory write attempt at: {:#4X}",
                    address
                );
            }
            ADDR_RANGE_APU_1_START..=ADDR_RANGE_APU_1_END => {
                // FIXME: implement CPU test mode.
                panic!(
                    "CPU test mode not implemented; memory write attempt at: {:#4x}",
                    address
                );
            }
            ADDR_RANGE_CART_START..=ADDR_RANGE_CART_END => {
                // FIXME: implement cartridge memory access.
                panic!(
                    "Cartridge memory not implemented; memory read attempt at: {:#4x}",
                    address
                );
            }
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        Memory, NESMemory, _ADDR_RANGE_RAM_MIRRORS_0_START, _ADDR_RANGE_RAM_MIRRORS_1_START,
        _ADDR_RANGE_RAM_MIRRORS_2_START, ADDR_RANGE_RAM_START,
    };

    #[test]
    fn test_reset() {
        let mut memory = NESMemory::new();
        memory.ram[0x0000] = 0xAA;

        memory.reset();
        assert_eq!(memory.ram[0x0000], 0x00);
    }

    #[test]
    fn test_fetch() {
        let mut memory = NESMemory::new();
        memory.ram[0x0000] = 0xAA;

        assert_eq!(memory.fetch(0x0000), 0xAA);
    }

    #[test]
    fn test_store() {
        let mut memory = NESMemory::new();
        memory.ram[0x0000] = 0xAA;

        let previous = memory.store(0x0000, 0xBB);
        assert_eq!(memory.ram[0x0000], 0xBB);
        assert_eq!(previous, 0xAA);
    }

    #[test]
    fn test_ram_mirrors() {
        let mut memory = NESMemory::new();

        // RAM mirrors.
        memory.store(ADDR_RANGE_RAM_START, 0xFF);
        assert_eq!(memory.fetch(ADDR_RANGE_RAM_START), 0xFF);
        assert_eq!(memory.fetch(_ADDR_RANGE_RAM_MIRRORS_0_START), 0xFF);
        assert_eq!(memory.fetch(_ADDR_RANGE_RAM_MIRRORS_1_START), 0xFF);
        assert_eq!(memory.store(_ADDR_RANGE_RAM_MIRRORS_2_START, 0x00), 0xFF);
        assert_eq!(memory.fetch(ADDR_RANGE_RAM_START), 0x00);
    }

    // FIXME: uncomment this when the PPU is implemented.
    /*
    #[test]
    fn test_ppu_mirrors() {
        let mut memory = NESMemory::new();

        memory.store(ADDR_RANGE_PPU_START, 0xFF);
        assert_eq!(memory.fetch(_ADDR_RANGE_PPU_MIRRORS_START), 0xFF);
        assert_eq!(
            memory.store(_ADDR_RANGE_PPU_MIRRORS_START + _MEM_SIZE_PPU_MIRROR, 0xAA),
            0xFF
        );
        assert_eq!(
            memory.fetch(ADDR_RANGE_PPU_MIRRORS_END - _MEM_SIZE_PPU_MIRROR + 0x0001),
            0xAA
        );
    }
    */

    #[test]
    fn test_open_bus_behaviour() {
        let mut memory = NESMemory::new();

        memory.store(0x0000, 0x73);

        assert_eq!(memory.fetch(0x0000), 0x73);
        // No SRAM is loaded at 0x6000, so we expect open bus behaviour.
        assert_eq!(memory.fetch(0x6000), 0x73);
    }
}
