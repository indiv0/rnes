/// Trait for 16-bit addressed memory management operations.
///
/// This trait allows for basic 16-bit memory functionality.
/// For example, this trait allows you to store and fetch values at specified
/// memory addresses.
pub trait Memory {
    /// Resets the entire memory space to zero.
    fn reset(&mut self);

    /// Fetches the value at the specified memory address.
    fn fetch(&self, address: u16) -> u8;

    /// Stores the value at the specified memory address and returns the
    /// previously stored value.
    fn store(&mut self, address: u16, value: u8) -> u8;
}

/// An implementation of the NES CPU memory.
///
/// # Memory Map
///
/// | Address Range | Size    | Device                                                  |
/// |---------------|---------|---------------------------------------------------------|
/// | `$0000-$07FF` | `$0800` | 2 KB internal RAM                                       |
/// | `$0800-$0FFF` | `$0800` | Mirrors of `$0000-$07FF`                                |
/// | `$1000-$17FF` | `$0800` | (same as above)                                         |
/// | `$1800-$1FFF` | `$0800` | (same as above)                                         |
/// | `$2000-$2007` | `$0008` | NES PPU registers                                       |
/// | `$2008-$3FFF` | `$1FF8` | Mirrors of `$2000-$2007` (repeats every 8 bytes)        |
/// | `$4000-$4017` | `$0018` | NES APU and I/O registers                               |
/// | `$4018-$401F` | `$0008` | APU and I/O functionality that is normally disabled     |
/// | `$4020-$FFFF` | `$BFE0` | Cartridge space: PRG ROM, PRG RAM, and mapper registers |
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
/// The "zero page" or "direct page" lies at `$0000-$00FF` (256 B).
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
///
/// # Addressing Modes
///
/// NES memory has several addressing modes available, as can be seen in the
/// following table:
///
/// | Mode          | Instruction  | Action               |
/// |---------------|--------------|----------------------|
/// | Immediate     | LDA #$EA     | A <- $EA             |
/// | Absolute      | LDA $0314    | A <- M($0314)        |
/// | Absolute, X   | LDA $0314, X | A <- M($0314 + X)    |
/// | Absolute, Y   | LDA $0314, Y | A <- M($0314 + Y)    |
/// | Zeropage      | LDA $02      | A <- M($02)          |
/// | Zeropage, X   | LDA $02, X   | A <- M($02 + X)      |
/// | Zeropage, Y   | LDA $02, Y   | A <- M($02 + Y)      |
/// | (Zeropage, X) | LDA ($02, X) | A <- M(PTR($02 + X)) |
/// | (Zeropage), Y | LDA ($02), Y | A <- M(PTR($02) + Y) |
pub struct NESMemory {
    /// Stores the 64 KB of NES memory.
    address_space: [u8; 0xFFFF],
}

impl NESMemory {
    /// Constructs a new `NESMemory`.
    pub fn new() -> Self {
        Self {
            address_space: [0; 0xFFFF],
        }
    }
}

impl Memory for NESMemory {
    fn reset(&mut self) {
        self.address_space = [0; 0xFFFF];
    }

    fn fetch(&self, address: u16) -> u8 {
        self.address_space[address as usize]
    }

    fn store(&mut self, address: u16, value: u8) -> u8 {
        let previous = self.address_space[address as usize];
        self.address_space[address as usize] = value;
        previous
    }
}

#[cfg(test)]
mod tests {
    use super::{Memory, NESMemory};

    #[test]
    fn test_reset() {
        let mut memory = NESMemory::new();
        memory.address_space[0x0000] = 0xAA;

        memory.reset();
        assert_eq!(memory.address_space[0x0000], 0x00);
    }

    #[test]
    fn test_fetch() {
        let mut memory = NESMemory::new();
        memory.address_space[0x0000] = 0xAA;

        assert_eq!(memory.fetch(0x0000), 0xAA);
    }

    #[test]
    fn test_store() {
        let mut memory = NESMemory::new();
        memory.address_space[0x0000] = 0xAA;

        let previous = memory.store(0x0000, 0xBB);
        assert_eq!(memory.address_space[0x0000], 0xBB);
        assert_eq!(previous, 0xAA);
    }
}
