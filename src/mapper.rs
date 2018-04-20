use memory::Address;
use rom::ROM;
use util::{CHR_RAM_PAGE_SIZE, CHR_ROM_PAGE_SIZE, PRG_RAM_PAGE_SIZE, PRG_ROM_PAGE_SIZE};

/// Trait for 16-bit addressed memory management operations on a memory mapper.
///
/// This trait allows for basic 16-bit memory functionality.
/// For example, this trait allows you to store and fetch values at specified
/// memory addresses in the PRG ROM/RAM and/or CHR ROM/RAM.
trait Mapper {
    /// Fetches the value at the specified memory address in the PRG.
    fn fetch_prg(&self, address: Address) -> u8;

    /// Fetches the value at the specified memory address in the CHR.
    fn fetch_chr(&self, address: Address) -> u8;

    /// Stores the value at the specified memory address in the PRG and returns
    /// the previously stored value.
    fn store_prg(&mut self, address: Address, value: u8) -> u8;

    /// Stores the value at the specified memory address in the CHR and returns
    /// the previously stored value.
    fn store_chr(&mut self, address: Address, value: u8) -> u8;
}

/// NROM (Mapper 0)
#[derive(Debug)]
pub struct NROM {
    rom: ROM,

    // PRG ROM
    prg_rom_size: usize,

    // PRG RAM
    prg_ram: Vec<u8>,
    prg_ram_size: usize,

    // CHR ROM/RAM
    chr_ram: Option<Vec<u8>>,
    chr_size: usize,
    use_chr_ram: bool,
}

impl NROM {
    /// Creates a new `NROM` mapper from the provided `ROM`.
    pub fn new(rom: ROM) -> Self {
        // Calculate the size (in bytes) of each of the ROM/RAM banks.
        let prg_rom_size = rom.header().prg_rom_pages() as usize * PRG_ROM_PAGE_SIZE;
        let chr_rom_size = rom.header().chr_rom_pages() as usize * CHR_ROM_PAGE_SIZE;
        let prg_ram_size = {
            let prg_ram_pages = match rom.header().prg_ram_pages() as usize {
                // A value of 0 for the number of PRG RAM pages implies 1 PRG
                // RAM page for compatibility.
                0 => 1,
                prg_ram_pages => prg_ram_pages,
            };
            prg_ram_pages * PRG_RAM_PAGE_SIZE
        };

        let prg_ram = Vec::with_capacity(prg_ram_size);

        // If CHR ROM **page count** is 0 then we use CHR RAM instead.
        let use_chr_ram = rom.header().chr_rom_pages() == 0;

        let chr_size;
        let chr_ram = if use_chr_ram {
            chr_size = CHR_RAM_PAGE_SIZE;
            Some(Vec::with_capacity(chr_size))
        } else {
            chr_size = chr_rom_size;
            None
        };

        Self {
            rom,
            prg_rom_size,
            prg_ram,
            prg_ram_size,
            chr_ram,
            chr_size,
            use_chr_ram,
        }
    }
}

impl Mapper for NROM {
    fn fetch_prg(&self, address: Address) -> u8 {
        // FIXME: replace this with a correct implementation.
        self.prg_ram[address as usize]
    }

    fn fetch_chr(&self, address: Address) -> u8 {
        // FIXME: replace this with a correct implementation.
        if let Some(ref chr_ram) = self.chr_ram {
            chr_ram[address as usize]
        } else {
            self.rom.chr_rom[address as usize]
        }
    }

    fn store_prg(&mut self, address: Address, value: u8) -> u8 {
        // FIXME: replace this with a correct implementation.
        let old_value = self.rom.prg_rom[address as usize];
        self.rom.prg_rom[address as usize] = value;
        old_value
    }

    fn store_chr(&mut self, address: Address, value: u8) -> u8 {
        // FIXME: replace this with a correct implementation.
        let chr = if let Some(ref mut chr_ram) = self.chr_ram {
            chr_ram
        } else {
            &mut self.rom.chr_rom
        };

        let old_value = chr[address as usize];
        chr[address as usize] = value;
        old_value
    }
}

#[cfg(test)]
mod tests {
    use super::NROM;
    use rom::ROM;
    use std::fs::File;

    const TEST_ROM_PATH: &str = "tests/sample-data/nes-test-roms/blargg_nes_cpu_test5/official.nes";

    /// Load the ROM located at the provided file path.
    fn load_rom_from_path(path: &str) -> ROM {
        let mut f = File::open(path).expect(&format!("File not found: {}", path));
        ROM::load(&mut f).expect(&format!("Failed to load ROM: {}", path))
    }

    #[test]
    fn nmap_new() {
        let rom = load_rom_from_path(TEST_ROM_PATH);

        assert_eq!(rom.header().prg_rom_pages(), 16);
        assert_eq!(rom.header().chr_rom_pages(), 1);

        let mapper = NROM::new(rom);
        assert_eq!(mapper.prg_rom_size, mapper.rom.prg_rom.capacity());
        assert_eq!(mapper.prg_ram_size, mapper.prg_ram.capacity());
        assert_eq!(mapper.chr_size, mapper.rom.chr_rom.capacity());
        assert_eq!(mapper.chr_ram, None);
    }
}
