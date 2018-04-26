use mapper::MemoryType::{self, CHRRAM, CHRROM, PRGRAM, PRGROM};
use mapper::{Fetch, Mapper, Store};
use memory::Address;
use rom::{Header, ROM};
use std::{u16, u8};
use util::{new_vec, CHR_RAM_PAGE_SIZE, PRG_RAM_PAGE_SIZE};

/// NROM (Mapper 0)
#[derive(Clone, Debug)]
pub struct NROM {
    // PRG ROM (16 KB for NROM-128, 32 KB for NROM-256)
    // PRG RAM (2 or 4 KB, not bankswitched, only in Family Basic)
    // CHR ROM (8 KB) or CHR RAM
    banks: Vec<MemoryType>,
}

impl NROM {
    /// Creates a new `NROM` mapper from the provided `ROM`.
    pub fn new(rom: ROM) -> Self {
        let ROM {
            header,
            prg_rom,
            chr_rom,
        } = rom;

        // Calculate the size (in bytes) of each of the ROM/RAM banks.
        let prg_rom_size = prg_rom.len();
        let chr_rom_size = chr_rom.len();
        let prg_ram_size = {
            let prg_ram_pages = match header.prg_ram_pages() as usize {
                // A value of 0 for the number of PRG RAM pages implies 1 PRG
                // RAM page for compatibility.
                0 => 1,
                prg_ram_pages => prg_ram_pages,
            };
            prg_ram_pages * PRG_RAM_PAGE_SIZE
        };
        let chr_ram_size = CHR_RAM_PAGE_SIZE;

        let mut banks = Vec::new();
        banks.push(PRGROM(prg_rom_size, prg_rom));
        banks.push(PRGRAM(prg_ram_size, new_vec(0x00, prg_ram_size)));

        // If CHR ROM **page count** is 0 then we use CHR RAM instead.
        let use_chr_ram = header.chr_rom_pages() == 0;

        let chr = if use_chr_ram {
            CHRRAM(chr_ram_size, new_vec(0x00, chr_ram_size))
        } else {
            CHRROM(chr_rom_size, chr_rom)
        };
        banks.push(chr);

        // The banks must never be so large as to be unaddressable.
        let sum_size: usize = banks.iter().map(|b| b.len()).sum();
        println!(
            "PRG_ROM_SIZE: {:x}\nPRG_RAM_SIZE: {:x}\nCHR_SIZE: {:x}\nSUM_SIZE: {:x}\nU16_MAX: {:x}",
            banks[0].len(),
            banks[1].len(),
            banks[2].len(),
            sum_size,
            u16::MAX,
        );

        Self { banks }
    }
}

impl Default for NROM {
    fn default() -> Self {
        let header = Header::new(1, 1, 0);
        let rom = ROM::new(header);

        Self::new(rom)
    }
}

impl Mapper for NROM {
    fn fetch(&self, address: Address) -> Option<u8> {
        assert!(address >= 0x6000);
        // PRG RAM is expected to be present.
        assert!(self.banks[1].len() > 0);

        if address >= 0x6000 && address < 0x8000 {
            let address = (address - 0x6000) & (self.banks[1].len() - 1) as u16;
            // TODO: is there a better way to enforce this assert?
            assert!((address as usize) < self.banks[1].len());
            return Some(self.banks[1].fetch(address));
        } else if address >= 0x8000 {
            let address = (address - 0x8000) & (self.banks[0].len() - 1) as u16;
            return Some(self.banks[0].fetch(address));
        } else {
            // TODO: ensure this is truly unreachable.
            unreachable!();
        }
    }

    fn store(&mut self, address: Address, value: u8) -> u8 {
        assert!(address >= 0x6000);
        // PRG RAM is expected to be present.
        assert!(self.banks[1].len() > 0);

        if address >= 0x6000 && address < 0x8000 {
            let address = (address - 0x6000) & (self.banks[1].len() - 1) as u16;
            // TODO: is there a better way to enforce this assert?
            assert!((address as usize) < self.banks[1].len());
            return self.banks[1].store(address, value);
        } else if address >= 0x8000 {
            let address = (address - 0x8000) & (self.banks[0].len() - 1) as u16;
            return self.banks[0].store(address, value);
        } else {
            unreachable!();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::NROM;
    use mapper::Mapper;
    use rom::{Header, ROM};
    use std::fs::File;
    use util::PRG_RAM_PAGE_SIZE;

    const TEST_ROM_PATH: &str = "tests/sample-data/nes-test-roms/blargg_nes_cpu_test5/official.nes";

    /// Load the ROM located at the provided file path.
    fn load_rom_from_path(path: &str) -> ROM {
        let mut f = File::open(path).expect(&format!("File not found: {}", path));
        ROM::load(&mut f).expect(&format!("Failed to load ROM: {}", path))
    }

    #[test]
    fn nmap_new() {
        let rom = load_rom_from_path(TEST_ROM_PATH);

        assert_eq!(rom.header.prg_rom_pages(), 16);
        assert_eq!(rom.header.chr_rom_pages(), 1);

        let prg_rom_capacity = rom.prg_rom.capacity();
        let chr_rom_capacity = rom.chr_rom.capacity();
        let prg_ram_pages = match rom.header.prg_ram_pages() {
            0 => 1,
            pages => pages,
        };

        let mapper = NROM::new(rom);
        assert_eq!(mapper.banks[0].len(), prg_rom_capacity);
        assert_eq!(
            mapper.banks[1].len(),
            prg_ram_pages as usize * PRG_RAM_PAGE_SIZE
        );
        assert_eq!(mapper.banks[2].len(), chr_rom_capacity);
    }

    #[test]
    fn nmap_prg_ram() {
        let mut mapper = NROM::new(ROM::new(Header::new(1, 1, 1)));

        mapper.store(0x6000, 0xAA);
        assert_eq!(mapper.fetch(0x6000), Some(0xAA));
    }

    #[test]
    fn nmap_store_prg_rom() {
        let mut mapper = NROM::new(ROM::new(Header::new(1, 1, 1)));

        mapper.store(0x8000, 0xAA);
        assert_eq!(mapper.fetch(0x8000), Some(0x00));
    }
}
