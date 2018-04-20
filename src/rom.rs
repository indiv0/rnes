// These lines are workarounds to issues in nom macros.
#![cfg_attr(feature="clippy", allow(useless_let_if_seq, double_parens))]

use nom::{le_u8, Err as NomError, Needed};
use std::fmt;
use std::io::{Error as IoError, Read};
use util::{
    BYTES_PER_KB,
    CHR_ROM_PAGE_SIZE,
    PRG_RAM_PAGE_SIZE,
    PRG_ROM_PAGE_SIZE,
};

/// Constant string located at the beginning of every iNES file.
const HEADER_START: &str = "NES";

/// An error which occurs while parsing a NES ROM.
// TODO: hide nom errors from the external interface.
#[derive(Debug)]
pub enum Error {
    /// Internal IO error.
    Io(IoError),
    /// A `nom` error occured while parsing the ROM.
    Nom(NomError),
    /// The input data provided was incomplete.
    ///
    /// May include a `Needed` enum specifying the amount of needed data.
    Incomplete(Needed),
}

impl From<IoError> for Error {
    fn from(value: IoError) -> Self {
        Error::Io(value)
    }
}

#[derive(Debug, PartialEq)]
pub enum Mirroring {
    Horizontal,
    Vertical,
}

#[derive(Debug, PartialEq)]
pub enum TvSystem {
    NTSC,
    PAL,
}

/// A NES cartridge.
///
/// # Specification
///
/// These struct definitions and associated parsing code were developed to
/// support the [**.NES file format**][nes-file-format] (AKA **iNES format**;
/// file extension `.nes`) developed by Marat Fayzullin for his
/// [iNES emulator][ines-emulator].
///
/// The ROM and header implementations attempt to follow the
/// [official iNES file format specification][nes-file-format].
/// Optional features of the specification are only partially supported, and
/// will be implemented in the future along with
/// [NES 2.0 file format][nes-2-file-format] support.
///
/// # Structure
///
/// Structure of a .NES file:
///
/// | Section                   | Size (B)     | Optional? |
/// |---------------------------|--------------|-----------|
/// | Header                    | 16           |           |
/// | Trainer                   | 512          | Yes       |
/// | PRG ROM data              | 16384 * `x`  |           |
/// | CHR ROM data              | 8192 * `y`   | Yes       |
/// | PlayChoice INST-ROM       | 8192         | Yes       |
/// | PlayChoice PROM           | 16 + 16 = 32 | Yes       |
/// | Title                     | 127 or 128   | Yes       |
///
/// [ines-emulator]: http://fms.komkon.org/iNES/
/// [nes-file-format]: http://fms.komkon.org/EMUL8/NES.html#LABM "iNES File Format Specification"
/// [nes-2-file-format]: http://forums.nesdev.com/viewtopic.php?p=17727#p17727 "NES 2.0 \"Official\" Specification"
#[derive(Debug, PartialEq)]
pub struct ROM {
    /// Header.
    header: Header,
    /// PRG ROM data.
    // TODO: make this private.
    pub prg_rom: Vec<u8>,
    /// CHR ROM data.
    // TODO: make this private.
    pub chr_rom: Vec<u8>,
    // TODO:
    // PlayChoice INST-ROM
    // PlayChoice PROM, if present (16 bytes Data, 16 bytes CounterOut) (this is
    // often missing, see PC10 ROM-Images for details)
    // Title
}

impl ROM {
    /// Load and parse the provided input into a NES ROM.
    pub fn load(r: &mut Read) -> Result<ROM, Error> {
        use nom::IResult::*;
        use self::Error;

        let mut data = Vec::new();
        r.read_to_end(&mut data)?;

        match rom(&data) {
            Done(_rest, output) => Ok(output),
            Error(err) => Err(Error::Nom(err)),
            Incomplete(needed) => Err(Error::Incomplete(needed)),
        }
    }

    pub fn header(&self) -> &Header {
        &self.header
    }
}

impl Default for ROM {
    fn default() -> Self {
        Self {
            header: Header::default(),
            prg_rom: Vec::new(),
            chr_rom: Vec::new(),
        }
    }
}

/// A NES cartridge header.
///
/// # Structure
///
/// Structure of a .NES header:
///
/// | Byte(s)  | Bit(s)          | Contents                                                      |
/// |----------|-----------------|---------------------------------------------------------------|
/// | 0-3      |                 | "NES<EOF>" string constant present in all .NES files          |
/// | 4        |                 | PRG ROM page count (16 KB each)                               |
/// | 5        |                 | CHR ROM page count (8 KB each)                                |
/// | 6        | 4-7             | Lower nibble of the ROM mapper number                         |
/// |          | 3               | Four-screen VRAM layout                                       |
/// |          | 2               | Trainer (512 B) is present (at `$7000-$71FF`)                 |
/// |          | 1               | Persistent (battery-backed) RAM is present (at `$6000-$7FFF`) |
/// |          | 0               | Mirroring (0 = horizontal, 1 = vertical)                      |
/// | 7        | 4-7             | Upper nibble of the ROM mapper number                         |
/// |          | 1-3             | Reserved (**must be zeroes**)                                 |
/// |          | 0               | VS Unisystem (0 = false, 1 = true)                            |
/// | 8        |                 | PRG RAM page count (8 KB each)                                |
/// | 9        | 1-7             | Reserved (**must be zeroes**)                                 |
/// |          | 0               | TV system (0 = NTSC, 1 = PAL)                                 |
/// | 10-15    |                 | Reserved (**must be zeroes**)                                 |
///
/// # Notes
///
/// * Value `0` for CHR ROM size means the board uses CHR RAM
///
/// ## Compatibility
/// ### With earlier versions of the .NES format
///
/// * Value `0` for PRG RAM size implies 1x8 KB RAM page.
#[derive(Debug, PartialEq)]
pub struct Header {
    /// Size of PRG ROM (in 16 KB pages).
    prg_rom_pages: u8,
    /// Size of CHR ROM (in 8 KB pages).
    chr_rom_pages: u8,
    /// Nametable mirroring (horizontal or vertical).
    mirroring: Mirroring,
    /// Cartridge contains battery-backed PRG RAM (`$6000-$7FFF`) or other
    /// persistent memory.
    persistent_memory: bool,
    /// Whether or not a 512 B trainer is present.
    trainer: bool,
    /// Ignore the above mirroring control; instead provide four-screen VRAM.
    ignore_mirroring_control: bool,
    /// Whether or not the cartridge is intended for a VS Unisystem.
    unisystem: bool,
    /// Whether or not the cartridge is intended for a PlayChoice-10 bit.
    playchoice: bool,
    /// Number of the mapper to use.
    mapper: u8,
    /// Size of PRG RAM (in 8 KB pages).
    prg_ram_pages: u8,
    /// TV system (NTSC or PAL).
    tv_system: TvSystem,
}

impl Header {
    pub fn prg_rom_pages(&self) -> u8 {
        self.prg_rom_pages
    }

    pub fn chr_rom_pages(&self) -> u8 {
        self.chr_rom_pages
    }

    pub fn prg_ram_pages(&self) -> u8 {
        self.prg_ram_pages
    }
}

impl Default for Header {
    fn default() -> Self {
        Self {
            prg_rom_pages: 0,
            chr_rom_pages: 0,
            mirroring: Mirroring::Horizontal,
            persistent_memory: false,
            trainer: false,
            ignore_mirroring_control: false,
            unisystem: false,
            playchoice: false,
            mapper: 1,
            prg_ram_pages: 0,
            tv_system: TvSystem::NTSC,
        }
    }
}

impl fmt::Display for Header {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "<Header Mapper:{}, PRG ROM:{} KB, CHR ROM:{} KB, PRG RAM:{} KB>",
            self.mapper,
            self.prg_rom_pages as usize * PRG_ROM_PAGE_SIZE / BYTES_PER_KB,
            self.chr_rom_pages as usize * CHR_ROM_PAGE_SIZE / BYTES_PER_KB,
            self.prg_ram_pages as usize * PRG_RAM_PAGE_SIZE / BYTES_PER_KB,
        )
    }
}

named!(
    rom<&[u8], ROM>,
    do_parse!(
        header: header >>
        // Load the PRG ROM.
        prg_rom: take!(header.prg_rom_pages as usize * PRG_ROM_PAGE_SIZE) >>
        // Load the CHR ROM.
        chr_rom: take!(header.chr_rom_pages as usize * CHR_ROM_PAGE_SIZE) >>
        ({
            ROM {
                header,
                prg_rom: prg_rom.to_vec(),
                chr_rom: chr_rom.to_vec(),
            }
        })
    )
);

named!(
    pub header<&[u8], Header>,
    bits!(do_parse!(
        // Bytes 0-3
                                    bytes!(tag!(HEADER_START)) >>
        // Bytes 4-5
        prg_rom_pages:              bytes!(le_u8) >>
        chr_rom_pages:              bytes!(le_u8) >>
        // Flags 6
        mapper_nibble_lower:        take_nibble >>
        ignore_mirroring_control:   take_bool >>
        trainer:                    take_bool >>
        persistent_memory:          take_bool >>
        mirroring:
            map!(
                take_bool,
                |m| if m {
                    Mirroring::Vertical
                } else {
                    Mirroring::Horizontal
                }
            ) >>
        // Flags 7
        mapper_nibble_upper:        take_nibble >>
        nes_2_flags:
            // If bits 2-3 of byte 7 are equal to 2, then flags 8-15 are in the
            // NES 2.0 format.
            alt!(
                preceded!(tag_bits!(u8, 2, 0b10), value!(true)) |
                preceded!(take_bits!(u8, 2), value!(false))
            ) >>
        playchoice:                 take_bool >>
        unisystem:                  take_bool >>
        // Byte 8
        prg_ram_pages:              bytes!(le_u8) >>
        // Flags 9
        tv_system:
            preceded!(
                take_bits!(u8, 7), // Reserved
                map!(
                    take_bool,
                    |s| if s {
                        TvSystem::PAL
                    } else {
                        TvSystem::NTSC
                    }
                )
            ) >>
        // Flags 10
        _flags_10:      bytes!(le_u8) >>
        // Bytes 11-15
        trailing_bytes: bytes!(take!(5)) >>
        ({
            // Calculate the mapper number by merging the lower and upper
            // nibbles.
            let mut mapper = (mapper_nibble_upper << 4) | mapper_nibble_lower;

            // If the trailing 4 bytes are non-zero and the header is not marked
            // as being in the NES 2.0 format, then we want to mask off the
            // upper 4 bits of the mapper number.
            // This is done because older versions of the iNES emulator ignored
            // bytes 7-15, and some ROM management tools would write messages in
            // there.
            let trailing_bytes_are_null = trailing_bytes[1..] == [0x00, 0x00, 0x00, 0x00];
            if !trailing_bytes_are_null && !nes_2_flags {
                mapper &= 0b0000_1111;
            }

            Header {
                prg_rom_pages,
                chr_rom_pages,
                mirroring,
                persistent_memory,
                trainer,
                ignore_mirroring_control,
                unisystem,
                playchoice,
                mapper,
                prg_ram_pages,
                tv_system,
            }
        })
    ))
);

/// Take the next bit as a `bool`.
named!(take_bool<(&[u8], usize), bool>, map!(take_bits!(u8, 1), |v| v != 0 ));

/// Take the next 4 bits as a nibble (`u4` represented with a `u8`).
named!(take_nibble<(&[u8], usize), u8>, take_bits!(u8, 4));

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::Read;
    use super::{header, rom, Header};

    pub const HEADER_BYTES: [u8; 16] = [
        0x4E, 0x45, 0x53, 0x1A, 0x10, 0x00, 0x10, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    ];
    const TEST_ROM_PATH: &str = "tests/sample-data/nes-test-roms/blargg_nes_cpu_test5/official.nes";

    /// Read the file at the specified file path to a `Vec<u8>`.
    fn read_file_to_bytes(path: &str) -> Vec<u8> {
        let mut f = File::open(path)
            .expect(&format!("File not found: {}", path));
        let mut contents = Vec::new();
        f.read_to_end(&mut contents)
            .expect(&format!("Failed to read the file: {}", path));
        contents
    }

    #[test]
    fn parse_header() {
        let header = header(&HEADER_BYTES).unwrap().1;

        assert_eq!(header, Header {
            prg_rom_pages: 16,
            ..Default::default()
        });
    }

    #[test]
    fn parse_header_example_file() {
        let data = read_file_to_bytes(TEST_ROM_PATH);

        let header = header(&data).unwrap().1;

        assert_eq!(header, Header {
            prg_rom_pages: 16,
            chr_rom_pages: 1,
            ..Default::default()
        });
    }

    #[test]
    fn parse_rom_example_file() {
        let data = read_file_to_bytes(TEST_ROM_PATH);

        let rom = rom(&data).unwrap().1;

        assert_eq!(rom.header, Header {
            prg_rom_pages: 16,
            chr_rom_pages: 1,
            ..Default::default()
        });
        assert_eq!(rom.prg_rom[0], 0x4C);
        assert_eq!(rom.chr_rom[0], 0x00);
    }
}

#[cfg(all(feature = "nightly", test))]
mod bench {
    extern crate test;

    use self::test::Bencher;
    use super::header;
    use super::tests::HEADER_BYTES;

    #[bench]
    fn bench_parse_header(b: &mut Bencher) {
        b.iter(|| header(&HEADER_BYTES));
    }
}
