#![cfg_attr(feature="clippy", allow(double_parens))]

use nom::{le_u8, Err as NomError, Needed};

/// Constant string located at the beginning of every iNES file.
const HEADER_START: &str = "NES";

/// An error which occurs while parsing a NES ROM.
// TODO: hide nom errors from the external interface.
#[derive(Debug)]
pub enum Error {
    /// A `nom` error occured while parsing the ROM.
    Nom(NomError),
    /// The input data provided was incomplete.
    ///
    /// May include a `Needed` enum specifying the amount of needed data.
    Incomplete(Needed),
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
    // TODO:
    // Trainer, if present (0 or 512 bytes)
    // PRG ROM data (16384 * x bytes)
    // CHR ROM data, if present (8192 * y bytes)
    // PlayChoice PROM, if present (16 bytes Data, 16 bytes CounterOut) (this is
    // often missing, see PC10 ROM-Images for details)
}

impl Default for ROM {
    fn default() -> Self {
        Self {
            header: Header::default(),
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
/// | 6        | 4-7             | Lower nybble of the ROM mapper number                         |
/// |          | 3               | Four-screen VRAM layout                                       |
/// |          | 2               | Trainer (512 B) is present (at `$7000-$71FF`)                 |
/// |          | 1               | Persistent (battery-backed) RAM is present (at `$6000-$7FFF`) |
/// |          | 0               | Mirroring (0 = horizontal, 1 = vertical)                      |
/// | 7        | 4-7             | Upper nybble of the ROM mapper number                         |
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
    prg_rom_size: u8,
    /// Size of CHR ROM (in 8 KB pages).
    chr_size: u8,
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
    prg_ram_size: u8,
    /// TV system (NTSC or PAL).
    tv_system: TvSystem,
}

impl Default for Header {
    fn default() -> Self {
        Self {
            prg_rom_size: 0,
            chr_size: 0,
            mirroring: Mirroring::Horizontal,
            persistent_memory: false,
            trainer: false,
            ignore_mirroring_control: false,
            unisystem: false,
            playchoice: false,
            mapper: 1,
            prg_ram_size: 0,
            tv_system: TvSystem::NTSC,
        }
    }
}

/// Parses the provided byte string into a NES ROM.
pub fn parse_rom(input: &[u8]) -> Result<ROM, Error> {
    use nom::IResult::*;
    use self::Error;

    match rom(input) {
        Done(_rest, output) => Ok(output),
        Error(err) => Err(Error::Nom(err)),
        Incomplete(needed) => Err(Error::Incomplete(needed)),
    }
}

/// Take the next bit as a `bool`.
named!(take_bool<(&[u8], usize), bool>, map!(take_bits!(u8, 1), |v| v != 0 ));

/// Take the next 4 bits as a nibble (`u4` represented with a `u8`).
named!(take_nibble<(&[u8], usize), u8>, take_bits!(u8, 4));

named!(rom<&[u8], ROM>,
    do_parse!(
        header: header >>
        (ROM { header })
    )
);

named!(flags_6<(&[u8], usize), (u8, bool, bool, bool, Mirroring)>,
    do_parse!(
        mapper_lower_nibble:        take_nibble >>
        ignore_mirroring_control:   take_bool >>
        trainer:                    take_bool >>
        persistent_memory:          take_bool >>
        mirroring:                  map!(
            take_bool,
            |m| if m {
                Mirroring::Vertical
            } else {
                Mirroring::Horizontal
            }
        ) >>
        ((
            mapper_lower_nibble,
            ignore_mirroring_control,
            trainer,
            persistent_memory,
            mirroring,
        ))
    )
);

named!(flags_7<(&[u8], usize), (u8, bool, bool, bool)>,
    do_parse!(
        mapper_upper_nibble: take_nibble >>
        nes_2_flags:         alt!(
            preceded!(tag_bits!(u8, 2, 0b10), value!(true)) |
            preceded!(take_bits!(u8, 2), value!(false))
        ) >>
        playchoice:         take_bool >>
        unisystem:          take_bool >>
        ((
            mapper_upper_nibble,
            nes_2_flags,
            playchoice,
            unisystem,
        ))
    )
);

named!(flags_9<(&[u8], usize), TvSystem>,
    do_parse!(
                    take_bits!(u8, 7) >> // Reserved
        tv_system:  map!(
            take_bool,
            |s| if s {
                TvSystem::PAL
            } else {
                TvSystem::NTSC
            }
        ) >>
        (tv_system)
    )
);

named!(header<&[u8], Header>,
    do_parse!(
                        tag!(HEADER_START) >>
        prg_rom_size:   le_u8 >>
        chr_size:       le_u8 >>
        flags_6:        bits!(flags_6) >>
        flags_7:        bits!(flags_7) >>
        prg_ram_size:   le_u8 >>
        flags_9:        bits!(flags_9) >>
        _flags_10:      le_u8 >>
        trailing_bytes: take!(5) >>
        ({
            // If bits 2-3 of byte 7 are equal to 2, then flags 8-15 are in the
            // NES 2.0 format.
            let nes_2_flags = flags_7.1;

            // Calculate the mapper number by merging the lower and upper
            // nibbles.
            let mut mapper = (flags_7.0 << 4) | flags_6.0;

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
                prg_rom_size,
                chr_size,
                mirroring: flags_6.4,
                persistent_memory: flags_6.3,
                trainer: flags_6.2,
                ignore_mirroring_control: flags_6.1,
                unisystem: flags_7.3,
                playchoice: flags_7.2,
                mapper,
                prg_ram_size,
                tv_system: flags_9,
            }
        })
    )
);

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::io::Read;
    use super::{header, rom, Header, ROM};
    use test::Bencher;

    const HEADER_BYTES: [u8; 16] = [
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

    #[bench]
    fn bench_parse_header(b: &mut Bencher) {
        b.iter(|| header(&HEADER_BYTES));
    }

    #[test]
    fn parse_header() {
        let header = header(&HEADER_BYTES).unwrap().1;

        assert_eq!(header, Header {
            prg_rom_size: 16,
            ..Default::default()
        });
    }

    #[test]
    fn parse_header_example_file() {
        let data = read_file_to_bytes(TEST_ROM_PATH);

        let header = header(&data).unwrap().1;

        assert_eq!(header, Header {
            prg_rom_size: 16,
            chr_size: 1,
            ..Default::default()
        });
    }

    #[test]
    fn parse_rom_example_file() {
        let data = read_file_to_bytes(TEST_ROM_PATH);

        let rom = rom(&data).unwrap().1;

        assert_eq!(rom, ROM {
            header: Header {
                prg_rom_size: 16,
                chr_size: 1,
                ..Default::default()
            },
        });
    }
}
