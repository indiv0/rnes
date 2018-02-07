/// All of the opcodes available on the NES.
#[allow(non_camel_case_types)]
#[derive(Debug)]
pub enum Opcode {
    LDA_IMM = 0xA9,
    LDA_ZPAGE = 0xA5,
    LDA_ABS = 0xAD,
    LDA_ABSX = 0xBD,
    Unimplemented,
}

impl From<u8> for Opcode {
    fn from(byte: u8) -> Self {
        use self::Opcode::*;

        match byte {
            0xA9 => LDA_IMM,
            0xAD => LDA_ABS,
            0xA5 => LDA_ZPAGE,
            0xBD => LDA_ABSX,
            _ => Unimplemented,
        }
    }
}
