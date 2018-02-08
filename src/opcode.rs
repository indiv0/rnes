/// All of the opcodes available on the NES.
#[allow(non_camel_case_types)]
#[derive(Clone, Debug)]
pub enum Opcode {
    LDA_IMM = 0xA9,
    LDA_ZPAGE = 0xA5,
    LDA_ZPAGEX = 0xB5,
    LDA_ABS = 0xAD,
    LDA_ABSX = 0xBD,
    LDA_ABSY = 0xB9,
    LDA_INDX = 0xA1,
    LDA_INDY = 0xB1,
    Unimplemented,
}

impl From<u8> for Opcode {
    fn from(byte: u8) -> Self {
        use self::Opcode::*;

        match byte {
            0xA9 => LDA_IMM,
            0xA5 => LDA_ZPAGE,
            0xB5 => LDA_ZPAGEX,
            0xAD => LDA_ABS,
            0xBD => LDA_ABSX,
            0xB9 => LDA_ABSY,
            0xA1 => LDA_INDX,
            0xB1 => LDA_INDY,
            _ => Unimplemented,
        }
    }
}
