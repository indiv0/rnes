/// All of the opcodes available on the NES.
#[allow(non_camel_case_types)]
#[derive(Clone, Debug)]
pub enum Opcode {
    // Add with Carry
    ADC_IMM = 0x69,
    ADC_ZPAGE = 0x65,
    ADC_ZPAGEX = 0x75,
    ADC_ABS = 0x6D,
    ADC_ABSX = 0x7D,
    ADC_ABSY = 0x79,
    ADC_INDX = 0x61,
    ADC_INDY = 0x71,
    // Load Accumulator
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
            0x69 => ADC_IMM,
            0x65 => ADC_ZPAGE,
            0x75 => ADC_ZPAGEX,
            0x6D => ADC_ABS,
            0x7D => ADC_ABSX,
            0x79 => ADC_ABSY,
            0x61 => ADC_INDX,
            0x71 => ADC_INDY,
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
