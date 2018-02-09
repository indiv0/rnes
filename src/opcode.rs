use instruction::Instruction;

macro_rules! opcodes {
    ( $( ($opcode:tt, $id:expr, $addressingMode:expr) ),* ) => {
        /// All of the opcodes available on the NES.
        #[allow(non_camel_case_types)]
        #[derive(Clone, Debug)]
        pub enum Opcode {
            $(
                $opcode = $id,
            )*
            Unimplemented,
        }

        impl Opcode {
            /// Decodes an opcode into an executable CPU instruction.
            pub fn decode(self) -> Instruction {
                use instruction::AddressingMode::*;
                use opcode::Opcode::*;

                match self {
                    $(
                        $opcode => Instruction::new(self, Some($addressingMode)),
                    )*
                    Unimplemented => panic!("Unimplemented opcode"),
                }
            }
        }

        impl From<u8> for Opcode {
            fn from(byte: u8) -> Self {
                use self::Opcode::*;

                match byte {
                    $(
                        $id => $opcode,
                    )*
                    _ => Unimplemented,
                }
            }
        }
    };
}

opcodes!(
    // Add with Carry
    (ADC_IMM, 0x69, Immediate),
    (ADC_ZPAGE, 0x65, ZeroPage),
    (ADC_ZPAGEX, 0x75, ZeroPageX),
    (ADC_ABS, 0x6D, Absolute),
    (ADC_ABSX, 0x7D, AbsoluteX),
    (ADC_ABSY, 0x79, AbsoluteY),
    (ADC_INDX, 0x61, IndirectX),
    (ADC_INDY, 0x71, IndirectY),
    // Logical AND
    (AND_IMM, 0x29, Immediate),
    (AND_ZPAGE, 0x25, ZeroPage),
    (AND_ZPAGEX, 0x35, ZeroPageX),
    (AND_ABS, 0x2D, Absolute),
    (AND_ABSX, 0x3D, AbsoluteX),
    (AND_ABSY, 0x39, AbsoluteY),
    (AND_INDX, 0x21, IndirectX),
    (AND_INDY, 0x31, IndirectY),
    // Arithmetic shift left
    (ASL_ACC, 0x0A, Accumulator),
    (ASL_ZPAGE, 0x06, ZeroPage),
    (ASL_ZPAGEX, 0x16, ZeroPageX),
    (ASL_ABS, 0x0E, Absolute),
    (ASL_ABSX, 0x1E, AbsoluteX),
    // Load Accumulator
    (LDA_IMM, 0xA9, Immediate),
    (LDA_ZPAGE, 0xA5, ZeroPage),
    (LDA_ZPAGEX, 0xB5, ZeroPageX),
    (LDA_ABS, 0xAD, Absolute),
    (LDA_ABSX, 0xBD, AbsoluteX),
    (LDA_ABSY, 0xB9, AbsoluteY),
    (LDA_INDX, 0xA1, IndirectX),
    (LDA_INDY, 0xB1, IndirectY)
);
