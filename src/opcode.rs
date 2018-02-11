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
        }

        impl Opcode {
            /// Decodes an opcode into an executable CPU instruction.
            pub fn decode(self) -> Instruction {
                use instruction::AddressingMode::*;
                use opcode::Opcode::*;

                match self {
                    $(
                        $opcode => Instruction::new(self, $addressingMode),
                    )*
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
                    _ => panic!("Unknown opcode"),
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
    // Branch if Carry Clear
    (BCC, 0x90, Relative),
    // Branch if Carry Set
    (BCS, 0xB0, Relative),
    // Branch if Equal
    (BEQ, 0xF0, Relative),
    // Bit Test
    (BIT_ZPAGE, 0x24, ZeroPage),
    (BIT_ABS, 0x2C, Absolute),
    // Branch if Minus
    (BMI, 0x30, Relative),
    // Branch if Not Equal
    (BNE, 0xD0, Relative),
    // Branch if Positive
    (BPL, 0x10, Relative),
    // Force Interrupt
    (BRK, 0x00, Implicit),
    // Branch if Overflow Clear
    (BVC, 0x50, Relative),
    // Branch if Overflow Set
    (BVS, 0x70, Relative),
    // Clear Carry Flag
    (CLC, 0x18, Implicit),
    // Clear Decimal Mode
    (CLD, 0xD8, Implicit),
    // Clear Interrupt Disable
    (CLI, 0x58, Implicit),
    // Clear Overflow Flag
    (CLV, 0xB8, Implicit),
    // Compare
    (CMP_IMM, 0xC9, Immediate),
    (CMP_ZPAGE, 0xC5, ZeroPage),
    (CMP_ZPAGEX, 0xD5, ZeroPageX),
    (CMP_ABS, 0xCD, Absolute),
    (CMP_ABSX, 0xDD, AbsoluteX),
    (CMP_ABSY, 0xD9, AbsoluteY),
    (CMP_INDX, 0xC1, IndirectX),
    (CMP_INDY, 0xD1, IndirectY),
    // Compare X Register
    (CPX_IMM, 0xE0, Immediate),
    (CPX_ZPAGE, 0xE4, ZeroPage),
    (CPX_ABS, 0xEC, Absolute),
    // Compare Y Register
    (CPY_IMM, 0xC0, Immediate),
    (CPY_ZPAGE, 0xC4, ZeroPage),
    (CPY_ABS, 0xCC, Absolute),
    // Decrement Memory
    (DEC_ZPAGE, 0xC6, ZeroPage),
    (DEC_ZPAGEX, 0xD6, ZeroPageX),
    (DEC_ABS, 0xCE, Absolute),
    (DEC_ABSX, 0xDE, AbsoluteX),
    // Decrement X Register
    (DEX, 0xCA, Implicit),
    // Decrement Y Register
    (DEY, 0x88, Implicit),
    // Exclusive OR
    (EOR_IMM, 0x49, Immediate),
    (EOR_ZPAGE, 0x45, ZeroPage),
    (EOR_ZPAGEX, 0x55, ZeroPageX),
    (EOR_ABS, 0x4D, Absolute),
    (EOR_ABSX, 0x5D, AbsoluteX),
    (EOR_ABSY, 0x59, AbsoluteY),
    (EOR_INDX, 0x41, IndirectX),
    (EOR_INDY, 0x51, IndirectY),
    // Increment Memory
    (INC_ZPAGE, 0xE6, ZeroPage),
    (INC_ZPAGEX, 0xF6, ZeroPageX),
    (INC_ABS, 0xEE, Absolute),
    (INC_ABSX, 0xFE, AbsoluteX),
    // Increment X Register
    (INX, 0xE8, Implicit),
    // Increment Y Register
    (INY, 0xC8, Implicit),
    // Jump
    (JMP_ABS, 0x4C, Absolute),
    (JMP_IND, 0x6C, Indirect),
    // Jump to Subroutine
    (JSR, 0x20, Absolute),
    // Load Accumulator
    (LDA_IMM, 0xA9, Immediate),
    (LDA_ZPAGE, 0xA5, ZeroPage),
    (LDA_ZPAGEX, 0xB5, ZeroPageX),
    (LDA_ABS, 0xAD, Absolute),
    (LDA_ABSX, 0xBD, AbsoluteX),
    (LDA_ABSY, 0xB9, AbsoluteY),
    (LDA_INDX, 0xA1, IndirectX),
    (LDA_INDY, 0xB1, IndirectY),
    // Load X Register
    (LDX_IMM, 0xA2, Immediate),
    (LDX_ZPAGE, 0xA6, ZeroPage),
    (LDX_ZPAGEY, 0xB6, ZeroPageY),
    (LDX_ABS, 0xAE, Absolute),
    (LDX_ABSY, 0xBE, AbsoluteY),
    // Load Y Register
    (LDY_IMM, 0xA0, Immediate),
    (LDY_ZPAGE, 0xA4, ZeroPage),
    (LDY_ZPAGEX, 0xB4, ZeroPageX),
    (LDY_ABS, 0xAC, Absolute),
    (LDY_ABSX, 0xBC, AbsoluteX),
    // Logical Shift Right
    (LSR_ACC, 0x4A, Accumulator),
    (LSR_ZPAGE, 0x46, ZeroPage),
    (LSR_ZPAGEX, 0x56, ZeroPageX),
    (LSR_ABS, 0x4E, Absolute),
    (LSR_ABSX, 0x5E, AbsoluteX),
    // No Operation
    (NOP, 0xEA, Implicit),
    // Logical Inclusive OR
    (ORA_IMM, 0x09, Immediate),
    (ORA_ZPAGE, 0x05, ZeroPage),
    (ORA_ZPAGEX, 0x15, ZeroPageX),
    (ORA_ABS, 0x0D, Absolute),
    (ORA_ABSX, 0x1D, AbsoluteX),
    (ORA_ABSY, 0x19, AbsoluteY),
    (ORA_INDX, 0x01, IndirectX),
    (ORA_INDY, 0x11, IndirectY),
    // Push Accumulator
    (PHA, 0x48, Implicit),
    // Push Processor Status
    (PHP, 0x08, Implicit),
    // Pull Accumulator
    (PLA, 0x68, Implicit),
    // Pull Processor Status
    (PLP, 0x28, Implicit),
    // Rotate Left
    (ROL_ACC, 0x2A, Accumulator),
    (ROL_ZPAGE, 0x26, ZeroPage),
    (ROL_ZPAGEX, 0x36, ZeroPageX),
    (ROL_ABS, 0x2E, Absolute),
    (ROL_ABSX, 0x3E, AbsoluteX),
    // Rotate Right
    (ROR_ACC, 0x6A, Accumulator),
    (ROR_ZPAGE, 0x66, ZeroPage),
    (ROR_ZPAGEX, 0x76, ZeroPageX),
    (ROR_ABS, 0x6E, Absolute),
    (ROR_ABSX, 0x7E, AbsoluteX),
    // Return from Interrupt
    (RTI, 0x40, Implicit),
    // Return from Subroutine
    (RTS, 0x60, Implicit),
    // Subtract with Carry
    (SBC_IMM, 0xE9, Immediate),
    (SBC_ZPAGE, 0xE5, ZeroPage),
    (SBC_ZPAGEX, 0xF5, ZeroPageX),
    (SBC_ABS, 0xED, Absolute),
    (SBC_ABSX, 0xFD, AbsoluteX),
    (SBC_ABSY, 0xF9, AbsoluteY),
    (SBC_INDX, 0xE1, IndirectX),
    (SBC_INDY, 0xF1, IndirectY),
    // Set Carry Flag
    (SEC, 0x38, Implicit),
    // Set Decimal Flag
    (SED, 0xF8, Implicit),
    // Set Interrupt Disable
    (SEI, 0x78, Implicit),
    // Store Accumulator
    (STA_ZPAGE, 0x85, ZeroPage),
    (STA_ZPAGEX, 0x95, ZeroPageX),
    (STA_ABS, 0x8D, Absolute),
    (STA_ABSX, 0x9D, AbsoluteX),
    (STA_ABSY, 0x99, AbsoluteY),
    (STA_INDX, 0x81, IndirectX),
    (STA_INDY, 0x91, IndirectY),
    // Store X Register
    (STX_ZPAGE, 0x86, ZeroPage),
    (STX_ZPAGEY, 0x96, ZeroPageY),
    (STX_ABS, 0x8E, Absolute),
    // Store Y Register
    (STY_ZPAGE, 0x84, ZeroPage),
    (STY_ZPAGEX, 0x94, ZeroPageX),
    (STY_ABS, 0x8C, Absolute),
    // Transfer Accumulator to X
    (TAX, 0xAA, Implicit),
    // Transfer Accumulator to Y
    (TAY, 0xA8, Implicit),
    // Transfer Stack Pointer to X
    (TSX, 0xBA, Implicit),
    // Transfer X to Accumulator
    (TXA, 0x8A, Implicit),
    // Transfer X to Stack Pointer
    (TXS, 0x9A, Implicit),
    // Transfer Y to Accumulator
    (TYA, 0x98, Implicit)
);
