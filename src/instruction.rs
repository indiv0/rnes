use opcode::Opcode;

/// Memory addressing modes available to NES CPU instructions.
///
/// NES memory has several addressing modes available, as can be seen in the
/// following table:
///
/// | Mode          | Instruction  | Action               |
/// |---------------|--------------|----------------------|
/// | Accumulator   | ASL A        | A <- A << 1          |
/// | Immediate     | LDA #$EA     | A <- $EA             |
/// | Zeropage      | LDA $02      | A <- M($02)          |
/// | Zeropage, X   | LDA $02, X   | A <- M($02 + X)      |
/// | Zeropage, Y   | LDA $02, Y   | A <- M($02 + Y)      |
/// | Relative      | BCC *+4      | PC <- PC + 4         |
/// | Absolute      | LDA $0314    | A <- M($0314)        |
/// | Absolute, X   | LDA $0314, X | A <- M($0314 + X)    |
/// | Absolute, Y   | LDA $0314, Y | A <- M($0314 + Y)    |
/// | (Indirect, X) | LDA ($02, X) | A <- M(PTR($02 + X)) |
/// | (Indirect), Y | LDA ($02), Y | A <- M(PTR($02) + Y) |
pub enum AddressingMode {
    /// The source/destination of the instruction is implied by the instruction
    /// itself (i.e. no operand).
    Implicit,
    /// Operate directly on the accumulator.
    Accumulator,
    /// Operate on an 8-bit constant specified in the instruction.
    Immediate,
    /// Address to be accessed is an 8-bit operand pointing to a memory location
    /// in the zero page ($0000-$00FF).
    ZeroPage,
    /// Address to be accessed is a zero page address calculated by taking the
    /// 8-bit operand and adding the current value of the `X` register to it.
    ZeroPageX,
    /// Address to be accessed is a zero page address calculated by taking the
    /// 8-bit operand and adding the current value of the `Y` register to it.
    ZeroPageY,
    /// Used by branch instructions; adds operand as a signed 8-bit offset to
    /// the program counter.
    Relative,
    /// Address to be accessed is the 16-bit operand following the instruction.
    Absolute,
    /// Address to be accessed is calculated by taking the 16-bit operand
    /// following the instruction and adding the current value of register `X`
    /// to it.
    AbsoluteX,
    /// Address to be accessed is calculated by taking the 16-bit operand
    /// following the instruction and adding the current value of register `Y`
    /// to it.
    AbsoluteY,
    /// The 16-bit operand is used as the location of the least significant byte
    /// of another 16-bit memory address, which is used as the real target of the
    /// instruction.
    ///
    /// # Note
    ///
    /// JMP is the only instruction which uses this addressing mode.
    Indirect,
    /// Address to be accessed is calculated by taking the 8-bit operand
    /// following the instruction, adding the current value of register `X` to
    /// it, and retrieving the value at the resulting memory address in the zero
    /// page.
    IndirectX,
    /// Address to be accessed is calculated by taking the 8-bit operand
    /// following the instruction, retrieving the value at the memory address in
    /// the zero page corresponding to the operand, and adding the current value
    /// of register `Y` to it.
    IndirectY,
}

/// An executable instruction for the NES CPU.
pub struct Instruction {
    opcode: Opcode,
    addressing_mode: AddressingMode,
}

impl Instruction {
    /// Constructs a new `Instruction`.
    pub fn new(opcode: Opcode, addressing_mode: AddressingMode) -> Self {
        Self {
            opcode,
            addressing_mode,
        }
    }

    /// Returns the opcode of this `Instruction`.
    pub fn opcode(&self) -> &Opcode {
        &self.opcode
    }

    /// Returns the addressing mode of the `Instruction`.
    pub fn addressing_mode(&self) -> &AddressingMode {
        &self.addressing_mode
    }
}
