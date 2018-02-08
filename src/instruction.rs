use opcode::Opcode;

/// Memory addressing modes available to NES CPU instructions.
///
/// NES memory has several addressing modes available, as can be seen in the
/// following table:
///
/// | Mode          | Instruction  | Action               |
/// |---------------|--------------|----------------------|
/// | Immediate     | LDA #$EA     | A <- $EA             |
/// | Absolute      | LDA $0314    | A <- M($0314)        |
/// | Absolute, X   | LDA $0314, X | A <- M($0314 + X)    |
/// | Absolute, Y   | LDA $0314, Y | A <- M($0314 + Y)    |
/// | Zeropage      | LDA $02      | A <- M($02)          |
/// | Zeropage, X   | LDA $02, X   | A <- M($02 + X)      |
/// | Zeropage, Y   | LDA $02, Y   | A <- M($02 + Y)      |
/// | (Zeropage, X) | LDA ($02, X) | A <- M(PTR($02 + X)) |
/// | (Zeropage), Y | LDA ($02), Y | A <- M(PTR($02) + Y) |
pub enum AddressingMode {
    Immediate,
    Absolute,
    AbsoluteX,
    _AbsoluteY,
    ZeroPage,
    _ZeroPageX,
    _ZeroPageY,
    _IndirectX,
    _IndirectY,
}

/// An executable instruction for the NES CPU.
pub struct Instruction {
    opcode: Opcode,
    addressing_mode: Option<AddressingMode>,
}

impl Instruction {
    /// Constructs a new `Instruction`.
    pub fn new(
        opcode: Opcode,
        addressing_mode: Option<AddressingMode>,
    ) -> Self {
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
    pub fn addressing_mode(&self) -> Option<&AddressingMode> {
        self.addressing_mode.as_ref()
    }
}
