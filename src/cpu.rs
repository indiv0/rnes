use instruction::Instruction;
use memory::{Address, Memory, NESMemory};
use opcode::Opcode;
use opcode::Opcode::*;

const CPU_STATUS_REGISTER_INITIAL_VALUE: u8 = 0x34; // 0x00111000 (IRQ disabled)
const CPU_STACK_POINTER_INITIAL_VALUE: u8 = 0xFD;

/// An implementation of the NES CPU.
///
/// # Architecture
///
/// The NES CPU is an 8-bit CPU with a small number of internal registers, 64 KB
/// of memory, and a 16-bit address bus. The processor is little endian and
/// expects addresses to be stored in memory least significant byte first.
pub struct CPU {
    // Registers
    /// Accumulator.
    a: u8,
    /// Index register X.
    ///
    /// # Special Functionality
    ///
    /// The X register has one special function. It can be used to get a copy of
    /// the stack pointer or change its value.
    x: u8,
    /// Index register Y.
    y: u8,
    /// Processor status.
    ///
    /// The processor status register contains flags which are set or cleared
    /// after the execution of instructions to record their results.
    /// There are also several control flags.
    /// Each flag has a single bit within the register.
    ///
    /// Flags (from LSB to MSB):
    ///
    /// * Carry flag: set if the last operation caused an overflow from bit 7 of
    ///   the result or an underflow from bit 0.
    /// * Zero flag: set if the result of the last operation was zero.
    /// * Interrupt Disable: set if the program has executed a "Set Interrupt
    ///   Disable" (SEI) instruction.
    ///   While this flag is set the processor will not respond to interrupts
    ///   from devices until it is cleared by a "Clear Interrupt Disable" (CLI)
    ///   instruction.
    /// * Decimal Mode: while this flag is set the processor will utilize the
    ///   rules of binary coded decimal (BCD) arithmetic during addition and
    ///   subtraction.
    /// * Unknown
    /// * Break Command: set when a BRK instruction has been executed an an
    ///   interrupt has been generated to process it.
    /// * Overflow Flag: set during arithmetic operations if the result has
    ///   yielded an invalid 2's complement result (e.g. adding two positive
    ///   numbers and ending up with a negative result).
    /// * Negative Flag: set if the result of the last operation had bit 7 set
    ///   to one.
    _p: u8,
    /// Program counter.
    ///
    /// Points to the address from which the next instruction byte will be
    /// fetched.
    ///
    /// Low and high 8-bit halves of this register are called PCL and PCH,
    /// respectively. The program counter may be read by pushing its value to
    /// the stack. This can be done by jumping to a subroutine or by causing an
    /// interrupt.
    pc: Address,
    /// Stack pointer.
    ///
    /// Holds the low 8 bits of the next free location on the stack.
    /// Pushing to the stack causes the stack pointer to be decremented.
    /// Popping from the stack causes it to be incremented.
    ///
    /// The top 8 bits of the stack pointer are hard-coded to `00000001`, so the
    /// stack pointer really has an 8-bit address space.
    _sp: u8,

    memory: NESMemory,
}

impl CPU {
    pub fn new() -> Self {
        let mut memory = NESMemory::new();

        // TODO: are these resets necessary?
        // Disable all channels.
        memory.store(0x4015, 0x00);
        // Enable frame IRQ
        memory.store(0x4017, 0x00);

        Self {
            a: 0,
            x: 0,
            y: 0,
            _p: CPU_STATUS_REGISTER_INITIAL_VALUE,
            pc: 0,
            _sp: CPU_STACK_POINTER_INITIAL_VALUE,
            memory,
        }
    }

    /// Execute a single instruction cycle.
    fn step(&mut self) {
        // Read the next opcode to be executed.
        let opcode = self.read_u8(self.pc).into();
        self.pc += 1;

        // Decode the opcode into an executable instruction.
        let instruction = CPU::decode(opcode);

        // If the instruction requires an operand, use the specified addressing
        // mode to determine its address.
        let operand_addr = instruction.addressing_mode().map(|addressing_mode| {
            use instruction::AddressingMode::*;

            match *addressing_mode {
                Immediate => self.addr_imm(),
                ZeroPage => self.addr_zero_page(),
                ZeroPageX => self.addr_zero_page_x(),
                Absolute => self.addr_abs(),
                AbsoluteX => self.addr_abs_x(),
                AbsoluteY => self.addr_abs_y(),
                IndirectX => self.addr_ind_x(),
                IndirectY => self.addr_ind_y(),
                _ => panic!("Unimplemented addressing mode"),
            }
        });

        match *instruction.opcode() {
            LDA_IMM |
            LDA_ZPAGE |
            LDA_ZPAGEX |
            LDA_ABS |
            LDA_ABSX |
            LDA_ABSY |
            LDA_INDX |
            LDA_INDY => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.lda(addr);
                return;
            },
            _ => panic!("Unimplemented instruction"),
        }
    }

    pub fn emulate(&mut self) {
        // TODO: reset here (e.g. a, x, y, to 0)?
        loop {
            self.step();
        }
    }

    /// Decodes an opcode into an executable CPU instruction.
    fn decode(opcode: Opcode) -> Instruction {
        use instruction::AddressingMode::*;

        match opcode {
            LDA_IMM => Instruction::new(opcode, Some(Immediate)),
            LDA_ZPAGE => Instruction::new(opcode, Some(ZeroPage)),
            LDA_ZPAGEX => Instruction::new(opcode, Some(ZeroPageX)),
            LDA_ABS => Instruction::new(opcode, Some(Absolute)),
            LDA_ABSX => Instruction::new(opcode, Some(AbsoluteX)),
            LDA_ABSY => Instruction::new(opcode, Some(AbsoluteY)),
            LDA_INDX => Instruction::new(opcode, Some(IndirectX)),
            LDA_INDY => Instruction::new(opcode, Some(IndirectY)),
            Unimplemented => panic!("Unimplemented opcode"),
        }
    }

    /// Reads and returns a single u8 value at the specified memory address.
    fn read_u8(&self, addr: Address) -> u8 {
        self.memory.fetch(addr)
    }

    /// Reads and returns a little endian u16 at the specified memory address.
    fn read_u16(&self, addr: u16) -> u16 {
        let low = self.read_u8(addr) as u16;
        let high = self.read_u8(addr + 1) as u16;
        high << 8 | low
    }

    /// Returns the address value of the program counter location.
    ///
    /// # Note
    ///
    /// Increments the program counter by 1 to represent the memory read.
    fn addr_imm(&mut self) -> Address {
        let addr = self.pc;
        self.pc += 1;
        addr
    }

    /// Returns the zero page address value at the program counter location.
    ///
    /// # Note
    ///
    /// Increments the program counter by 1 to represent the memory read.
    fn addr_zero_page(&mut self) -> Address {
        let addr = self.read_u8(self.pc) as Address;
        self.pc +=1;
        addr
    }

    /// Returns the zero page address value at the program counter location,
    /// with the current value of the `X` register added to it.
    ///
    /// # Note
    ///
    /// Increments the program counter by 1 to represent the memory read.
    fn addr_zero_page_x(&mut self) -> Address {
        let addr = self.read_u8(self.pc) as Address;
        self.pc +=1;
        addr + self.x as u16
    }

    /// Returns the address value pointed to by the address value at the program
    /// counter location.
    ///
    /// # Note
    ///
    /// Increments the program counter by 2 to represent the memory read.
    fn addr_abs(&mut self) -> Address {
        let addr = self.read_u16(self.pc);
        self.pc += 2;
        addr
    }

    /// Returns the address value pointed to by the value located at the program
    /// counter location, incremented by the value of register `X`.
    ///
    /// # Note
    ///
    /// Increments the program counter by 2 to represent the memory read.
    fn addr_abs_x(&mut self) -> Address {
        let base_addr = self.read_u16(self.pc);
        self.pc += 2;
        base_addr + self.x as u16
    }

    /// Returns the address value pointed to by the value located at the program
    /// counter location, incremented by the value of register `Y`.
    ///
    /// # Note
    ///
    /// Increments the program counter by 2 to represent the memory read.
    fn addr_abs_y(&mut self) -> Address {
        let base_addr = self.read_u16(self.pc);
        self.pc += 2;
        base_addr + self.y as u16
    }

    /// Adds the value of register `X` to the memory address located at the
    /// program counter location, then returns the memory address value pointed
    /// to by that value.
    ///
    /// # Note
    ///
    /// Increments the program counter by 1 to represent the memory read.
    fn addr_ind_x(&mut self) -> Address {
        let base_addr = self.read_u8(self.pc) as Address;
        self.pc += 1;
        self.read_u16(base_addr + self.x as u16)
    }

    /// Retrieves the memory address pointed to by the instruction operand, then
    /// adds the value of register `Y` to this address.
    ///
    /// # Note
    ///
    /// Increments the program counter by 1 to represent the memory read.
    fn addr_ind_y(&mut self) -> Address {
        let base_addr = self.read_u8(self.pc) as Address;
        self.pc += 1;
        self.read_u16(base_addr) + self.y as u16
    }

    fn lda(&mut self, addr: Address) {
        self.a = self.read_u8(addr)
    }

    fn _reset(&mut self) {
        // A, X, Y are not affected by reset.

        // Decrement S by 3, but do not write anything to the stack.
        self._sp -= 3;

        // Set the I (IRQ disable) flag to true).
        self._p |= 0x04;

        // Internal memory remains unchanged.
        // APU mode in $4017 remains unchanged.

        // Silence the APU.
        self.memory.store(0x4015, 0x00);
    }
}

#[cfg(test)]
mod tests {
    use memory::Memory;
    use opcode::Opcode::*;
    use super::CPU;

    #[test]
    fn test_read_u8() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x1000, 0xFF);

        assert_eq!(cpu.read_u8(0x1000), 0xFF);
    }

    #[test]
    fn test_read_u16() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x1000, 0xCD);
        cpu.memory.store(0x1001, 0xAB);

        assert_eq!(cpu.read_u16(0x1000), 0xABCD);
    }

    #[test]
    fn test_addr_imm() {
        let mut cpu = CPU::new();
        cpu.pc = 0x00FF;

        assert_eq!(cpu.addr_imm(), 0x00FF);
    }

    #[test]
    fn test_addr_zero_page() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, 0x10);

        assert_eq!(cpu.addr_zero_page(), 0x0010);
    }

    #[test]
    fn test_addr_zero_page_x() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, 0x10);
        cpu.x = 0x05;

        assert_eq!(cpu.addr_zero_page_x(), 0x0015);
    }

    #[test]
    fn test_addr_abs() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, 0x00);
        cpu.memory.store(0x0001, 0x02);

        assert_eq!(cpu.addr_abs(), 0x0200);
    }

    #[test]
    fn test_addr_abs_x() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, 0x00);
        cpu.memory.store(0x0001, 0x02);
        cpu.x = 0x05;

        assert_eq!(cpu.addr_abs_x(), 0x0205);
    }

    #[test]
    fn test_addr_abs_y() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, 0x00);
        cpu.memory.store(0x0001, 0x02);
        cpu.y = 0x05;

        assert_eq!(cpu.addr_abs_y(), 0x0205);
    }

    #[test]
    fn test_addr_ind_x() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, 0x04);
        cpu.memory.store(0x0034, 0xCD);
        cpu.memory.store(0x0035, 0xAB);
        cpu.x = 0x30;

        assert_eq!(cpu.addr_ind_x(), 0xABCD);
    }

    #[test]
    fn test_addr_ind_y() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, 0x0A);
        cpu.memory.store(0x000A, 0xEF);
        cpu.memory.store(0x000B, 0xCD);
        cpu.y = 0x01;

        assert_eq!(cpu.addr_ind_y(), 0xCDF0);
    }

    #[test]
    fn test_lda() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0200, 0xFF);

        assert_eq!(cpu.a, 0x00);
        cpu.lda(0x0200);
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_lda_immediate() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, LDA_IMM as u8);
        cpu.memory.store(0x0001, 0x17); // #$17

        cpu.step();
        assert_eq!(cpu.a, 0x17);
    }

    #[test]
    fn test_lda_zero_page() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, LDA_ZPAGE as u8);
        cpu.memory.store(0x0001, 0x02); // $02
        cpu.memory.store(0x0002, 0x03);

        cpu.step();
        assert_eq!(cpu.a, 0x03);
    }

    #[test]
    fn test_lda_zero_page_x() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, LDA_ZPAGEX as u8);
        cpu.memory.store(0x0001, 0x02); // $02
        cpu.memory.store(0x0005, 0xAB);
        cpu.x = 0x03;

        cpu.step();
        assert_eq!(cpu.a, 0xAB);
    }

    #[test]
    fn test_lda_absolute() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, LDA_ABS as u8);
        cpu.memory.store(0x0001, 0x14); // $0314
        cpu.memory.store(0x0002, 0x03);

        cpu.memory.store(0x0314, 0x31);

        cpu.step();
        assert_eq!(cpu.a, 0x31);
    }

    #[test]
    fn test_lda_absolute_x() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, LDA_ABSX as u8);
        cpu.memory.store(0x0001, 0x00); // $0200
        cpu.memory.store(0x0002, 0x02);

        cpu.memory.store(0x20A, 0xFF);
        cpu.x = 0x0A;

        cpu.step();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_lda_absolute_y() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, LDA_ABSY as u8);
        cpu.memory.store(0x0001, 0x00); // $0200
        cpu.memory.store(0x0002, 0x02);

        cpu.memory.store(0x020A, 0xFF);
        cpu.y = 0x0A;

        cpu.step();
        assert_eq!(cpu.a, 0xFF);
    }

    #[test]
    fn test_lda_ind_x() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, LDA_INDX as u8);
        cpu.memory.store(0x0001, 0x80); // $0080
        cpu.memory.store(0x008C, 0x3F);
        cpu.memory.store(0x008D, 0xC4);
        cpu.memory.store(0xC43F, 0x45);
        cpu.x = 0x0C;

        cpu.step();
        assert_eq!(cpu.a, 0x45);
    }

    #[test]
    fn test_lda_ind_y() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, LDA_INDY as u8);
        cpu.memory.store(0x0001, 0x14); // $0014
        cpu.memory.store(0x0014, 0x00);
        cpu.memory.store(0x0015, 0xD8);
        cpu.memory.store(0xD828, 0x0B);
        cpu.y = 0x28;

        cpu.step();
        assert_eq!(cpu.a, 0x0B);
    }
}
