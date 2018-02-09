use memory::{Address, Memory, NESMemory};
use opcode::Opcode;
use opcode::Opcode::*;

// Initialization values for the CPU registers.
const CPU_STATUS_REGISTER_INITIAL_VALUE: u8 = 0x34; // 0x00111000 (IRQ disabled)
const CPU_STACK_POINTER_INITIAL_VALUE: u8 = 0xFD;

// Indices of the flag bits in the CPU status register.
// TODO: perhaps replace this with the bitflags crate?
const FLAG_CARRY: u8 = 0;
const FLAG_ZERO: u8 = 1;
const _FLAG_IRQ_DISABLE: u8 = 2;
const _FLAG_DECIMAL_MODE: u8 = 3;
const _FLAG_BREAK: u8 = 5;
const FLAG_OVERFLOW: u8 = 6;
const FLAG_NEGATIVE: u8 = 7;

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
    p: u8,
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
            p: CPU_STATUS_REGISTER_INITIAL_VALUE,
            pc: 0,
            _sp: CPU_STACK_POINTER_INITIAL_VALUE,
            memory,
        }
    }

    /// Execute a single instruction cycle.
    fn step(&mut self) {
        use instruction::AddressingMode::*;

        // Read the next opcode to be executed.
        let opcode: Opcode = self.read_u8(self.pc).into();
        self.pc += 1;

        // Decode the opcode into an executable instruction.
        let instruction = opcode.decode();

        // If the instruction requires an operand, use the specified addressing
        // mode to determine its address.
        let operand_addr = Some(
            match *instruction.addressing_mode() {
                Immediate => self.addr_imm(),
                ZeroPage => self.addr_zero_page(),
                ZeroPageX => self.addr_zero_page_x(),
                Relative => self.relative(),
                Absolute => self.addr_abs(),
                AbsoluteX => self.addr_abs_x(),
                AbsoluteY => self.addr_abs_y(),
                IndirectX => self.addr_ind_x(),
                IndirectY => self.addr_ind_y(),
                Implicit |
                Indirect |
                Accumulator |
                _ZeroPageY => panic!("Unimplemented addressing mode"),
            }
        );

        match *instruction.opcode() {
            ADC_IMM |
            ADC_ZPAGE |
            ADC_ZPAGEX |
            ADC_ABS |
            ADC_ABSX |
            ADC_ABSY |
            ADC_INDX |
            ADC_INDY => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.adc(addr);
                return;
            },
            AND_IMM |
            AND_ZPAGE |
            AND_ZPAGEX |
            AND_ABS |
            AND_ABSX |
            AND_ABSY |
            AND_INDX |
            AND_INDY => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.and(addr);
                return;
            },
            ASL_ACC => {
                self.asl(None);
            },
            ASL_ZPAGE |
            ASL_ZPAGEX |
            ASL_ABS |
            ASL_ABSX => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.asl(Some(addr));
            },
            BCC => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.bcc(addr);
            },
            BCS => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.bcs(addr);
            },
            BEQ => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.beq(addr);
            },
            BIT_ZPAGE | BIT_ABS => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.bit(addr);
            },
            BMI => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.bmi(addr);
            },
            BNE => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.bne(addr);
            },
            BPL => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.bpl(addr);
            },
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
            ref opcode => panic!("Unimplemented instruction: {:?}", opcode),
        }
    }

    pub fn emulate(&mut self) {
        // TODO: reset here (e.g. a, x, y, to 0)?
        loop {
            self.step();
        }
    }

    /// Returns the value of the "carry" flag.
    fn carry(&self) -> bool {
        bit_get(self.p, FLAG_CARRY)
    }

    /// Sets the value of the "carry" flag.
    fn set_carry(&mut self, carry: bool) {
        self.p = bit_set(self.p, FLAG_CARRY, carry);
    }

    /// Returns the value of the "zero" flag.
    fn zero(&self) -> bool {
        bit_get(self.p, FLAG_ZERO)
    }

    /// Sets the value of the "zero" flag.
    fn set_zero(&mut self, zero: bool) {
        self.p = bit_set(self.p, FLAG_ZERO, zero);
    }

    /// Returns the value of the "overflow" flag.
    fn overflow(&self) -> bool {
        bit_get(self.p, FLAG_OVERFLOW)
    }

    /// Sets the value of the "overflow" flag.
    fn set_overflow(&mut self, overflow: bool) {
        self.p = bit_set(self.p, FLAG_OVERFLOW, overflow);
    }

    /// Sets the value of the "negative" flag.
    fn negative(&self) -> bool {
        bit_get(self.p, FLAG_NEGATIVE)
    }

    /// Sets the value of the "negative" flag.
    fn set_negative(&mut self, negative: bool) {
        self.p = bit_set(self.p, FLAG_NEGATIVE, negative);
    }

    fn _reset(&mut self) {
        // A, X, Y are not affected by reset.

        // Decrement S by 3, but do not write anything to the stack.
        self._sp -= 3;

        // Set the I (IRQ disable) flag to true).
        self.p |= 0x04;

        // Internal memory remains unchanged.
        // APU mode in $4017 remains unchanged.

        // Silence the APU.
        self.memory.store(0x4015, 0x00);
    }

    /// Adds the relative displacement to the program counter to branch to a new
    /// location.
    fn branch(&mut self, relative_addr: Address) {
        // Because branch instructions step the program counter by 2, we must
        // first decrement it back.
        // TODO: find a way to optimize this?
        self.pc -= 2;
        // Add the signed relative value to the program counter.
        self.pc += (relative_addr ^ 0x80) - 0x80;
    }

    // Memory read

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

    // Memory addressing

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
        self.pc += 1;
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
        self.pc += 1;
        addr + self.x as u16
    }

    /// Returns a memory address by taking the value at the program counter
    /// location and adding it to the current value of the program counter.
    fn relative(&mut self) -> Address {
        let addr = self.read_u8(self.pc) as Address;
        self.pc += 1;
        addr
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

    // Instructions

    /// Performs an add with carry.
    fn adc(&mut self, addr: Address) {
        let arg = self.read_u8(addr);
        let (sum, overflow1) = self.a.overflowing_add(arg);
        let (sum, overflow2) = sum.overflowing_add(self.carry() as u8);
        let carry = overflow1 || overflow2;

        // Carry flag gets set if overflow in bit 7.
        self.set_carry(carry);
        // Set if sign bit is incorrect.
        let overflow = !(self.a ^ arg) & (self.a ^ sum) & 0x80;
        self.set_overflow(overflow != 0);

        self.a = sum;

        // Set if A = 0
        let zero = self.a == 0;
        self.set_zero(zero);
    }

    /// Performs a logical AND.
    fn and(&mut self, addr: Address) {
        let arg = self.read_u8(addr);

        self.a = self.a & arg;

        // Set if A = 0
        let zero = self.a == 0;
        self.set_zero(zero);
        // Set if bit 7 set
        let negative = is_negative(self.a);
        self.set_negative(negative);
    }

    /// Shifts the contents of the accumulator or the specified memory address
    /// one bit left.
    fn asl(&mut self, addr: Option<Address>) {
        let value = match addr {
            Some(addr) => self.read_u8(addr),
            None => self.a,
        };

        let carry = is_negative(value);

        let res = value << 1;

        // Bit 7 is placed in the carry flag.
        self.set_carry(carry);
        // Set if A = 0
        let zero = self.a == 0;
        self.set_zero(zero);
        // Set if bit 7 of the result is set.
        self.set_negative(bit_get(res, 7));

        match addr {
            Some(addr) => { self.memory.store(addr, res); },
            None => self.a = res,
        };
    }

    /// Adds the relative value to the program counter to branch to a new
    /// location if the carry flag is clear.
    fn bcc(&mut self, addr: Address) {
        if !self.carry() {
            self.branch(addr);
        }
    }

    /// Adds the relative value to the program counter to branch to a new
    /// location if the carry flag is set.
    fn bcs(&mut self, addr: Address) {
        if self.carry() {
            self.branch(addr);
        }
    }

    /// Adds the relative value to the program counter to branch to a new
    /// location if the zero flag is set.
    fn beq(&mut self, addr: Address) {
        if self.zero() {
            self.branch(addr);
        }
    }

    /// Tests if one or more bits are set in a target memory location.
    fn bit(&mut self, addr: Address) {
        let value = self.read_u8(addr);

        // AND the value of the mask pattern in A with the value in memory to
        // set or clear the zero flag.
        let zero = (self.a & value) == 0;
        self.set_zero(zero);

        // Bit 6 of the value is copied into the V flag.
        self.set_overflow(bit_get(value, 7));
        // Bit 7 of the value is copied into the N flag.
        self.set_negative(bit_get(value, 6));
    }

    /// Adds the relative displacement to the program counter to branch, if
    /// the negative flag is set.
    fn bmi(&mut self, addr: Address) {
        if self.negative() {
            self.branch(addr);
        }
    }

    /// Adds the relative value to the program counter to branch to a new
    /// location if the zero flag is not set.
    fn bne(&mut self, addr: Address) {
        if !self.zero() {
            self.branch(addr);
        }
    }

    /// Adds the relative value to the program counter to branch to a new
    /// location if the negative flag is clear.
    fn bpl(&mut self, addr: Address) {
        if !self.negative() {
            self.branch(addr);
        }
    }

    /// Loads a byte of memory into the accumulator.
    fn lda(&mut self, addr: Address) {
        let value = self.read_u8(addr);
        self.a = value;
        let zero = self.a == 0;
        self.set_zero(zero);
        // Negative gets set if bit 7 of A is set.
        let negative = is_negative(self.a);
        self.set_negative(negative);
    }
}

/// Sets the bit at position `n` to the specified value.
fn bit_set(word: u8, n: u8, value: bool) -> u8 {
    (word & (!(1 << n))) | ((value as u8) << n)
}

/// Gets the value of the bit at position `n`.
fn bit_get(word: u8, n: u8) -> bool {
    word & (1 << n) != 0
}

/// Returns true if the provided value is negative (i.e., if bit 7 is set).
fn is_negative(value: u8) -> bool {
    bit_get(value, 7)
}

#[cfg(test)]
mod tests {
    use memory::Memory;
    use opcode::Opcode::*;
    use super::{bit_set, bit_get, CPU};

    #[test]
    fn test_status_register() {
        let mut cpu = CPU::new();

        cpu.set_carry(false);
        assert!(!cpu.carry());
        cpu.set_carry(true);
        assert!(cpu.carry());

        cpu.set_zero(false);
        assert!(!cpu.zero());
        cpu.set_zero(true);
        assert!(cpu.zero());

        cpu.set_overflow(false);
        assert!(!cpu.overflow());
        cpu.set_overflow(true);
        assert!(cpu.overflow());

        cpu.set_negative(false);
        assert!(!cpu.negative());
        cpu.set_negative(true);
        assert!(cpu.negative());
    }

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
    fn test_adc() {
        let mut cpu = CPU::new();

        // 1 + 1 = 2, returns C = 0, V = 0
        cpu.set_zero(false);
        cpu.set_carry(false);
        cpu.set_overflow(false);
        cpu.memory.store(0x0000, 0x01);
        cpu.a = 0x01;
        cpu.adc(0x0000);
        assert_eq!(cpu.a, 0x02);
        assert!(!cpu.zero());
        assert!(!cpu.carry());
        assert!(!cpu.overflow());

        // 1 + -1 = 0, returns C = 1, V = 0
        cpu.set_zero(false);
        cpu.set_carry(false);
        cpu.set_overflow(false);
        cpu.memory.store(0x0000, 0xFF);
        cpu.a = 0x01;
        cpu.adc(0x0000);
        assert_eq!(cpu.a, 0x00);
        assert!(cpu.zero());
        assert!(cpu.carry());
        assert!(!cpu.overflow());

        // 127 + 1 = 128, returns C = 0, V = 1
        cpu.set_zero(false);
        cpu.set_carry(false);
        cpu.set_overflow(false);
        cpu.memory.store(0x0000, 0x01);
        cpu.a = 0x7F;
        cpu.adc(0x0000);
        assert_eq!(cpu.a, 0x80);
        assert!(!cpu.zero());
        assert!(!cpu.carry());
        assert!(cpu.overflow());

        // -128 + -1 = -129, returns C = 1, V = 1
        cpu.set_zero(false);
        cpu.set_carry(false);
        cpu.set_overflow(false);
        cpu.memory.store(0x0000, 0xFF);
        cpu.a = 0x80;
        cpu.adc(0x0000);
        assert_eq!(cpu.a, 0x7F);
        assert!(!cpu.zero());
        assert!(cpu.carry());
        assert!(cpu.overflow());
    }

    #[test]
    fn test_and() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, 0xA5);

        cpu.a = 0xFF;
        cpu.and(0x0000);
        assert_eq!(cpu.a, 0xA5);
        assert!(!cpu.zero());
        assert!(cpu.negative());

        cpu.a = 0x05;
        cpu.and(0x0000);
        assert_eq!(cpu.a, 0x05);
        assert!(!cpu.zero());
        assert!(!cpu.negative());

        cpu.a = 0x00;
        cpu.and(0x0000);
        assert_eq!(cpu.a, 0x00);
        assert!(cpu.zero());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_asl() {
        let mut cpu = CPU::new();

        cpu.a = 0xFF;
        cpu.asl(None);
        assert_eq!(cpu.a, 0xFE);
        assert!(cpu.carry());
        assert!(!cpu.zero());
        assert!(cpu.negative());

        cpu.memory.store(0x0000, 0x0E);
        cpu.asl(Some(0x0000));
        assert_eq!(cpu.memory.fetch(0x0000), 0x1C);
        assert!(!cpu.carry());
        assert!(!cpu.zero());
        assert!(!cpu.negative());

        cpu.memory.store(0x0000, 0x80);
        cpu.asl(Some(0x0000));
        assert_eq!(cpu.memory.fetch(0x0000), 0x00);
        assert!(cpu.carry());
        assert!(!cpu.zero());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_bcc() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, BCC as u8);
        cpu.memory.store(0x0001, 0x04);

        cpu.set_carry(false);
        cpu.step();
        assert_eq!(cpu.pc, 4);

        cpu.pc = 0;
        cpu.set_carry(true);
        cpu.step();
        assert_eq!(cpu.pc, 2);
    }

    #[test]
    fn test_bcs() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, BCS as u8);
        cpu.memory.store(0x0001, 0x04);

        cpu.set_carry(true);
        cpu.step();
        assert_eq!(cpu.pc, 4);

        cpu.pc = 0;
        cpu.set_carry(false);
        cpu.step();
        assert_eq!(cpu.pc, 2);
    }

    #[test]
    fn test_beq() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, BEQ as u8);
        cpu.memory.store(0x0001, 0x04);

        cpu.set_zero(true);
        cpu.step();
        assert_eq!(cpu.pc, 4);

        cpu.pc = 0;
        cpu.set_zero(false);
        cpu.step();
        assert_eq!(cpu.pc, 2);
    }

    #[test]
    fn test_bit() {
        let mut cpu = CPU::new();
        cpu.a = 0xEA;

        cpu.memory.store(0x0000, 0xEA);
        cpu.bit(0x0000);
        assert!(!cpu.zero());
        assert!(cpu.overflow());
        assert!(cpu.negative());

        cpu.memory.store(0x0000, 0x28);
        cpu.bit(0x0000);
        assert!(!cpu.zero());
        assert!(!cpu.overflow());
        assert!(!cpu.negative());

        cpu.memory.store(0x0000, 0x00);
        cpu.bit(0x0000);
        assert!(cpu.zero());
        assert!(!cpu.overflow());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_bmi() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, BMI as u8);
        cpu.memory.store(0x0001, 0x04);

        cpu.set_negative(true);
        cpu.step();
        assert_eq!(cpu.pc, 4);

        cpu.pc = 0;
        cpu.set_negative(false);
        cpu.step();
        assert_eq!(cpu.pc, 2);
    }

    #[test]
    fn test_bne() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, BNE as u8);
        cpu.memory.store(0x0001, 0x04);

        cpu.set_zero(false);
        cpu.step();
        assert_eq!(cpu.pc, 4);

        cpu.pc = 0;
        cpu.set_zero(true);
        cpu.step();
        assert_eq!(cpu.pc, 2);
    }

    #[test]
    fn test_bpl() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, BPL as u8);
        cpu.memory.store(0x0001, 0x04);

        cpu.set_negative(false);
        cpu.step();
        assert_eq!(cpu.pc, 4);

        cpu.pc = 0;
        cpu.set_negative(true);
        cpu.step();
        assert_eq!(cpu.pc, 2);
    }

    #[test]
    fn test_lda() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0200, 0xFF);

        assert_eq!(cpu.a, 0x00);
        cpu.lda(0x0200);
        assert_eq!(cpu.a, 0xFF);
        assert!(!cpu.zero());

        // Test that the zero flag gets set correctly.
        cpu.memory.store(0x0000, 0x00);
        cpu.memory.store(0x0001, 0x01);
        cpu.lda(0x0000);
        assert!(cpu.zero());
        cpu.lda(0x0001);
        assert!(!cpu.zero());

        // Test that the negative flag gets set correctly.
        cpu.memory.store(0x0000, 0x00);
        cpu.memory.store(0x0001, 0x80);
        cpu.lda(0x0000);
        assert!(!cpu.negative());
        cpu.lda(0x0001);
        assert!(cpu.negative());
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

    #[test]
    fn test_bit_set() {
        let mut value = 0;
        value = bit_set(value, 0, true);
        assert_eq!(value, 0b00000001);
        value = bit_set(value, 0, true);
        assert_eq!(value, 0b00000001);
        value = bit_set(value, 7, true);
        assert_eq!(value, 0b10000001);
        value = bit_set(value, 7, false);
        assert_eq!(value, 0b00000001);
    }

    #[test]
    fn test_bit_get() {
        assert_eq!(bit_get(0b10000000, 7), true);
        assert_eq!(bit_get(0b10000000, 6), false);
    }
}
