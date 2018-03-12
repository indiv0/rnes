use memory::{Address, Memory, NESMemory};
use opcode::Opcode;
use opcode::Opcode::*;
use std::cmp::Ordering::{Equal, Greater, Less};

// Initialization values for the CPU registers.
const CPU_STATUS_REGISTER_INITIAL_VALUE: u8 = 0x34; // 0x00111000 (IRQ disabled)
const CPU_STACK_POINTER_INITIAL_VALUE: u8 = 0xFD;

// Indices of the flag bits in the CPU status register.
// TODO: perhaps replace this with the bitflags crate?
const FLAG_CARRY: u8 = 0;
const FLAG_ZERO: u8 = 1;
const FLAG_IRQ_DISABLE: u8 = 2;
const FLAG_DECIMAL_MODE: u8 = 3;
const FLAG_BREAK: u8 = 5;
const FLAG_OVERFLOW: u8 = 6;
const FLAG_NEGATIVE: u8 = 7;

// IRQ/BRK vector memory address.
const IRQ_VECTOR_ADDR: Address = 0xFFFE;

/// An implementation of the NES CPU.
///
/// # Architecture
///
/// The NES CPU is an 8-bit CPU with a small number of internal registers, 64 KB
/// of memory, and a 16-bit address bus. The processor is little endian and
/// expects addresses to be stored in memory least significant byte first.
#[derive(Clone)]
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
    sp: u8,

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
            sp: CPU_STACK_POINTER_INITIAL_VALUE,
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
        let operand_addr = match *instruction.addressing_mode() {
            Immediate => Some(self.addr_imm()),
            ZeroPage => Some(self.addr_zero_page()),
            ZeroPageX => Some(self.addr_zero_page_x()),
            Relative => Some(self.relative()),
            Absolute => Some(self.addr_abs()),
            AbsoluteX => Some(self.addr_abs_x()),
            AbsoluteY => Some(self.addr_abs_y()),
            IndirectX => Some(self.addr_ind_x()),
            IndirectY => Some(self.addr_ind_y()),
            Implicit => None,
            Indirect |
            Accumulator |
            ZeroPageY => panic!("Unimplemented addressing mode"),
        };

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
            BRK => self.brk(),
            BVC => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.bvc(addr);
            },
            BVS => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.bvs(addr);
            },
            CLC => self.clc(),
            CLD => self.cld(),
            CLI => self.cli(),
            CLV => self.clv(),
            CMP_IMM |
            CMP_ZPAGE |
            CMP_ZPAGEX |
            CMP_ABS |
            CMP_ABSX |
            CMP_ABSY |
            CMP_INDX |
            CMP_INDY => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.cmp(addr);
            },
            CPX_IMM |
            CPX_ZPAGE |
            CPX_ABS => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.cpx(addr);
            }
            CPY_IMM |
            CPY_ZPAGE |
            CPY_ABS => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.cpy(addr);
            }
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
            },
            DEC_ZPAGE |
            DEC_ZPAGEX |
            DEC_ABS |
            DEC_ABSX => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.dec(addr);
            },
            DEX => self.dex(),
            DEY => self.dey(),
            EOR_IMM |
            EOR_ZPAGE |
            EOR_ZPAGEX |
            EOR_ABS |
            EOR_ABSX |
            EOR_ABSY |
            EOR_INDX |
            EOR_INDY => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.eor(addr);
            },
            INC_ZPAGE |
            INC_ZPAGEX |
            INC_ABS |
            INC_ABSX => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.inc(addr);
            },
            INX => self.inx(),
            INY => self.iny(),
            JMP_ABS |
            JMP_IND => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.jmp(addr);
            },
            JSR => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.jsr(addr);
            },
            LDX_IMM |
            LDX_ZPAGE |
            LDX_ZPAGEY |
            LDX_ABS |
            LDX_ABSY => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.ldx(addr);
            },
            LDY_IMM |
            LDY_ZPAGE |
            LDY_ZPAGEX |
            LDY_ABS |
            LDY_ABSX => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.ldy(addr);
            },
            LSR_ACC => self.lsr_acc(),
            LSR_ZPAGE |
            LSR_ZPAGEX |
            LSR_ABS |
            LSR_ABSX => {
                let addr = operand_addr
                    .expect("Operand address was unexpectedly missing");
                self.lsr_mem(addr);
            },
            NOP => self.nop(),
            ref opcode @ ORA_IMM |
            ref opcode @ ORA_ZPAGE |
            ref opcode @ ORA_ZPAGEX |
            ref opcode @ ORA_ABS |
            ref opcode @ ORA_ABSX |
            ref opcode @ ORA_ABSY |
            ref opcode @ ORA_INDX |
            ref opcode @ ORA_INDY |
            ref opcode @ PHA |
            ref opcode @ PHP |
            ref opcode @ PLA |
            ref opcode @ PLP |
            ref opcode @ ROL_ACC |
            ref opcode @ ROL_ZPAGE |
            ref opcode @ ROL_ZPAGEX |
            ref opcode @ ROL_ABS |
            ref opcode @ ROL_ABSX |
            ref opcode @ ROR_ACC |
            ref opcode @ ROR_ZPAGE |
            ref opcode @ ROR_ZPAGEX |
            ref opcode @ ROR_ABS |
            ref opcode @ ROR_ABSX |
            ref opcode @ RTI |
            ref opcode @ RTS |
            ref opcode @ SBC_IMM |
            ref opcode @ SBC_ZPAGE |
            ref opcode @ SBC_ZPAGEX |
            ref opcode @ SBC_ABS |
            ref opcode @ SBC_ABSX |
            ref opcode @ SBC_ABSY |
            ref opcode @ SBC_INDX |
            ref opcode @ SBC_INDY |
            ref opcode @ SEC |
            ref opcode @ SED |
            ref opcode @ SEI |
            ref opcode @ STA_ZPAGE |
            ref opcode @ STA_ZPAGEX |
            ref opcode @ STA_ABS |
            ref opcode @ STA_ABSX |
            ref opcode @ STA_ABSY |
            ref opcode @ STA_INDX |
            ref opcode @ STA_INDY |
            ref opcode @ STX_ZPAGE |
            ref opcode @ STX_ZPAGEY |
            ref opcode @ STX_ABS |
            ref opcode @ STY_ZPAGE |
            ref opcode @ STY_ZPAGEX |
            ref opcode @ STY_ABS |
            ref opcode @ TAX |
            ref opcode @ TAY |
            ref opcode @ TSX |
            ref opcode @ TXA |
            ref opcode @ TXS |
            ref opcode @ TYA => panic!("Unimplemented opcode: {:?}", opcode),
        }
    }

    pub fn emulate(&mut self) {
        // TODO: reset here (e.g. a, x, y, to 0)?
        loop {
            self.step();
        }
    }

    fn _reset(&mut self) {
        // A, X, Y are not affected by reset.

        // Decrement S by 3, but do not write anything to the stack.
        self.sp.wrapping_sub(3);

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

    /// Compares the specified value to another value in memory, and sets the zaro and carry flags
    /// as appropriate.
    fn compare(&mut self, value: u8, other_addr: Address) {
        // Retrieve the value to be compared.
        let other = self.read_u8(other_addr);

        match value.cmp(&other) {
            Less => {
                self.set_carry(false);
                self.set_zero(false);
                self.set_negative(true);
            },
            Equal => {
                self.set_carry(true);
                self.set_zero(true);
                self.set_negative(false);
            },
            Greater => {
                self.set_carry(true);
                self.set_zero(false);
                self.set_negative(false);
            }
        }
    }

    /// Shifts the bits of the specified value to the right, returning the
    /// result and setting the carry, zero, and negative status flags as
    /// necessary.
    fn lsr(&mut self, value: u8) -> u8 {
        self.set_carry(bit_get(value, 0));
        let res = value >> 1;
        self.set_zero(res == 0);
        self.set_negative(false);
        res
    }

    // Processor status

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

    /// Returns the value of the "IRQ disable" flag.
    fn irq_disable(&self) -> bool {
        bit_get(self.p, FLAG_IRQ_DISABLE)
    }

    /// Sets the value of the "IRQ disable" flag.
    fn set_irq_disable(&mut self, irq_disable: bool) {
        self.p = bit_set(self.p, FLAG_IRQ_DISABLE, irq_disable);
    }

    /// Returns the value of the "decimal mode" flag.
    fn decimal_mode(&self) -> bool {
        bit_get(self.p, FLAG_DECIMAL_MODE)
    }

    /// Sets the value of the "decimal mode" flag.
    fn set_decimal_mode(&mut self, decimal_mode: bool) {
        self.p = bit_set(self.p, FLAG_DECIMAL_MODE, decimal_mode);
    }

    /// Returns the value of the "break" flag.
    fn break_flag(&self) -> bool {
        bit_get(self.p, FLAG_BREAK)
    }

    /// Sets the value of the "break" flag.
    fn set_break(&mut self, brk: bool) {
        self.p = bit_set(self.p, FLAG_BREAK, brk);
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

    // Stack operations and variables

    /// Returns the value of the stack pointer as an absolute address value.
    fn sp(&self) -> u16 {
        // Compute the address of the stack pointer;
        // the top 8 bits are hard-coded to be equal to 0b0000_0001.
        0x0100 | u16::from(self.sp)
    }

    /// Pushes a value to the stack.
    ///
    /// The stack is implemented as a descending stack, so the stack pointer
    /// is decremented after this operation.
    fn push(&mut self, value: u8) {
        // Push the value onto the stack and decrement the stack pointer.
        let addr = self.sp();
        self.write_u8(addr, value);
        self.sp = self.sp.wrapping_sub(1);
    }

    /// Pops a value from the stack.
    ///
    /// The stack is implemented as a descending stack, so the stack pointer
    /// is incremented after this operation.
    fn pop(&mut self) -> u8 {
        // Increment the stack pointer and pop the value from the stack.
        self.sp = self.sp.wrapping_add(1);
        let addr = self.sp();
        self.read_u8(addr)
    }

    /// Retrieves a value "index" positions from the top without removing it.
    fn peek(&self, index: u8) -> u8 {
        // Calculate the address we wish to peek at.
        let addr = 0x0100 | u16::from(self.sp
            .wrapping_add(1)
            .wrapping_add(index));
        self.read_u8(addr)
    }

    // Memory read

    /// Reads and returns a single u8 value at the specified memory address.
    fn read_u8(&self, addr: Address) -> u8 {
        self.memory.fetch(addr)
    }

    /// Reads and returns a little endian u16 at the specified memory address.
    fn read_u16(&self, addr: Address) -> u16 {
        let low = u16::from(self.read_u8(addr));
        let high = u16::from(self.read_u8(addr + 1));
        high << 8 | low
    }

    // Memory write

    /// Writes a single `u8` value to the specified memory address.
    fn write_u8(&mut self, addr: Address, value: u8) {
        self.memory.store(addr, value);
    }

    /// Writes a little endian `u16` value to the specified memory address.
    fn write_u16(&mut self, addr: Address, value: u16) {
        self.write_u8(addr, value as u8);
        self.write_u8(addr + 1, (value >> 8) as u8);
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
        let addr = Address::from(self.read_u8(self.pc));
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
        let addr = Address::from(self.read_u8(self.pc));
        self.pc += 1;
        addr + u16::from(self.x)
    }

    /// Returns a memory address by taking the value at the program counter
    /// location and adding it to the current value of the program counter.
    fn relative(&mut self) -> Address {
        let addr = Address::from(self.read_u8(self.pc));
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
        base_addr + u16::from(self.x)
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
        base_addr + u16::from(self.y)
    }

    /// Adds the value of register `X` to the memory address located at the
    /// program counter location, then returns the memory address value pointed
    /// to by that value.
    ///
    /// # Note
    ///
    /// Increments the program counter by 1 to represent the memory read.
    fn addr_ind_x(&mut self) -> Address {
        let base_addr = Address::from(self.read_u8(self.pc));
        self.pc += 1;
        self.read_u16(base_addr + u16::from(self.x))
    }

    /// Retrieves the memory address pointed to by the instruction operand, then
    /// adds the value of register `Y` to this address.
    ///
    /// # Note
    ///
    /// Increments the program counter by 1 to represent the memory read.
    fn addr_ind_y(&mut self) -> Address {
        let base_addr = Address::from(self.read_u8(self.pc));
        self.pc += 1;
        self.read_u16(base_addr) + u16::from(self.y)
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

        self.a &= arg;

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

    /// Generates an interrupt request.
    ///
    /// The program counter and processor status are pushed onto the stack, the
    /// IRQ interrupt vector is read into the program counter, and the break
    /// flag is set to `true`.
    fn brk(&mut self) {
        // Push the program counter onto the stack.
        let pc = self.pc;
        self.push((pc >> 8) as u8);
        self.push(pc as u8);

        // Push the processor status onto the stack.
        let p = self.p;
        self.push(p);

        // Load the IRQ interrupt vector into the PC.
        self.pc = self.read_u16(IRQ_VECTOR_ADDR);

        // Set the break flag in the status to 1.
        self.set_break(true);
    }

    /// Adds the relative value to the program counter to branch to a new
    /// location if the overflow flag is clear.
    fn bvc(&mut self, addr: Address) {
        if !self.overflow() {
            self.branch(addr);
        }
    }

    /// Adds the relative displacement to the program counter to branch, if
    /// the overflow flag is set.
    fn bvs(&mut self, addr: Address) {
        if self.overflow() {
            self.branch(addr);
        }
    }

    /// Sets the carry flag to zero.
    fn clc(&mut self) {
        self.set_carry(false);
    }

    /// Sets the decimal mode flag to zero.
    ///
    /// # Note
    ///
    /// The state of the decimal flag is undefined when the CPU is powered up
    /// and it is not reset when an interrupt is generated.
    /// In both cases you should include an explicit CLD to ensure that the flag is cleared before
    /// performing addition or subtraction.
    fn cld(&mut self) {
        self.set_decimal_mode(false);
    }

    /// Clears the interrupt disable flag.
    fn cli(&mut self) {
        self.set_irq_disable(false);
    }

    /// Clears the overflow flag.
    fn clv(&mut self) {
        self.set_overflow(false);
    }

    /// Compares the contents of the accumulator with another value and sets the
    /// zero and carry flags as appropriate.
    fn cmp(&mut self, addr: Address) {
        let a = self.a;
        self.compare(a, addr);
    }

    /// Compares the contents of the X register with another value and sets the
    /// zero and carry flags as appropriate.
    fn cpx(&mut self, addr: Address) {
        let x = self.x;
        self.compare(x, addr);
    }

    /// Compares the contents of the Y register with another value and sets the
    /// zero and carry flags as appropriate.
    fn cpy(&mut self, addr: Address) {
        let y = self.y;
        self.compare(y, addr);
    }

    /// Subtracts one from the specified value in memory, setting the zero and
    /// negative flags as appropriate.
    fn dec(&mut self, addr: Address) {
        let mut value = self.read_u8(addr);
        value = value.wrapping_sub(1);

        self.set_zero(value == 0);
        self.set_negative(is_negative(value));

        self.write_u8(addr, value);
    }

    /// Subtracts one from the X register, setting the zero and negative flags
    /// appropriate.
    fn dex(&mut self) {
        let mut value = self.x;
        value = value.wrapping_sub(1);

        self.set_zero(value == 0);
        self.set_negative(is_negative(value));

        self.x = value;
    }

    /// Subtracts one from the Y register, setting the zero and negative flags
    /// appropriate.
    fn dey(&mut self) {
        let mut value = self.y;
        value = value.wrapping_sub(1);

        self.set_zero(value == 0);
        self.set_negative(is_negative(value));

        self.y = value;
    }

    /// Performs an exclusive OR on the contents of the accumulator and the byte
    /// value at the specified memory address.
    fn eor(&mut self, addr: Address) {
        let value = self.read_u8(addr);

        self.a ^= value;

        let a = self.a;
        self.set_zero(a == 0);
        self.set_negative(is_negative(a));
    }

    /// Adds one to the value at the specified memory location, setting the zero
    /// and negative flags as appropriate.
    fn inc(&mut self, addr: Address) {
        let mut value = self.read_u8(addr);

        value = value.wrapping_add(1);

        self.set_zero(value == 0);
        self.set_negative(is_negative(value));

        self.write_u8(addr, value);
    }

    /// Adds one to the X register, setting the zero and negative flags as
    /// appropriate.
    fn inx(&mut self) {
        self.x = self.x.wrapping_add(1);

        let x = self.x;
        self.set_zero(x == 0);
        self.set_negative(is_negative(x));
    }

    /// Adds one to the Y register, setting the zero and negative flags as
    /// appropriate.
    fn iny(&mut self) {
        self.y = self.y.wrapping_add(1);

        let y = self.y;
        self.set_zero(y == 0);
        self.set_negative(is_negative(y));
    }

    /// Sets the program to the address specified.
    ///
    /// # Note
    ///
    // From: http://obelisk.me.uk/6502/reference.html#JMP
    /// An original 6502 has does not correctly fetch the target address if the
    /// indirect vector falls on a page boundary (e.g. $xxFF where xx is any
    /// value from $00 to $FF).
    /// In this case fetches the LSB from $xxFF as expected but takes the MSB
    /// from $xx00.
    /// This is fixed in some later chips like the 65SC02 so for compatibility
    /// always ensure the indirect vector is not at the end of the page.
    fn jmp(&mut self, addr: Address) {
        let target_addr = self.read_u16(addr);
        self.pc = target_addr;
    }

    /// Pushes the address (minus one) of the return location to the stack and
    /// then sets the program counter to the target memory address.
    fn jsr(&mut self, addr: Address) {
        let return_addr = self.pc.wrapping_sub(1);
        self.push((return_addr >> 8) as u8);
        self.push(return_addr as u8);

        self.pc = self.read_u16(addr);
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

    /// Loads a byte of memory into the X register.
    fn ldx(&mut self, addr: Address) {
        let value = self.read_u8(addr);
        self.x = value;

        self.set_zero(value == 0);
        self.set_negative(is_negative(value));
    }

    /// Loads a byte of memory into the Y register.
    fn ldy(&mut self, addr: Address) {
        let value = self.read_u8(addr);
        self.y = value;

        self.set_zero(value == 0);
        self.set_negative(is_negative(value));
    }

    /// Shift each of the bits in the accumulator one place to the right.
    /// Sets the carry, zero, and negative flags as necessary.
    fn lsr_acc(&mut self) {
        let a = self.a;
        self.a = self.lsr(a);
    }

    /// Shift each of the bits of the value at the specified address one place
    /// to the right.
    /// Sets the carry, zero, and negative flags as necessary.
    fn lsr_mem(&mut self, addr: Address) {
        let value = self.read_u8(addr);
        let res = self.lsr(value);
        self.write_u8(addr, res);
    }

    /// Causes no changes to the processor (except the normal incrementing of the program counter).
    fn nop(&self) {}
}

impl Default for CPU {
    fn default() -> Self {
        Self::new()
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
    use super::{
        bit_set, bit_get, CPU, CPU_STACK_POINTER_INITIAL_VALUE, IRQ_VECTOR_ADDR
    };

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

        cpu.set_break(false);
        assert!(!cpu.break_flag());
        cpu.set_break(true);
        assert!(cpu.break_flag());

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
    fn test_stack_push() {
        let mut cpu = CPU::new();

        cpu.push(0xAA);
        cpu.push(0xBB);
        assert_eq!(cpu.read_u8(0x01FD), 0xAA);
        assert_eq!(cpu.read_u8(0x01FC), 0xBB);
        assert_eq!(cpu.sp, CPU_STACK_POINTER_INITIAL_VALUE.wrapping_sub(2));
    }

    #[test]
    fn test_stack_pop() {
        let mut cpu = CPU::new();
        cpu.push(0xAA);

        assert_eq!(cpu.pop(), 0xAA);
        assert_eq!(cpu.sp, CPU_STACK_POINTER_INITIAL_VALUE);
    }

    #[test]
    fn test_stack_peek() {
        let mut cpu = CPU::new();
        cpu.push(0xAA);
        cpu.push(0xBB);

        assert_eq!(cpu.peek(0), 0xBB);
        assert_eq!(cpu.peek(1), 0xAA);
    }

    #[test]
    fn test_stack_wrapping_behaviour() {
        let mut cpu = CPU::new();

        // Pop enough times to reach stack address 0x100.
        cpu.pop();
        cpu.pop();
        cpu.pop();
        assert_eq!(cpu.sp, 0x00);
        cpu.push(0xAA);
        assert_eq!(cpu.sp, 0xFF);
        assert_eq!(cpu.read_u8(0x0100), 0xAA);
        cpu.push(0xBB);
        assert_eq!(cpu.peek(0), 0xBB);
        assert_eq!(cpu.peek(1), 0xAA);
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
    fn test_write_u8() {
        let mut cpu = CPU::new();

        cpu.write_u8(0x0010, 0xAA);
        assert_eq!(cpu.memory.fetch(0x0010), 0xAA);
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
    fn test_brk() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, BRK as u8);
        cpu.write_u16(IRQ_VECTOR_ADDR, 0x0400);
        cpu.set_break(false);

        let pc = cpu.pc;
        let status = cpu.p;

        assert_eq!(cpu.break_flag(), false);
        cpu.step();
        assert_eq!(cpu.peek(0), status);
        assert_eq!(cpu.peek(1), pc as u8 + 1); // PC has since been incremented
        assert_eq!(cpu.peek(2), (pc >> 8) as u8);
        assert_eq!(cpu.pc, 0x0400);
        assert_eq!(cpu.break_flag(), true);
    }

    #[test]
    fn test_bvc() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, BVC as u8);
        cpu.memory.store(0x0001, 0x04);

        cpu.set_overflow(false);
        cpu.step();
        assert_eq!(cpu.pc, 4);

        cpu.pc = 0;
        cpu.set_overflow(true);
        cpu.step();
        assert_eq!(cpu.pc, 2);
    }

    #[test]
    fn test_bvs() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, BVS as u8);
        cpu.memory.store(0x0001, 0x04);

        cpu.set_overflow(true);
        cpu.step();
        assert_eq!(cpu.pc, 4);

        cpu.pc = 0;
        cpu.set_overflow(false);
        cpu.step();
        assert_eq!(cpu.pc, 2);
    }

    #[test]
    fn test_clc() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, CLC as u8);
        cpu.set_carry(true);

        assert!(cpu.carry());
        cpu.step();
        assert!(!cpu.carry());
    }

    #[test]
    fn test_cld() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, CLD as u8);
        cpu.set_decimal_mode(true);

        assert!(cpu.decimal_mode());
        cpu.step();
        assert!(!cpu.decimal_mode());
    }

    #[test]
    fn test_cli() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, CLI as u8);
        cpu.set_irq_disable(true);

        assert!(cpu.irq_disable());
        cpu.step();
        assert!(!cpu.irq_disable());
    }

    #[test]
    fn test_clv() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, CLV as u8);
        cpu.set_overflow(true);

        assert!(cpu.overflow());
        cpu.step();
        assert!(!cpu.overflow());
    }

    #[test]
    fn test_cmp() {
        let mut cpu = CPU::new();
        cpu.a = 0x05;

        // Test that the carry, zero, and negative flags get set correctly when
        // A < M.
        cpu.memory.store(0x0000, 0x06);
        cpu.set_carry(true);
        cpu.set_zero(true);
        cpu.set_negative(false);
        cpu.cmp(0x0000);
        assert!(!cpu.carry());
        assert!(!cpu.zero());
        assert!(cpu.negative());

        // Test that the carry, zero, and negative flags get set correctly when
        // A = M.
        cpu.memory.store(0x0000, 0x05);
        cpu.pc = 0x0000;
        cpu.set_carry(false);
        cpu.set_zero(false);
        cpu.set_negative(true);
        cpu.cmp(0x0000);
        assert!(cpu.carry());
        assert!(cpu.zero());
        assert!(!cpu.negative());

        // Test that the carry, zero, and negative flags get set correctly when
        // A > M.
        cpu.memory.store(0x0000, 0x04);
        cpu.pc = 0x0000;
        cpu.set_carry(false);
        cpu.set_zero(true);
        cpu.set_negative(true);
        cpu.cmp(0x0000);
        assert!(cpu.carry());
        assert!(!cpu.zero());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_cpx() {
        let mut cpu = CPU::new();
        cpu.x = 0x05;

        // Test that the carry, zero, and negative flags get set correctly when
        // A < M.
        cpu.memory.store(0x0000, 0x06);
        cpu.set_carry(true);
        cpu.set_zero(true);
        cpu.set_negative(false);
        cpu.cpx(0x0000);
        assert!(!cpu.carry());
        assert!(!cpu.zero());
        assert!(cpu.negative());

        // Test that the carry, zero, and negative flags get set correctly when
        // A = M.
        cpu.memory.store(0x0000, 0x05);
        cpu.pc = 0x0000;
        cpu.set_carry(false);
        cpu.set_zero(false);
        cpu.set_negative(true);
        cpu.cpx(0x0000);
        assert!(cpu.carry());
        assert!(cpu.zero());
        assert!(!cpu.negative());

        // Test that the carry, zero, and negative flags get set correctly when
        // A > M.
        cpu.memory.store(0x0000, 0x04);
        cpu.pc = 0x0000;
        cpu.set_carry(false);
        cpu.set_zero(true);
        cpu.set_negative(true);
        cpu.cpx(0x0000);
        assert!(cpu.carry());
        assert!(!cpu.zero());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_cpy() {
        let mut cpu = CPU::new();
        cpu.y = 0x05;

        // Test that the carry, zero, and negative flags get set correctly when
        // A < M.
        cpu.memory.store(0x0000, 0x06);
        cpu.set_carry(true);
        cpu.set_zero(true);
        cpu.set_negative(false);
        cpu.cpy(0x0000);
        assert!(!cpu.carry());
        assert!(!cpu.zero());
        assert!(cpu.negative());

        // Test that the carry, zero, and negative flags get set correctly when
        // A = M.
        cpu.memory.store(0x0000, 0x05);
        cpu.pc = 0x0000;
        cpu.set_carry(false);
        cpu.set_zero(false);
        cpu.set_negative(true);
        cpu.cpy(0x0000);
        assert!(cpu.carry());
        assert!(cpu.zero());
        assert!(!cpu.negative());

        // Test that the carry, zero, and negative flags get set correctly when
        // A > M.
        cpu.memory.store(0x0000, 0x04);
        cpu.pc = 0x0000;
        cpu.set_carry(false);
        cpu.set_zero(true);
        cpu.set_negative(true);
        cpu.cpy(0x0000);
        assert!(cpu.carry());
        assert!(!cpu.zero());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_dec() {
        let mut cpu = CPU::new();

        cpu.memory.store(0x0000, 0xFF);
        cpu.set_zero(true);
        cpu.set_negative(false);
        cpu.dec(0x0000);
        assert_eq!(cpu.memory.fetch(0x0000), 0xFE);
        assert!(!cpu.zero());
        assert!(cpu.negative());

        cpu.memory.store(0x0000, 0x01);
        cpu.set_zero(false);
        cpu.set_negative(true);
        cpu.dec(0x0000);
        assert_eq!(cpu.memory.fetch(0x0000), 0x00);
        assert!(cpu.zero());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_dex() {
        let mut cpu = CPU::new();

        cpu.x = 0xFF;
        cpu.set_zero(true);
        cpu.set_negative(false);
        cpu.dex();
        assert_eq!(cpu.x, 0xFE);
        assert!(!cpu.zero());
        assert!(cpu.negative());

        cpu.x = 0x01;
        cpu.set_zero(false);
        cpu.set_negative(true);
        cpu.dex();
        assert_eq!(cpu.x, 0x00);
        assert!(cpu.zero());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_dey() {
        let mut cpu = CPU::new();

        cpu.y = 0xFF;
        cpu.set_zero(true);
        cpu.set_negative(false);
        cpu.dey();
        assert_eq!(cpu.y, 0xFE);
        assert!(!cpu.zero());
        assert!(cpu.negative());

        cpu.y = 0x01;
        cpu.set_zero(false);
        cpu.set_negative(true);
        cpu.dey();
        assert_eq!(cpu.y, 0x00);
        assert!(cpu.zero());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_eor() {
        let mut cpu = CPU::new();

        cpu.a = 0xFF;
        cpu.memory.store(0x0000, 0x0F);
        cpu.set_zero(true);
        cpu.set_negative(false);
        cpu.eor(0x0000);
        assert_eq!(cpu.a, 0xF0);
        assert!(!cpu.zero());
        assert!(cpu.negative());

        cpu.a = 0xFF;
        cpu.memory.store(0x0000, 0xFF);
        cpu.set_zero(false);
        cpu.set_negative(true);
        cpu.eor(0x0000);
        assert_eq!(cpu.a, 0x00);
        assert!(cpu.zero());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_inc() {
        let mut cpu = CPU::new();

        cpu.memory.store(0x0000, 0xFF);
        cpu.set_zero(false);
        cpu.set_negative(true);
        cpu.inc(0x0000);
        assert_eq!(cpu.memory.fetch(0x0000), 0x00);
        assert!(cpu.zero());
        assert!(!cpu.negative());

        cpu.memory.store(0x0000, 0xFE);
        cpu.set_zero(true);
        cpu.set_negative(false);
        cpu.inc(0x0000);
        assert_eq!(cpu.memory.fetch(0x0000), 0xFF);
        assert!(!cpu.zero());
        assert!(cpu.negative());
    }

    #[test]
    fn test_inx() {
        let mut cpu = CPU::new();

        cpu.x = 0xFF;
        cpu.set_zero(false);
        cpu.set_negative(true);
        cpu.inx();
        assert_eq!(cpu.x, 0x00);
        assert!(cpu.zero());
        assert!(!cpu.negative());

        cpu.x = 0xFE;
        cpu.set_zero(true);
        cpu.set_negative(false);
        cpu.inx();
        assert_eq!(cpu.x, 0xFF);
        assert!(!cpu.zero());
        assert!(cpu.negative());
    }

    #[test]
    fn test_iny() {
        let mut cpu = CPU::new();

        cpu.y = 0xFF;
        cpu.set_zero(false);
        cpu.set_negative(true);
        cpu.iny();
        assert_eq!(cpu.y, 0x00);
        assert!(cpu.zero());
        assert!(!cpu.negative());

        cpu.y = 0xFE;
        cpu.set_zero(true);
        cpu.set_negative(false);
        cpu.iny();
        assert_eq!(cpu.y, 0xFF);
        assert!(!cpu.zero());
        assert!(cpu.negative());
    }

    #[test]
    fn test_jmp() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0000, 0xBB);
        cpu.memory.store(0x0001, 0xAA);

        assert_eq!(cpu.pc, 0x0000);
        cpu.jmp(0x0000);
        assert_eq!(cpu.pc, 0xAABB);
    }

    #[test]
    fn test_jsr() {
        let mut cpu = CPU::new();
        cpu.pc = 0x0220;
        cpu.memory.store(0x0220, 0xBB);
        cpu.memory.store(0x0221, 0xAA);

        assert_eq!(cpu.pc, 0x0220);
        cpu.jsr(0x0220);
        assert_eq!(cpu.pc, 0xAABB);
        assert_eq!(cpu.peek(0), 0x1F);
        assert_eq!(cpu.peek(1), 0x02);
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
    fn test_ldx() {
        let mut cpu = CPU::new();

        cpu.memory.store(0x0200, 0xFF);
        cpu.set_zero(true);
        cpu.set_negative(false);
        assert_eq!(cpu.x, 0x00);
        cpu.ldx(0x0200);
        assert_eq!(cpu.x, 0xFF);
        assert!(!cpu.zero());
        assert!(cpu.negative());

        cpu.x = 0xFF;
        cpu.memory.store(0x0200, 0x00);
        cpu.set_zero(false);
        cpu.set_negative(true);
        assert_eq!(cpu.x, 0xFF);
        cpu.ldx(0x0200);
        assert_eq!(cpu.x, 0x00);
        assert!(cpu.zero());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_ldy() {
        let mut cpu = CPU::new();

        cpu.memory.store(0x0200, 0xFF);
        cpu.set_zero(true);
        cpu.set_negative(false);
        assert_eq!(cpu.y, 0x00);
        cpu.ldy(0x0200);
        assert_eq!(cpu.y, 0xFF);
        assert!(!cpu.zero());
        assert!(cpu.negative());

        cpu.y = 0xFF;
        cpu.memory.store(0x0200, 0x00);
        cpu.set_zero(false);
        cpu.set_negative(true);
        assert_eq!(cpu.y, 0xFF);
        cpu.ldy(0x0200);
        assert_eq!(cpu.y, 0x00);
        assert!(cpu.zero());
        assert!(!cpu.negative());
    }

    #[test]
    fn test_lsr() {
        let mut cpu = CPU::new();

        cpu.a = 0xFF;
        cpu.set_carry(false);
        cpu.set_zero(true);
        cpu.set_negative(true);
        assert_eq!(cpu.a, 0xFF);
        cpu.lsr_acc();
        assert_eq!(cpu.a, 0x7F);
        assert!(cpu.carry());
        assert!(!cpu.zero());
        assert!(!cpu.negative());

        cpu.a = 0x00;
        cpu.set_carry(true);
        cpu.set_zero(false);
        assert_eq!(cpu.a, 0x00);
        cpu.lsr_acc();
        assert_eq!(cpu.a, 0x00);
        assert!(!cpu.carry());
        assert!(cpu.zero());
    }

    #[test]
    fn test_nop() {
        let mut cpu = CPU::new();
        cpu.memory.store(0x0200, NOP as u8);
        cpu.pc = 0x0200;

        let mut cpu2 = cpu.clone();
        cpu2.step();
        assert_eq!(cpu2.pc, 0x0201);
        cpu2.pc -= 1;

        assert_eq!(cpu.a, cpu2.a);
        assert_eq!(cpu.x, cpu2.x);
        assert_eq!(cpu.y, cpu2.y);
        assert_eq!(cpu.p, cpu2.p);
        assert_eq!(cpu.pc, cpu2.pc);
        assert_eq!(cpu.sp, cpu2.sp);
    }

    #[test]
    fn test_bit_set() {
        let mut value = 0;
        value = bit_set(value, 0, true);
        assert_eq!(value, 0b0000_0001);
        value = bit_set(value, 0, true);
        assert_eq!(value, 0b0000_0001);
        value = bit_set(value, 7, true);
        assert_eq!(value, 0b1000_0001);
        value = bit_set(value, 7, false);
        assert_eq!(value, 0b0000_0001);
    }

    #[test]
    fn test_bit_get() {
        assert_eq!(bit_get(0b1000_0000, 7), true);
        assert_eq!(bit_get(0b1000_0000, 6), false);
    }
}
