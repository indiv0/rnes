use memory::{Address, Memory};

// Addresses of all registers utilized by the APU.
const REG_PULSE_1_TIMER: Address = 0x4000;
const _REG_PULSE_1_LENGTH_COUNTER: Address = 0x4001;
const _REG_PULSE_1_ENVELOPE: Address = 0x4002;
const _REG_PULSE_1_SWEEP: Address = 0x4003;
const _REG_PULSE_2_TIMER: Address = 0x4004;
const _REG_PULSE_2_LENGTH_COUNTER: Address = 0x4005;
const _REG_PULSE_2_ENVELOPE: Address = 0x4006;
const _REG_PULSE_2_SWEEP: Address = 0x4007;
const _REG_TRIANGLE_TIMER: Address = 0x4008;
const _REG_TRIANGLE_LENGTH_COUNTER: Address = 0x400A;
const _REG_TRIANGLE_LINEAR_COUNTER: Address = 0x400B;
const _REG_NOISE_TIMER: Address = 0x400C;
const _REG_NOISE_LENGTH_COUNTER: Address = 0x400D;
const _REG_NOISE_ENVELOPE: Address = 0x400E;
const _REG_NOISE_LFSR: Address = 0x400F;
const _REG_DMC_TIMER: Address = 0x4010;
const _REG_DMC_MEM_READER: Address = 0x4011;
const _REG_DMC_SAMPLE_BUFFER: Address = 0x4012;
const _REG_DMC_OUTPUT_UNIT: Address = 0x4013;
const REG_STATUS: Address = 0x4015;
const REG_FRAME_COUNTER: Address = 0x4017;

#[derive(Clone, Debug)]
pub struct APU;

impl APU {
    /// Reads the "Status" (`0x4015`) register of the APU.
    fn status(&self) -> u8 {
        // FIXME: implement this correctly.
        0b0000_0000
    }

    /// Sets the "Status" (`0x4015`) register of the APU.
    fn set_status(&mut self, value: u8) {
        // FIXME: implement this correctly.
    }
}

impl Memory for APU {
    // TODO: is it necessary to do something here?
    fn reset(&mut self) {}

    fn fetch(&mut self, address: Address) -> u8 {
        assert!(address >= REG_PULSE_1_TIMER && address <= REG_FRAME_COUNTER);

        match address {
            REG_STATUS => self.status(),
            _ => {
                unimplemented!(
                    "APU/IO not implemented; memory read attempt at: {:#4X}",
                    address
                );
            }
        }
    }

    fn store(&mut self, address: Address, value: u8) -> u8 {
        match address {
            REG_STATUS => {
                let prev = self.status();
                self.set_status(value);
                prev
            }
            _ => unimplemented!(
                "APU/IO not implemented; memory write attempt at: {:#4X}",
                address
            ),
        }
    }
}
