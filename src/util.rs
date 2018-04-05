/// Number of bytes in a kilobyte.
pub const BYTES_PER_KB: usize = 1024;

/// Number of bytes in a CHR RAM page.
pub const CHR_RAM_PAGE_SIZE: usize = 8 * BYTES_PER_KB;
/// Number of bytes in a CHR ROM page.
pub const CHR_ROM_PAGE_SIZE: usize = 8 * BYTES_PER_KB;
/// Number of bytes in a PRG RAM page.
pub const PRG_RAM_PAGE_SIZE: usize = 8 * BYTES_PER_KB;
/// Number of bytes in a PRG ROM page.
pub const PRG_ROM_PAGE_SIZE: usize = 16 * BYTES_PER_KB;

/// Sets the bit at position `n` to the specified value.
pub fn bit_set(word: u8, n: u8, value: bool) -> u8 {
    (word & (!(1 << n))) | ((value as u8) << n)
}

/// Gets the value of the bit at position `n`.
pub fn bit_get(word: u8, n: u8) -> bool {
    word & (1 << n) != 0
}

/// Returns true if the provided value is negative (i.e., if bit 7 is set).
pub fn is_negative(value: u8) -> bool {
    bit_get(value, 7)
}
