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
