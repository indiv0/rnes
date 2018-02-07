extern crate rnes;

use rnes::{Memory, NESMemory};

fn main() {
    let mut memory = NESMemory::new();
    memory.store(0x0000, 0x0A);
    println!("Memory value at 0x0000: {}", memory.fetch(0x0000));
}
