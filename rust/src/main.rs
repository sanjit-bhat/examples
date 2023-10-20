/*
 * This shows the Rust optimization where:
 * if zero is an invalid value for a particular type,
 * Rust will exploit this to generate more mem efficient enums.
*/

pub enum ZeroValid {
    A,
    B(u32),
}

pub enum ZeroNotValid {
    A,
    B(Box<u32>),
}


pub enum ZeroNotValid2 {
    A,
    B(*mut u32),
}

fn main() {
    println!(
        "ZeroValid: {} {}",
        std::mem::size_of::<ZeroValid>(),
        std::mem::size_of::<u32>()
    ); // 8 4
    println!(
        "ZeroNotValid: {} {}",
        std::mem::size_of::<ZeroNotValid>(),
        std::mem::size_of::<Box<u32>>()
    ); // 8 8
    println!(
        "ZeroNotValid2: {} {}",
        std::mem::size_of::<ZeroNotValid2>(),
        std::mem::size_of::<*mut u32>()
    ); // 16 8
}
