fn inc(mut b: Box<u8>) -> Box<u8> { *b = *b + 1; b }
fn main() { let mut x = Box::new(42); x = inc(x); assert_eq!(*x, 43); }