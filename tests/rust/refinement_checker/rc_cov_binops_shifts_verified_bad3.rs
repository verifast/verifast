pub fn compute_ops(a: u32, b: u32) -> (u32, u32, bool, u32) {
    let sum = a + b;
    let diff = a - b;
    let shl = a << (b & 31);
    let cmp = a <= b; // changed < to <=
    let xor_val = sum ^ diff;
    (sum, shl, cmp, xor_val)
}

fn main() {}
