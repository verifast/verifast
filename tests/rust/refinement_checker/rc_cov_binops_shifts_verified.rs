pub fn compute_ops(a: u32, b: u32) -> (u32, u32, bool, u32) {
    let sum = {
        let tmp = a + b;
        tmp
    };
    let diff = {
        let tmp = a - b;
        tmp
    };
    let shl = a << (b & 31);
    let cmp = a < b;
    let xor_val = sum ^ diff;
    (sum, shl, cmp, xor_val)
}

fn main() {}
