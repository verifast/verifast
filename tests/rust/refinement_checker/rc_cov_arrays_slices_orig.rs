pub fn test_array_slice_ops(a: i32, b: i32, c: i32, s: &[i32]) -> ([i32; 3], usize) {
    let arr = [a, b, c];
    let len = s.len();
    (arr, len)
}

fn main() {}
