pub fn helper(a: i32, b: i32, out: &mut i32) -> i32 {
    *out = a - b;
    a + b
}

pub fn test_calls(x: i32, y: i32) -> (i32, i32) {
    let mut z = 0;
    let sum = x + y; // omitted helper function call
    (sum, z)
}

fn main() {}
