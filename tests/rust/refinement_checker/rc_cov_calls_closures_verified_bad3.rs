pub fn helper(a: i32, b: i32, out: &mut i32) -> i32 {
    *out = a - b;
    a + b
}

pub fn test_calls(x: i32, y: i32) -> (i32, i32) {
    let mut z = 0;
    helper(x, y, &mut z); // called helper twice instead of once
    let sum = helper(x, y, &mut z);
    (sum, z)
}

fn main() {}
