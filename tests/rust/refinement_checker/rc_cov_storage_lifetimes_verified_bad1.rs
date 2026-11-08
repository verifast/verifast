pub fn scoped_blocks(x: i32) -> i32 {
    let mut sum = 0;
    {
        let a = x + 1;
        sum += a + 1; // leaked unintended side effect
    }
    {
        let b = x * 2;
        sum += b;
    }
    sum
}

fn main() {}
