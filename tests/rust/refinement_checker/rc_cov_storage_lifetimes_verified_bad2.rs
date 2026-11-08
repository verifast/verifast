pub fn scoped_blocks(x: i32) -> i32 {
    let mut sum = 0;
    let mut a = 0;
    {
        a = x + 1;
        sum += a;
    }
    {
        let b = x * 2;
        sum += a; // used wrong local (a instead of b)
    }
    sum
}

fn main() {}
