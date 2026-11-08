pub fn scoped_blocks(x: i32) -> i32 {
    let mut sum = 0;
    {
        let a = x + 1;
        sum += a;
    }
    // omitted second scoped block
    sum
}

fn main() {}
