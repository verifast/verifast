pub fn scoped_blocks(x: i32) -> i32 {
    let mut sum = 0;
    {
        let a = {
            let tmp = x + 1;
            tmp
        };
        sum += a;
    }
    {
        let b = x * 2;
        sum += b;
    }
    sum
}

fn main() {}
