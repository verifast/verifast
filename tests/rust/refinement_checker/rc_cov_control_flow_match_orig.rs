pub enum Status {
    Active(i32),
    Pending(u32),
    Inactive,
}

pub fn handle_status(s: Status, flag: bool) -> i32 {
    if !flag {
        return -1;
    }
    match s {
        Status::Active(v) => v + 1,
        Status::Pending(u) => u as i32,
        Status::Inactive => 0,
    }
}

pub fn count_even(n: i32) -> i32 {
    let mut i = 0;
    let mut count = 0;
    while i < n {
        i += 1;
        if i % 2 != 0 {
            continue;
        }
        count += 1;
    }
    count
}

fn main() {}
