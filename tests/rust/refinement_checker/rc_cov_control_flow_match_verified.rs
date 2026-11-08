pub enum Status {
    Active(i32),
    Pending(u32),
    Inactive,
}

pub fn handle_status(s: Status, flag: bool) -> i32 {
    if !flag {
        let ret = -1;
        return ret;
    }
    match s {
        Status::Active(v) => {
            let tmp = v + 1;
            tmp
        }
        Status::Pending(u) => u as i32,
        Status::Inactive => 0,
    }
}

pub fn count_even(n: i32) -> i32 {
    let mut i = 0;
    let mut count = 0;
    while i < n {
        let step = 1;
        i += step;
        if i % 2 != 0 {
            continue;
        }
        count += 1;
    }
    count
}

fn main() {}
