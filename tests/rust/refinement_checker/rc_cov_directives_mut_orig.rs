use std::cell::Cell;

pub fn bind_and_replace(opt: Option<Cell<i32>>, r: &mut i32, v: i32) -> (i32, i32) {
    let a = match opt {
        None => 0,
        Some(/*@~mut@*/ c) => c.get(),
    };
    let old = std::mem::replace(r, { *r; v });
    (a, old)
}

fn main() {}
