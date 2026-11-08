use std::cell::Cell;

pub fn bind_and_replace(opt: Option<Cell<i32>>, r: &mut i32, v: i32) -> (i32, i32) {
    let a = match opt {
        None => 0,
        Some(mut c) => c.get(),
    };
    let r_ref = &mut *r as *mut i32;
    *r;
    let old = std::mem::replace(unsafe { &mut *r_ref }, v);
    (a, old)
}

fn main() {}
