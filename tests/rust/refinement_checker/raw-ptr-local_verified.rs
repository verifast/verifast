// `&raw` of locals: a field of a tuple local, a local in a loop, and a write through the
// raw pointer that must not be dropped.

fn tuple_field() -> i32 {
    let mut t = (1, 2);
    let p = &raw mut t.1;
    let q = p;
    unsafe { *q += 10; }
    t.0 + t.1
}

fn in_loop(n: u32) -> u32 {
    let mut s = 0;
    let mut i = 0;
    while i < n {
        let p = &raw mut s;
        let q = p;
        unsafe { *q += 1; }
        i += 1;
    }
    s
}

fn write_through() -> i32 {
    let mut x = 1;
    let p = &raw mut x;
    let q = p;
    unsafe { *q = 2; }
    x
}

fn main() {}
