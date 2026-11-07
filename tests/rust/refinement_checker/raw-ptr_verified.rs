pub struct S {
    a: i32,
    b: i32,
}

unsafe fn field_addr(s: *mut S) -> *mut i32 {
    let r = &raw mut (*s).b;
    r
}

unsafe fn read_field(s: *const S) -> i32 {
    let p = &raw const (*s).a;
    *p
}

unsafe fn discard_addr(s: *mut S) {
    let _p = &raw const (*s).a;
    let _q = ();
}

fn local_addr() -> i32 {
    let mut x = 5;
    let p = &raw mut x;
    let q = p;
    unsafe { *q += 1; }
    x
}

fn main() {}
