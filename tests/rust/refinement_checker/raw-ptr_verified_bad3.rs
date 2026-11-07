pub struct S {
    a: i32,
    b: i32,
}

unsafe fn field_addr(s: *mut S) -> *mut i32 {
    &raw mut (*s).b
}

unsafe fn read_field(s: *const S) -> i32 {
    *(&raw const (*s).a)
}

unsafe fn discard_addr(s: *mut S) {
    let _p = &raw const (*s).a;
}

fn local_addr() -> i32 {
    let mut x = 5;
    let p = &raw mut x;
    let q = p;
    unsafe { *q += 2; } // different update through the pointer
    x
}

fn main() {}
