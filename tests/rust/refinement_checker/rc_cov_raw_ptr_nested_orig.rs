pub struct Inner {
    pub val: i32,
    pub other: i32,
}

pub struct Outer {
    pub inner: Inner,
    pub extra: i32,
}

pub unsafe fn test_nested(s: *mut Outer, t: &mut (i32, (i32, i32))) -> (i32, i32) {
    let p_val = &raw mut (*s).inner.val;
    let p_t = &raw const (*t).1.0;
    *p_val = 42;
    let read_t = *p_t;
    ((*s).inner.val, read_t)
}

fn main() {}
