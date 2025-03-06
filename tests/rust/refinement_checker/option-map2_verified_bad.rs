use std::option::Option;

pub fn foo(o: Option<*mut i32>, o1: Option<*mut i32>, p1: *mut i32, v1: Option<i32>, v2: i32) -> Option<i32> {
    match o1 {
        None => None,
        Some(p) => Some(unsafe { *p })
    }
}
