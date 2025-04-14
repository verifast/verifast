use std::option::Option;

pub fn foo(o: Option<*mut i32>) -> Option<i32> {
    match o {
        None => None,
        Some(p) => Some(unsafe { p as usize as i32 })
    }
}
