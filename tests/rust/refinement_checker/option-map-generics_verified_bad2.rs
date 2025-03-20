use std::option::Option;

pub fn foo<X>(o: Option<*mut X>, n: *mut X) -> Option<usize> {
    match o {
        None => None,
        Some(p) => Some(n as usize ^ n as usize)
    }
}
