use std::option::Option;

pub fn foo<A>(o: Option<*mut A>, n: *mut A) -> Option<usize> {
    o.map(|p| p as usize ^ n as usize)
}
