use std::option::Option;

pub fn foo(o: Option<*mut i32>, n: i32) -> Option<i32> {
    o.map(|p| unsafe { *p } ^ n)
}
