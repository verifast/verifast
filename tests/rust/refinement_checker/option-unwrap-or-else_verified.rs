use std::option::Option;

fn foo(o: Option<i32>) -> i32 {
    match o {
        None => 42,
        Some(v) => v,
    }
}
