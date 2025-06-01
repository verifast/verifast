use std::option::Option;

fn foo(o: Option<i32>) -> i32 {
    o.unwrap_or_else(|| 42)
}
