fn foo(x: Option<i32>) -> Option<i32> {
    match x {
        None => None,
        Some(y) => Some(y)
    }
}
