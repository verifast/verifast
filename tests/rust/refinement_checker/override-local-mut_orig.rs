use std::cell::Cell;

fn foo(x: Option<Cell<i32>>) -> i32 {
    match x {
        None => 0,
        Some(/*@~mut@*/ cell) => cell.get()
    }
}
