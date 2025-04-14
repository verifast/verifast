#![feature(box_as_ptr)]

struct Point {
    x: i32,
    y: i32,
}

fn foo(b: &Box<Point>) -> i32 {
    let p = Box::as_ptr(b);
    unsafe { (*p).x }
}
