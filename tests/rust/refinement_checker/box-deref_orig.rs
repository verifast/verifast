#![feature(box_as_ptr)]

struct Point {
    x: i32,
    y: i32,
}

fn foo(b: Box<Point>) -> (i32, Box<Point>) {
    (b.x, b)
}
