#![feature(box_into_inner)]
#![feature(allocator_api)]

struct Point<T> {
    x: T,
    y: i32,
}

fn foo<T, A: std::alloc::Allocator>(b: Box<Point<T>, A>) -> T {
    b.x
}