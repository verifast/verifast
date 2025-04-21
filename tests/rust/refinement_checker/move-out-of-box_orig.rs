#![feature(box_into_inner)]
#![feature(allocator_api)]

fn foo<T, A: std::alloc::Allocator>(b: Box<T, A>) -> T {
    *b
}
