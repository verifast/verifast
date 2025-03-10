#![feature(box_into_inner)]

fn foo(b: Box<i32>) -> i32 {
    Box::into_inner(b)
}
