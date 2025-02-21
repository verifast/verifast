#![feature(allocator_api)]

use std::alloc::Allocator;

pub fn foo<A: Allocator + Clone>(alloc: A) -> (A, A) {
    let alloc_clone = alloc.clone();
    (alloc, alloc_clone)
}
