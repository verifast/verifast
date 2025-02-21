#![feature(allocator_api)]

use std::alloc::Allocator;

pub fn foo<A: Allocator + Clone>(alloc: A) -> (A, A) {
    let alloc_ref = &alloc;
    let alloc_clone = alloc_ref.clone();
    (alloc, alloc_clone)
}
