#![feature(allocator_api)]

use std::alloc::Allocator;

unsafe fn Allocator_clone__VeriFast_wrapper<A: Allocator + Clone>(alloc: &A) -> A {
    foo(alloc.clone()).0
}

pub fn foo<A: Allocator + Clone>(alloc: A) -> (A, A) {
    unsafe {
        let alloc_clone = Allocator_clone__VeriFast_wrapper(&alloc);
        (alloc, alloc_clone)
    }
}
