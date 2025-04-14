#![feature(allocator_api)]

use std::alloc::Allocator;

unsafe fn Allocator_clone__VeriFast_wrapper<'a, B: Allocator + Clone>(alloc: &'a B) -> B {
    alloc.clone()
}

pub fn foo<C: Allocator + Clone>(alloc: C) -> (C, C) {
    unsafe {
        let alloc_clone = Allocator_clone__VeriFast_wrapper(&alloc);
        (alloc, alloc_clone)
    }
}
