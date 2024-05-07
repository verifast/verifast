#![feature(negative_impls)]
use std::{cell::UnsafeCell, process::abort, ptr::NonNull};

pub struct RcU32 {
    ptr: NonNull<RcBoxU32>,
}

impl !Send for RcU32 {}
impl !Sync for RcU32 {}

struct RcBoxU32 {
    strong: UnsafeCell<usize>,
    // weak: UnsafeCell<usize>,
    value: u32,
}

impl RcU32 {
    pub fn new(value: u32) -> RcU32 {
        unsafe {
            Self::from_inner(NonNull::from(Box::leak(Box::new(RcBoxU32 {
                strong: UnsafeCell::new(1),
                value,
            }))))
        }
    }

    unsafe fn from_inner(ptr: NonNull<RcBoxU32>) -> Self {
        Self { ptr }
    }

    fn inner<'a>(&'a self) -> &'a RcBoxU32 {
        unsafe { self.ptr.as_ref() }
    }
}

impl std::ops::Deref for RcU32 {
    type Target = u32;

    fn deref<'a>(&'a self) -> &'a u32 {
        &self.inner().value
    }
}

impl Clone for RcU32 {
    fn clone<'a>(&'a self) -> Self {
        unsafe {
            let strong = self.inner().strong.get();
            if *strong == usize::MAX {
                abort();
            }
            *strong = *strong + 1;
            Self::from_inner(self.ptr)
        }
    }
}

impl Drop for RcU32 {
    fn drop<'a>(&'a mut self) {
        unsafe {
            let strong = self.inner().strong.get();
            *strong = *strong - 1;
            if *strong == 0 {
                // No need to drop a u32
                std::alloc::dealloc(
                    self.ptr.as_ptr() as *mut u8,
                    std::alloc::Layout::new::<RcBoxU32>(),
                );
            }
        }
    }
}
