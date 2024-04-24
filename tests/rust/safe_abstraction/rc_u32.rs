#![feature(negative_impls)]
use std::process::abort;
use boxed::Box;
use ptr::NonNull;

pub struct RcU32 {
    ptr: NonNull<RcBoxU32>,
}

impl !Send for RcU32 {}
impl !Sync for RcU32 {}

struct RcBoxU32 {
    strong: usize,
    // weak: usize,
    value: u32,
}

impl RcU32 {
    pub fn new(value: u32) -> RcU32 {
        unsafe {
            Self::from_inner(NonNull::from(Box::leak(Box::new(RcBoxU32 {
                strong: 1,
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
