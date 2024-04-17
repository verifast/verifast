#![feature(strict_provenance)]

use std::process::abort;

pub mod ptr {
    pub struct NonNull<T> {
        pointer: *const T,
    }

    impl<T> NonNull<T> {
        pub fn from<'a>(reference: &'a mut T) -> Self {
            NonNull {
                pointer: reference as *mut T,
            }
        }

        pub unsafe fn new_unchecked(ptr: *mut T) -> Self {
            NonNull { pointer: ptr }
        }

        pub unsafe fn as_ref<'a>(&'a self) -> &'a T {
            &*self.pointer
        }
    }
}

pub mod boxed {
    use abort;
    pub struct Box<T> {
        ptr: *mut T,
    }

    impl<T> Box<T> {
        pub fn new(x: T) -> Self {
            abort();
        }

        pub fn leak<'a>(x: Self) -> &'a mut T {
            abort();
        }
    }
}
pub mod sync {
    pub mod atomic {
        use abort;
        pub struct AtomicUsize {
            v: usize,
        }

        impl AtomicUsize {
            pub fn new(v: usize) -> AtomicUsize {
                abort();
            }
        }
    }
}

use ptr::NonNull;
use sync::atomic::AtomicUsize;

pub struct ArcU32 {
    ptr: NonNull<ArcInnerU32>,
}

unsafe impl Send for ArcU32 {}
unsafe impl Sync for ArcU32 {}

pub struct WeakU32 {
    ptr: NonNull<ArcInnerU32>,
}

unsafe impl Send for WeakU32 {}
unsafe impl Sync for WeakU32 {}

struct ArcInnerU32 {
    strong: AtomicUsize,
    weak: AtomicUsize,
    data: u32,
}

unsafe impl Send for ArcInnerU32 {}
unsafe impl Sync for ArcInnerU32 {}

impl ArcU32 {
    pub fn new(data: u32) -> ArcU32 {
        let x: Box<_> = Box::new(ArcInnerU32 {
            strong: AtomicUsize::new(1),
            weak: AtomicUsize::new(1),
            data,
        });
        unsafe { Self::from_inner(NonNull::from(Box::leak(x))) }
    }

    unsafe fn from_inner(ptr: NonNull<ArcInnerU32>) -> Self {
        Self { ptr }
    }

    fn inner<'a>(&'a self) -> &'a ArcInnerU32 {
        unsafe { self.ptr.as_ref() }
    }
}

impl std::ops::Deref for ArcU32 {
    type Target = u32;

    fn deref<'a>(&'a self) -> &u32 {
        &self.inner().data
    }
}

impl WeakU32 {
    pub fn new() -> WeakU32 {
        WeakU32 {
            ptr: unsafe {
                NonNull::new_unchecked(std::ptr::invalid_mut::<ArcInnerU32>(usize::MAX))
            },
        }
    }
}
