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

        pub fn as_ptr(self) -> *mut T {
            self.pointer as *mut T
        }
    }

    impl<T> Copy for NonNull<T> {}
    impl<T> Clone for NonNull<T> {
        fn clone<'a>(&'a self) -> Self {
            *self
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

            pub fn load_seq_cst<'a>(&'a self) -> usize {
                abort();
            }

            pub fn fetch_add_seq_cst<'a>(&'a self, val: usize) -> usize {
                abort();
            }

            pub fn compare_exchange_seq_cst<'a>(
                &'a self,
                current: usize,
                new: usize,
            ) -> Result<usize, usize> {
                abort();
            }

            pub fn fetch_update_seq_cst<'a, F>(&'a self, mut f: F) -> Result<usize, usize>
            where
                F: FnMut(usize) -> Option<usize>,
            {
                abort();
            }
        }
    }
}

use ptr::NonNull;
use sync::atomic::AtomicUsize;

//TODO: This will not be necessary in an approximation which ignores counter ovf possibility
const MAX_REFCOUNT: usize = (isize::MAX) as usize;

fn is_dangling<T>(ptr: *mut T) -> bool {
    //TODO: I am not sure why is the cast. Might be related to alignment
    (ptr as *mut ()).addr() == usize::MAX
}

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

struct WeakInner<'a> {
    weak: &'a AtomicUsize,
    strong: &'a AtomicUsize,
}

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

    pub fn strong_count<'a>(this: &'a Self) -> usize {
        this.inner().strong.load_seq_cst()
    }

    pub fn weak_count<'a>(this: &'a Self) -> usize {
        let cnt = this.inner().weak.load_seq_cst();
        // If the weak count is currently locked, the value of the
        // count was 0 just before taking the lock.
        if cnt == usize::MAX {
            0
        } else {
            cnt - 1
        }
    }

    pub fn downgrade<'a>(this: &'a Self) -> WeakU32 {
        let mut cur = this.inner().weak.load_seq_cst();
        loop {
            // check if the weak counter is currently "locked"; if so, spin.
            if cur == usize::MAX {
                cur = this.inner().weak.load_seq_cst();
                continue;
            }
            if cur > MAX_REFCOUNT {
                abort();
            }
            match this.inner().weak.compare_exchange_seq_cst(cur, cur + 1) {
                Ok(_) => {
                    return WeakU32 { ptr: this.ptr };
                }
                Err(old) => cur = old,
            }
        }
    }
}

impl std::ops::Deref for ArcU32 {
    type Target = u32;

    fn deref<'a>(&'a self) -> &u32 {
        &self.inner().data
    }
}

impl Clone for ArcU32 {
    fn clone<'a>(&'a self) -> ArcU32 {
        let old_size = self.inner().strong.fetch_add_seq_cst(1);
        if old_size > MAX_REFCOUNT {
            abort();
        }
        unsafe { Self::from_inner(self.ptr) }
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

    fn inner<'a>(&'a self) -> Option<WeakInner<'_>> {
        let ptr = self.ptr.as_ptr();
        if is_dangling(ptr) {
            None
        } else {
            Some(unsafe {
                WeakInner {
                    strong: &(*ptr).strong,
                    weak: &(*ptr).weak,
                }
            })
        }
    }

    fn checked_increment(n: usize) -> Option<usize> {
        // Any write of 0 we can observe leaves the field in permanently zero state.
        if n == 0 {
            return None;
        }
        if n > MAX_REFCOUNT {
            abort();
        }
        Some(n + 1)
    }

    pub fn upgrade<'a>(&'a self) -> Option<ArcU32> {
        if self
            .inner()?
            .strong
            .fetch_update_seq_cst(Self::checked_increment)
            .is_ok()
        {
            unsafe { Some(ArcU32::from_inner(self.ptr)) }
        } else {
            None
        }
    }
}

impl Clone for WeakU32 {
    fn clone<'a>(&'a self) -> WeakU32 {
        if let Some(inner) = self.inner() {
            let old_size = inner.weak.fetch_add_seq_cst(1);
            if old_size > MAX_REFCOUNT {
                abort();
            }
        }
        WeakU32 { ptr: self.ptr }
    }
}
