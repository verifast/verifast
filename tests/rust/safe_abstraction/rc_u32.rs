#![feature(negative_impls)]
use std::{cell::UnsafeCell, process::abort, ptr::NonNull};

/*@
pred nonatomic_inv(t: thread_id_t, m: mask_t, P: pred());
fix add<T>(x: real, y: real) -> real { x + y }
pred_ctor RcBoxU32_na_inv_cnt(ptr: *RcBoxU32)() = (*ptr).strong |-> ?strong &*& [?qv](*ptr).value |-> ?value &*& exists(?qs) &*& length(qs) == strong - 1 &*& fold_left(0 as real, add, qs) + qv == 1;

pred RcU32_own(t: thread_id_t, ptr: std::ptr::NonNull<RcBoxU32>) = [_]nonatomic_inv(t, MaskNshrSingle(std::ptr::NonNull_ptr(ptr)), RcBoxU32_na_inv_cnt(std::ptr::NonNull_ptr(ptr)));
pred RcU32_share(k: lifetime_t, t: thread_id_t, l: *RcU32) = true;
lem RcU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *RcU32)
    req lifetime_inclusion(k1, k) == true &*& [_]RcU32_share(k, t, l);
    ens [_]RcU32_share(k1, t, l);
{}
lem RcU32_share_full(k: lifetime_t, t: thread_id_t, l: *RcU32)
    req atomic_mask(Nlft) &*& full_borrow(k, RcU32_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [_]RcU32_share(k, t, l) &*& [q]lifetime_token(k);
{
    
}
@*/

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

    unsafe fn from_inner(ptr: NonNull<RcBoxU32>) -> Self
    //@ req true;
    //@ ens true;
    {
        Self { ptr }
    }

    fn inner<'a>(&'a self) -> &'a RcBoxU32 {
        unsafe { self.ptr.as_ref() }
    }
}
/*
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
*/