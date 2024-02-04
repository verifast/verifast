#![feature(negative_impls)]
#![allow(dead_code)]

mod sys {
    pub mod locks {
        use std::process::abort;

        pub struct Mutex();

        impl Mutex {
            pub fn new() -> Mutex {
                abort();
            }

            pub unsafe fn lock<'a>(&'a self) {
                abort();
            }

            pub unsafe fn unlock<'a>(&'a self) {
                abort();
            }
        }
    }
}

use std::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
};

pub struct MutexU32 {
    inner: sys::locks::Mutex,
    data: UnsafeCell<u32>,
}
// By this definition MutexU32 is Send and Sync automatically

pub struct MutexGuardU32<'a> {
    lock: &'a MutexU32,
}

/* Based on https://pubs.opengroup.org/onlinepubs/009695399/functions/pthread_mutex_lock.html
If a thread attempts to unlock a mutex that it has not locked or a mutex which is unlocked, undefined behavior results. */
impl !Send for MutexGuardU32<'_> {}
// It is Sync automatically
//unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}

impl MutexU32 {
    pub fn new(v: u32) -> MutexU32 {
        MutexU32 {
            inner: sys::locks::Mutex::new(),
            data: UnsafeCell::new(v),
        }
    }

    pub fn lock<'a>(&'a self) -> MutexGuardU32<'a> {
        unsafe {
            self.inner.lock();
            MutexGuardU32::new(self)
        }
    }

    pub fn unlock<'a>(guard: MutexGuardU32<'a>) {
        drop(guard);
    }
}

impl<'mutex> MutexGuardU32<'mutex> {
    unsafe fn new(lock: &'mutex MutexU32) -> MutexGuardU32<'mutex> {
        MutexGuardU32 { lock }
    }
}

impl Deref for MutexGuardU32<'_> {
    type Target = u32;
    fn deref<'a>(&'a self) -> &'a u32 {
        unsafe { &*self.lock.data.get() }
    }
}

impl DerefMut for MutexGuardU32<'_> {
    fn deref_mut<'a>(&'a mut self) -> &'a mut u32 {
        unsafe { &mut *self.lock.data.get() }
    }
}

impl Drop for MutexGuardU32<'_> {
    fn drop<'a>(&'a mut self) {
        unsafe {
            self.lock.inner.unlock();
        }
    }
}
