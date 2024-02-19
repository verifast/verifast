#![feature(negative_impls)]
#![allow(dead_code)]

/*
About the definition of `[[MutexU32]].Shr(k, t, l)`:
    In the proof of `Ty-Share` we need to get `MutexU32_full_borrow_content`, specifically `data` back, on the other hand we cannot keep track of 
    `SysMutex` fractions used to get the lock because in the proof of `MutexU32::lock` we need to close the `frac_borrow` which means we need the
    `SysMutex` fraction we used to lock the mutex back from method `sys::locks::Mutex::lock`. To solve this we put a `full_borrow` of `data` in the inner `SysMutex`
    and keep the `end_borrow_token` in the fractured borrow. The part of `Ty-Share`'s proof that represents the moment that sharing ends gets the whole `end_borrow`
    token and is able to retrive the `data`. The full borrow in the inner `SysMutex` gets leaked which is fine because we do not need it anymore.
*/

mod sys {
    pub mod locks {
        use std::process::abort;
        /* Based on `NORMAL` `pthread_mutex_t` described in https://pubs.opengroup.org/onlinepubs/9699919799/ */
        pub struct Mutex { m: *mut u32 }
        /*@
        // dummy
        pred sys::locks::Mutex_own(t: thread_id_t, m: *u32);
        pred sys::locks::Mutex_share(k: lifetime_t, t: thread_id_t, l: *sys::locks::Mutex;) = true;
        lem sys::locks::Mutex_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *sys::locks::Mutex)
        req lifetime_inclusion(k1, k) == true &*& [_]sys::locks::Mutex_share(k, t, l);
        ens [_]sys::locks::Mutex_share(k1, t, l);
        {}
        lem sys::locks::Mutex_share_full(k: lifetime_t, t: thread_id_t, l: *sys::locks::Mutex)
        req full_borrow(k, sys::locks::Mutex_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
        ens [_]sys::locks::Mutex_share(k, t, l) &*& [q]lifetime_token(k);
        {
            leak full_borrow(_, _);
        }
        // ymmud

        pred SysMutex(m: sys::locks::Mutex; P: pred());
        pred SysMutex::new_ghost_arg(P: pred()) = true;
        pred SysMutex_locked(m: sys::locks::Mutex, P: pred(); t: thread_id_t);        
        /* When we have the whole `SysMutex` chunk it means frame is empty, i.e. no other thread has access to this mutex. */
        lem SysMutex_renew(m: sys::locks::Mutex, Q: pred());
            req SysMutex(m, ?P) &*& Q();
            ens SysMutex(m, Q);
        /* With these specification we cannot know if the mutex is free, but in presence of `SysMutex_locked(...) we know it is locked.
           So the proof sketch for this lemma would be:
           No other thread has access to this mutex.
           If
               - The mutex is free and the resource `P` is protected by mutex; It is in the mutex so to speak. We substitute `P` with `Q`
               and from this point there will be no `[q]SysMutex(m, P)` anywhere. It means we forget about `P`. The state is just like after
               a call to `sys::locks::Mutex::new` to protect `Q()`.

               - The mutex is locked it means there should be a `SysMutex_locked(m, P(), ?t, ?q)` and `P()` in resources of some thread(s).
               Operations in this state:
                   - `lock` gets verified which is fine because this call will not terminate unless someone frees the lock. after that we get
                   `Q() &*& SysMutex_locked(m, Q, ..)` and we are in a consistent state.
                   - `unlock` needs to be called by thread `t` and requires `SysMutex_locked(m, P, ?t, ..) &*& P()`. It will soundly free the
                   mutex but here the P() is leaked again. state from here is consistent.
                   - Todo: `drop` will show undefined behaviour unless it knows the mutex is free. its specification needs to change.
                   https://pubs.opengroup.org/onlinepubs/9699919799/
        */
        // Todo: should we change our nonatomic_borrow to have a void * instead of mask so it would be compatible with Iris.
        /* Todo: we can put non-persistent predicate in `[[T]].Shr(k, t, l)` which is inconsistent with `Ty-Shr-Persist`. I think, not sure, our aproach for
        producing and consumming dummy fractions of `Shr` component is not enough and unsound.
        */
        @*/

        impl Mutex {
            pub unsafe fn new() -> Mutex
            //@ req SysMutex::new_ghost_arg(?P) &*& P();
            //@ ens SysMutex(result, P);
            {
                abort();
            }

            pub unsafe fn lock<'a>(&'a self)
            //@ req thread_token(?t) &*& [?q](*self) |-> ?m &*& [?q1]SysMutex(m, ?P);
            //@ ens thread_token(t) &*& [q](*self) |-> m &*& [q1]SysMutex(m, P) &*& SysMutex_locked(m, P, t) &*& P();
            {
                abort();
            }

            pub unsafe fn unlock<'a>(&'a self)
            //@ req thread_token(?t) &*& [?q](*self) |-> ?m &*& SysMutex_locked(m, ?P, t) &*& P();
            //@ ens thread_token(t) &*& [q](*self) |-> m;
            {
                abort();
            }

            /*impl Drop for Mutex */
            unsafe fn drop<'a>(&'a mut self)
            /*
            Todo: It is not sound. `https://pubs.opengroup.org/onlinepubs/9699919799/functions/pthread_mutex_destroy.html`
            It shall be safe to destroy an initialized mutex that is unlocked. Attempting to destroy a locked mutex,
            or a mutex that another thread is attempting to lock, or a mutex that is being used in a pthread_cond_timedwait() or pthread_cond_wait() call
            by another thread, results in undefined behavior.
            */
            //@ req (*self) |-> ?m &*& SysMutex(m, _);
            //@ ens true;
            {
                abort();
            }
        }
    }
}

use std::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
};

/*pub*/ struct MutexU32 {
    inner: sys::locks::Mutex,
    data: UnsafeCell<u32>,
}
// By this definition MutexU32 is Send and Sync automatically
/*@
pred True(;) = true;
pred MutexU32_own(t: thread_id_t, inner: sys::locks::Mutex, data: u32) = SysMutex(inner, True);


pred_ctor MutexU32_full_borrow_content0(t: thread_id_t, l: *MutexU32)() =
    (*l).inner |-> ?inner &*& (*l).data |-> ?data &*& MutexU32_own(t, inner, data);

pred_ctor SysMutex_content(k1: lifetime_t, t: thread_id_t, l: *MutexU32)(;) =
    full_borrow(k1, u32_full_borrow_content(t, &(*l).data));

pred_ctor MutexU32_frac_borrow_content(k1: lifetime_t, t: thread_id_t, l: *MutexU32)(;) =
     (*l).inner |-> ?inner &*& SysMutex(inner, SysMutex_content(k1, t, l)) &*& borrow_end_token(k1, u32_full_borrow_content(t, &(*l).data));

pred MutexU32_share(k: lifetime_t, t: thread_id_t, l: *MutexU32) =
    exists_np(?k1) &*& lifetime_inclusion(k, k1) == true &*& frac_borrow(k, MutexU32_frac_borrow_content(k1, t, l));

lem MutexU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *MutexU32)
    req lifetime_inclusion(k1, k) == true &*& [_]MutexU32_share(k, t, l);
    ens [_]MutexU32_share(k1, t, l);
{
    open MutexU32_share(k, t, l); assert [_]exists_np(?k10);
    frac_borrow_mono(k, k1, MutexU32_frac_borrow_content(k10, t, l));
    assert [?q]frac_borrow(k1, _); close [q]exists_np(k10);
    // @Bart Why does VeriFast not just close using any dummy fraction when it is trying to close a dummy fraction?
    lifetime_inclusion_trans(k1, k, k10);
    close [q]MutexU32_share(k1, t, l);
}

lem MutexU32_share_full(k: lifetime_t, t: thread_id_t, l: *MutexU32)
    req full_borrow(k, MutexU32_full_borrow_content0(t, l)) &*& [?q]lifetime_token(k);
    ens [_]MutexU32_share(k, t, l) &*& [q]lifetime_token(k);
{
    open_full_borrow_strong(k, MutexU32_full_borrow_content0(t, l), q);
    assert exists(?k1);
    produce_lem_ptr_chunk full_borrow_convert_strong(MutexU32_frac_borrow_content(k1, t, l), k1, MutexU32_full_borrow_content0(t, l))()
    {  // The end of sharing
        open MutexU32_frac_borrow_content(k1, t, l)();
        borrow_end(k1, u32_full_borrow_content(t, &(*l).data));
        open u32_full_borrow_content(t, &(*l).data)();
        assert (*l).inner |-> ?inner; assert (*l).data |-> ?data;
        SysMutex_renew(inner, True);
        close MutexU32_own(t, inner, data);
        close MutexU32_full_borrow_content0(t, l)();
    }{ // The sharing moment
        open MutexU32_full_borrow_content0(t, l)();
        close u32_full_borrow_content(t, &(*l).data)();
        borrow(k1, u32_full_borrow_content(t, &(*l).data));
        close SysMutex_content(k1, t, l)();
        open MutexU32_own(t, ?inner, ?data);
        SysMutex_renew(inner, SysMutex_content(k1, t, l));
        close_full_borrow_strong(k1, MutexU32_full_borrow_content0(t, l), MutexU32_frac_borrow_content(k1, t, l));
    }
    full_borrow_into_frac(k1, MutexU32_frac_borrow_content(k1, t, l));
    frac_borrow_mono(k1, k, MutexU32_frac_borrow_content(k1, t, l));
    assert [?qshr] frac_borrow(_, _);
    close [qshr]exists_np(k1);
    close [qshr]MutexU32_share(k, t, l);
}
@*/
/*pub*/ struct MutexGuardU32/*<'a>*/ {
    lock: *const MutexU32,
//    lock: &'a MutexU32,
}


impl !Send for MutexGuardU32/*<'_>*/ {}
/*@
pred MutexU32_locked(l: *MutexU32; t: thread_id_t);
lem MutexU32_locked_unwrap(l: *MutexU32, t: thread_id_t);
    req MutexU32_locked(l, t) &*& [?qi](*l).inner |-> ?inner &*& [?qm]SysMutex(inner, ?P);
    ens [qi](*l).inner |-> inner &*& [qm]SysMutex(inner, P) &*& SysMutex_locked(inner, P, t);
lem MutexU32_locked_wrap(l: *MutexU32);
    req [?qi](*l).inner |-> ?inner &*& [?qm]SysMutex(inner, ?P) &*& SysMutex_locked(inner, P, ?t);
    ens [qi](*l).inner |-> inner &*& [qm]SysMutex(inner, P) &*& MutexU32_locked(l, t);

pred_ctor MutexGuardU32_own(km: lifetime_t)(t: thread_id_t, lock: *MutexU32) =
    [_]MutexU32_share(km, t, lock) &*& MutexU32_locked(lock, t) &*& full_borrow(?k1, u32_full_borrow_content(t, &(*lock).data));

pred_ctor MutexGuardU32_full_borrow_content0(km: lifetime_t)(t: thread_id_t, l: *MutexGuardU32) =
    (*l).lock |-> ?lock &*& MutexGuardU32_own(km)(t, lock);

pred_ctor MutexGuardU32_share(km: lifetime_t)(k: lifetime_t, t: thread_id_t, l: *MutexGuardU32) = true /* Todo: Not very interesting */;
@*/


// It is Sync automatically as in our case `T=u32` and `u32:Sync`
//unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}

impl MutexU32 {
    /// The exact behavior on locking a mutex in the thread which already holds
    /// the lock is left unspecified. However, this function will not return on
    /// the second call (it might panic or deadlock, for example).
    pub unsafe fn lock<'a>(&'a self) -> MutexGuardU32/*<'a>*/
    //@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& [_]MutexU32_share(a, t, self);
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& MutexGuardU32_own(a)(t, self);
    {
        unsafe {
            //@ open MutexU32_share(a, t, self);
            //@ assert [_]exists_np(?k1);
            //@ open_frac_borrow(a, MutexU32_frac_borrow_content(k1, t, self), qa);
            //@ open MutexU32_frac_borrow_content(k1, t, self)();
            self.inner.lock();
            //@ MutexU32_locked_wrap(self);
            //@ assert [?qp](*self).inner |-> _;
            //@ close_frac_borrow(qp, MutexU32_frac_borrow_content(k1, t, self));
            //@ open SysMutex_content(k1, t, self)();
            MutexGuardU32::new(self)
        }
    }
}

impl/*<'mutex>*/ MutexGuardU32/*<'mutex>*/ {
    /* because MutexGuardU32_own is pred_ctor and not supported yet */
    unsafe fn new<'a>(lock: &'a/*'mutex*/ MutexU32) -> MutexGuardU32/*<'mutex>*/
    //@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& [_]MutexU32_share(a, t, lock) &*& MutexU32_locked(lock, t) &*& full_borrow(?k1, u32_full_borrow_content(t, &(*lock).data));
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& MutexGuardU32_own(a)(t, lock);
    {
        //@ close MutexGuardU32_own(a)(t, lock);
        MutexGuardU32 { lock }
    }
}
/*
impl MutexU32 {
    pub fn new(v: u32) -> MutexU32 {
        MutexU32 {
            inner: unsafe { sys::locks::Mutex::new() },
            data: UnsafeCell::new(v),
        }
    }

    pub fn lock<'a>(&'a self) -> MutexGuardU32/*<'a>*/ {
        unsafe {
            self.inner.lock();
            MutexGuardU32::new(self)
        }
    }

    pub fn unlock<'a>(guard: MutexGuardU32/*<'a>*/) {
        drop(guard);
    }
}
*/
/*
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
*/
