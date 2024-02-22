#![feature(negative_impls)]
#![allow(dead_code)]

/*
About the definitions:
    Since in the proof of `MutexU32::lock` we need to close the `frac_borrow`,
    in the `sys::locks::Mutex` interface; i.e. `SysMutex` fractions required by `sys::locks::Mutex::lock` to lock the mutex should be turened back from the method,
    we cannot keep track of `SysMutex` fractions used to get the lock. So we adapth an interface for `sys::locks::Mutex` such that it does not care
    if the mutex is locked or not.
*/

mod sys {
    pub mod locks {
        use std::process::abort;
        /* Based on `NORMAL` `pthread_mutex_t` described in https://pubs.opengroup.org/onlinepubs/9699919799/ */
        pub struct Mutex {
            m: *mut u32,
        }
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

/*pub*/
struct MutexU32 {
    inner: sys::locks::Mutex,
    data: UnsafeCell<u32>,
}
// By this definition MutexU32 is Send and Sync automatically
/*@
pred True(;) = true;
pred MutexU32_own(t: thread_id_t, inner: sys::locks::Mutex, data: u32) = SysMutex(inner, True);


pred_ctor MutexU32_full_borrow_content0(t: thread_id_t, l: *MutexU32)() =
    (*l).inner |-> ?inner &*& (*l).data |-> ?data &*& MutexU32_own(t, inner, data);

pred_ctor MutexU32_fbc_inner(l: *MutexU32)(;) = (*l).inner |-> ?inner &*& SysMutex(inner, True);
pred_ctor MutexU32_fbc_data(t: thread_id_t, l: *MutexU32)(;) = (*l).data |-> ?v;

pred_ctor SysMutex_content(k1: lifetime_t, t: thread_id_t, l: *MutexU32)(;) =
    full_borrow(k1, MutexU32_fbc_data(t, l));

pred_ctor MutexU32_frac_borrow_content(k1: lifetime_t, t: thread_id_t, l: *MutexU32)(;) =
     (*l).inner |-> ?inner &*& SysMutex(inner, SysMutex_content(k1, t, l));

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
    produce_lem_ptr_chunk implies(sep(MutexU32_fbc_inner(l), MutexU32_fbc_data(t, l)), MutexU32_full_borrow_content0(t, l))() {
        open sep(MutexU32_fbc_inner(l), MutexU32_fbc_data(t, l))();
        open MutexU32_fbc_inner(l)(); open MutexU32_fbc_data(t, l)();
        assert (*l).inner |-> ?inner &*& (*l).data |-> ?data;
        close MutexU32_own(t, inner, data);
        close MutexU32_full_borrow_content0(t, l)();
    }{
        produce_lem_ptr_chunk implies(MutexU32_full_borrow_content0(t, l), sep(MutexU32_fbc_inner(l), MutexU32_fbc_data(t, l)))() {
            open MutexU32_full_borrow_content0(t, l)();
            assert (*l).inner |-> ?inner &*& (*l).data |-> ?data;
            open MutexU32_own(t, inner, data);
            close MutexU32_fbc_inner(l)();
            close MutexU32_fbc_data(t, l)();
            close sep(MutexU32_fbc_inner(l), MutexU32_fbc_data(t, l))();
        }{
            full_borrow_implies(k, MutexU32_full_borrow_content0(t, l), sep(MutexU32_fbc_inner(l), MutexU32_fbc_data(t, l)));
        }
        full_borrow_split(k, MutexU32_fbc_inner(l), MutexU32_fbc_data(t, l));
        open_full_borrow_strong(k, MutexU32_fbc_inner(l), q);
        assert exists(?k1);
        produce_lem_ptr_chunk full_borrow_convert_strong(MutexU32_frac_borrow_content(k, t, l), k1, MutexU32_fbc_inner(l))() {
            open MutexU32_frac_borrow_content(k, t, l)();
            assert (*l).inner |-> ?inner;
            SysMutex_renew(inner, True);
            close MutexU32_fbc_inner(l)();
        }{
            open MutexU32_fbc_inner(l)();
            assert (*l).inner |-> ?inner;
            close SysMutex_content(k, t, l)();
            SysMutex_renew(inner, SysMutex_content(k, t, l));
            close MutexU32_frac_borrow_content(k, t, l)();
            close_full_borrow_strong(k1, MutexU32_fbc_inner(l), MutexU32_frac_borrow_content(k, t, l));
            full_borrow_into_frac(k1, MutexU32_frac_borrow_content(k, t, l));
            frac_borrow_mono(k1, k, MutexU32_frac_borrow_content(k, t, l));
            open exists(k1); assert [?qfb]frac_borrow(k, MutexU32_frac_borrow_content(k, t, l));
            close [qfb]exists_np(k);
            lifetime_inclusion_refl(k);
            close [qfb]MutexU32_share(k, t, l);
        }
    }
}
@*/

impl MutexU32 {
    /*    pub fn new(v: u32) -> MutexU32 {
            //@ close SysMutex::new_ghost_arg(True);
            let inner = unsafe { sys::locks::Mutex::new() };
            let data = UnsafeCell::new(v);
            let r = MutexU32 { inner, data };
            //@ close MutexU32_own(_t, r.inner, r.data); // Err: Dereferencing a pointer of type struct sys::locks::Mutex is not yet supported.
            r
        }
    */
    /// The exact behavior on locking a mutex in the thread which already holds
    /// the lock is left unspecified. However, this function will not return on
    /// the second call (it might panic or deadlock, for example).
    pub unsafe fn lock<'a>(&'a self) -> MutexGuardU32 /*<'a>*/
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
            //@ close [qp]MutexU32_frac_borrow_content(k1, t, self)();
            //@ close_frac_borrow(qp, MutexU32_frac_borrow_content(k1, t, self));
            //@ open SysMutex_content(k1, t, self)();
            //@ full_borrow_mono(k1, a, MutexU32_fbc_data(t, self));
            MutexGuardU32::new(self)
        }
    }
}

/*pub*/ struct MutexGuardU32 /*<'a>*/ {
    lock: *const MutexU32,
    //    lock: &'a MutexU32,
}

impl !Send for MutexGuardU32 /*<'_>*/ {}
/*@
pred MutexU32_locked(l: *MutexU32; t: thread_id_t);
lem MutexU32_locked_unwrap(l: *MutexU32, t: thread_id_t);
    req MutexU32_locked(l, t) &*& [?qi](*l).inner |-> ?inner &*& [?qm]SysMutex(inner, ?P);
    ens [qi](*l).inner |-> inner &*& [qm]SysMutex(inner, P) &*& SysMutex_locked(inner, P, t);
lem MutexU32_locked_wrap(l: *MutexU32);
    req [?qi](*l).inner |-> ?inner &*& [?qm]SysMutex(inner, ?P) &*& SysMutex_locked(inner, P, ?t);
    ens [qi](*l).inner |-> inner &*& [qm]SysMutex(inner, P) &*& MutexU32_locked(l, t);

pred_ctor MutexGuardU32_own_mutex(km: lifetime_t, t: thread_id_t, lock: *MutexU32)() =
    [_]MutexU32_share(km, t, lock) &*& MutexU32_locked(lock, t);
pred_ctor MutexGuardU32_own_data(km: lifetime_t, t: thread_id_t, lock: *MutexU32)() =
    full_borrow(km, MutexU32_fbc_data(t, lock));

pred_ctor MutexGuardU32_own(km: lifetime_t)(t: thread_id_t, lock: *MutexU32) =
    [_]MutexU32_share(km, t, lock) &*& MutexU32_locked(lock, t) &*& full_borrow(km, MutexU32_fbc_data(t, lock));

pred_ctor MutexGuardU32_fbc_lock_pto(l: *MutexGuardU32, lock: *MutexU32)() = (*l).lock |-> lock;
pred_ctor MutexGuardU32_fbc_own(km: lifetime_t, t: thread_id_t, lock: *MutexU32)() = MutexGuardU32_own(km)(t, lock);
pred_ctor MutexGuardU32_full_borrow_content0(km: lifetime_t, t: thread_id_t, l: *MutexGuardU32)() =
    (*l).lock |-> ?lock &*& MutexGuardU32_own(km)(t, lock);

pred_ctor MutexGuardU32_share(km: lifetime_t)(k: lifetime_t, t: thread_id_t, l: *MutexGuardU32) = true;

//Todo: proof obligations
@*/

// It is Sync automatically as in our case `T=u32` and `u32:Sync`
//unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}

impl MutexGuardU32 /*<'mutex>*/ {
    /* because MutexGuardU32_own is pred_ctor and not supported yet */
    unsafe fn new<'a>(lock: &'a /*'mutex*/ MutexU32) -> MutexGuardU32 /*<'mutex>*/
    /*@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& [_]MutexU32_share(a, t, lock)
        &*& MutexU32_locked(lock, t) &*& full_borrow(a, MutexU32_fbc_data(t, lock));
    @*/
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& MutexGuardU32_own(a)(t, lock);
    {
        //@ close MutexGuardU32_own(a)(t, lock);
        MutexGuardU32 { lock }
    }

    /*@ //Todo: add primary types `share` predicates in `general.h`
    //pred_ctor u32_frac_borrow_content(t: thread_id_t, l: *u32)(;) = *l |-> ?v;
    //pred u32_share(k: lifetime_t, t: thread_id_t, l: *u32) = frac_borrow(k, u32_frac_borrow_content(t, l));
    //Todo: The trait impl support is not complete yet
    @*/
/*    unsafe fn deref<'a>(&'a self) -> &'a u32
    //@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& exists(?kg) &*& [_]MutexGuardU32_share(kg)(a, t, self);
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& [_]u32_share(a, t, result);
    {
        unsafe { &*(*self.lock).data.get() }
    }*/

    // Todo: deref_mut should be in the implementation of the trait `DerefMut`
    // Todo: deref_mut should not be an `unsafe` function
    unsafe fn deref_mut<'a>(&'a mut self) -> &'a mut u32
    /*@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& exists(?km)
        &*& full_borrow(a, MutexGuardU32_full_borrow_content0(km, t, self))
        &*& lifetime_inclusion(a, km) == true;
        /* Todo: This inclusion must be generated automatically by translator based on reference and referee lifetimes.
           Referee lifetime always outlives reference lifetime out of compiler guarantees of welformedness of types */
    @*/
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& full_borrow(a, u32_full_borrow_content(t, result));
    {
        //@ open_full_borrow_strong(a, MutexGuardU32_full_borrow_content0(km, t, self), qa/2);
        //@ assert exists(?klong);
        //@ open MutexGuardU32_full_borrow_content0(km, t, self)();
        //@ open MutexGuardU32_own(km)(t, ?lock);
        
        // open MutexU32_fbc_data to get ptr provenance info
        //@ lifetime_token_trade(a, qa/2, km);
        //@ assert [?qkm]lifetime_token(km);
        //@ open_full_borrow(qkm, km, MutexU32_fbc_data(t, lock));
        //@ open MutexU32_fbc_data(t, lock)();
        //@ close MutexU32_fbc_data(t, lock)();
        //@ close_full_borrow(MutexU32_fbc_data(t, lock));
        //@ close MutexGuardU32_own(km)(t, lock);
        //@ lifetime_token_trade_back(qkm, km);
        let r = unsafe { &mut *(*self.lock).data.get() };
        /*@ produce_lem_ptr_chunk full_borrow_convert_strong(sep(MutexGuardU32_fbc_lock_pto(self, lock), MutexGuardU32_fbc_own(km, t, lock)), klong,
                MutexGuardU32_full_borrow_content0(km, t, self))()
            {
                open sep(MutexGuardU32_fbc_lock_pto(self, lock), MutexGuardU32_fbc_own(km, t, lock))();
                open MutexGuardU32_fbc_lock_pto(self, lock)();
                open MutexGuardU32_fbc_own(km, t, lock)();
                close MutexGuardU32_full_borrow_content0(km, t, self)();
            }{
                close MutexGuardU32_fbc_lock_pto(self, lock)();
                close MutexGuardU32_fbc_own(km, t, lock)();
                close sep(MutexGuardU32_fbc_lock_pto(self, lock), MutexGuardU32_fbc_own(km, t, lock))();
                close_full_borrow_strong(klong, MutexGuardU32_full_borrow_content0(km, t, self),
                    sep(MutexGuardU32_fbc_lock_pto(self, lock), MutexGuardU32_fbc_own(km, t, lock)));
                full_borrow_mono(klong, a, sep(MutexGuardU32_fbc_lock_pto(self, lock), MutexGuardU32_fbc_own(km, t, lock)));
                full_borrow_split(a, MutexGuardU32_fbc_lock_pto(self, lock), MutexGuardU32_fbc_own(km, t, lock));
            }
        @*/
        /*@
            produce_lem_ptr_chunk implies(MutexGuardU32_fbc_own(km, t, lock),
                sep(MutexGuardU32_own_mutex(km, t, lock), MutexGuardU32_own_data(km, t, lock)))()
            {
                open MutexGuardU32_fbc_own(km, t, lock)();
                open MutexGuardU32_own(km)(t, lock);
                close MutexGuardU32_own_mutex(km, t, lock)();
                close MutexGuardU32_own_data(km, t, lock)();
                close sep(MutexGuardU32_own_mutex(km, t, lock), MutexGuardU32_own_data(km, t, lock))();
                
            }{
                produce_lem_ptr_chunk implies(sep(MutexGuardU32_own_mutex(km, t, lock), MutexGuardU32_own_data(km, t, lock)),
                    MutexGuardU32_fbc_own(km, t, lock))()
                {
                    open sep(MutexGuardU32_own_mutex(km, t, lock), MutexGuardU32_own_data(km, t, lock))();
                    open MutexGuardU32_own_mutex(km, t, lock)(); open MutexGuardU32_own_data(km, t, lock)();
                    close MutexGuardU32_own(km)(t, lock);
                    close MutexGuardU32_fbc_own(km, t, lock)();
                }{
                    full_borrow_implies(a, MutexGuardU32_fbc_own(km, t, lock),
                        sep(MutexGuardU32_own_mutex(km, t, lock), MutexGuardU32_own_data(km, t, lock)));
                    full_borrow_split(a, MutexGuardU32_own_mutex(km, t, lock), MutexGuardU32_own_data(km, t, lock));
                }
            }
        @*/
        /*@
        produce_lem_ptr_chunk implies(MutexGuardU32_own_data(km, t, lock), full_borrow_wrapper(km, MutexU32_fbc_data(t, lock)))() {
            open MutexGuardU32_own_data(km, t, lock)(); close full_borrow_wrapper(km, MutexU32_fbc_data(t, lock))();
        }{
            produce_lem_ptr_chunk implies(full_borrow_wrapper(km, MutexU32_fbc_data(t, lock)), MutexGuardU32_own_data(km, t, lock))() {
                open full_borrow_wrapper(km, MutexU32_fbc_data(t, lock))(); close MutexGuardU32_own_data(km, t, lock)();
            }{
                full_borrow_implies(a, MutexGuardU32_own_data(km, t, lock), full_borrow_wrapper(km, MutexU32_fbc_data(t, lock)));
                full_borrow_unnest(a, km, MutexU32_fbc_data(t, lock));
                lifetime_inclusion_glb(a, a, km);
                full_borrow_mono(lifetime_intersection(a, km), a, MutexU32_fbc_data(t, lock));
            }
        }
        @*/
        /*@
        produce_lem_ptr_chunk implies(MutexU32_fbc_data(t, lock), u32_full_borrow_content(t, &(*lock).data))() {
            open MutexU32_fbc_data(t, lock)(); close u32_full_borrow_content(t, &(*lock).data)();
        }{
            produce_lem_ptr_chunk implies(u32_full_borrow_content(t, &(*lock).data), MutexU32_fbc_data(t, lock))() {
                open u32_full_borrow_content(t, &(*lock).data)(); close MutexU32_fbc_data(t, lock)();
            }{
                full_borrow_implies(a, MutexU32_fbc_data(t, lock), u32_full_borrow_content(t, &(*lock).data));
            }
        }
        @*/
        //@ leak full_borrow(a, MutexGuardU32_fbc_lock_pto(self, lock));
        //@ leak full_borrow(a, MutexGuardU32_own_mutex(km, t, lock));
        r
    }

    unsafe fn drop<'a>(&'a mut self)
    //@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& exists(?km) &*& full_borrow(a, MutexGuardU32_full_borrow_content0(km, t, self)) &*& lifetime_inclusion(a, km) == true;
    //@ ens thread_token(t) &*& [qa]lifetime_token(a);
    {
        //@ open_full_borrow(qa/2, a, MutexGuardU32_full_borrow_content0(km, t, self));
        //@ open MutexGuardU32_full_borrow_content0(km, t, self)();
        //@ open MutexGuardU32_own(km)(t, ?lock);
        //@ open MutexU32_share(km, t, lock);
        //@ assert [_]exists_np(?kfracc);
        //@ lifetime_token_trade(a, qa/2, km);
        //@ assert [?qkm]lifetime_token(km);
        //@ open_frac_borrow(km, MutexU32_frac_borrow_content(kfracc, t, lock), qkm);
        //@ open MutexU32_frac_borrow_content(kfracc, t, lock)();
        // assert false;
        //@ full_borrow_mono(kfracc, km, MutexU32_fbc_data(t, lock));
        //@ close SysMutex_content(kfracc, t, lock)();
        //@ MutexU32_locked_unwrap(lock, t);
        unsafe {
            (*self.lock).inner.unlock();
        }
        //@ close_full_borrow(MutexU32_fbc_data(t, lock));
        //@ close MutexGuardU32_own(km)(t, lock);
        //@ lifetime_token_trade_back(qkm, km);
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
