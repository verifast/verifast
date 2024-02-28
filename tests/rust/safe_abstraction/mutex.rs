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
        pred SysMutex_share(l: *sys::locks::Mutex; P: pred());
        lem SysMutex_share_full(l: *sys::locks::Mutex);
            req *l |-> ?m &*& SysMutex(m, ?P);
            ens SysMutex_share(l, P);
        lem SysMutex_end_share(l: *sys::locks::Mutex);
           req SysMutex_share(l, ?P);
           ens *l |-> ?m &*& SysMutex(m, P);

        pred SysMutex::new_ghost_arg(P: pred()) = true;
        pred SysMutex_locked(l: *sys::locks::Mutex, P: pred(); t: thread_id_t);
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
                   - `drop` will get verified and it is sound because `sys::locks::Mutex` implementation simply leaks a locked mutex.
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
            //@ req thread_token(?t) &*& [?q]SysMutex_share(self, ?P);
            //@ ens thread_token(t) &*& [q]SysMutex_share(self, P) &*& SysMutex_locked(self, P, t) &*& P();
            {
                abort();
            }

            pub unsafe fn unlock<'a>(&'a self)
            //@ req thread_token(?t) &*& SysMutex_locked(self, ?P, t) &*& P();
            //@ ens thread_token(t);
            {
                abort();
            }

            // Todo: impl Drop for Mutex
            unsafe fn drop<'a>(&'a mut self)
            //@ req (*self) |-> ?m &*& SysMutex(m, _);
            //@ ens (*self) |-> m;
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

// Todo: MutexU32 should be public type
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

pred_ctor MutexU32_frac_borrow_content(kfcc: lifetime_t, t: thread_id_t, l: *MutexU32)(;) =
     SysMutex_share(&(*l).inner, full_borrow_wrapper(kfcc, u32_full_borrow_content(t, &(*l).data)));

pred MutexU32_share(k: lifetime_t, t: thread_id_t, l: *MutexU32) =
    exists_np(?kfcc) &*& lifetime_inclusion(k, kfcc) == true &*& frac_borrow(k, MutexU32_frac_borrow_content(kfcc, t, l));

lem MutexU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *MutexU32)
    req lifetime_inclusion(k1, k) == true &*& [_]MutexU32_share(k, t, l);
    ens [_]MutexU32_share(k1, t, l);
{
    open MutexU32_share(k, t, l); assert [_]exists_np(?kfcc);
    frac_borrow_mono(k, k1, MutexU32_frac_borrow_content(kfcc, t, l));
    assert [?q]frac_borrow(k1, _); close [q]exists_np(kfcc);
    // Todo: Why does VeriFast not just close using any dummy fraction when it is trying to close a dummy fraction?
    lifetime_inclusion_trans(k1, k, kfcc);
    close [q]MutexU32_share(k1, t, l);
}

lem MutexU32_share_full(k: lifetime_t, t: thread_id_t, l: *MutexU32)
    req full_borrow(k, MutexU32_full_borrow_content0(t, l)) &*& [?q]lifetime_token(k);
    ens [_]MutexU32_share(k, t, l) &*& [q]lifetime_token(k);
{

    produce_lem_ptr_chunk implies(sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t, &(*l).data)), MutexU32_full_borrow_content0(t, l))() {
        open sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t, &(*l).data))();
        open MutexU32_fbc_inner(l)(); open u32_full_borrow_content(t, &(*l).data)();
        assert (*l).inner |-> ?inner &*& (*l).data |-> ?data;
        close MutexU32_own(t, inner, data);
        close MutexU32_full_borrow_content0(t, l)();
    }{
        produce_lem_ptr_chunk implies(MutexU32_full_borrow_content0(t, l), sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t, &(*l).data)))() {
            open MutexU32_full_borrow_content0(t, l)();
            assert (*l).inner |-> ?inner &*& (*l).data |-> ?data;
            open MutexU32_own(t, inner, data);
            close MutexU32_fbc_inner(l)();
            close u32_full_borrow_content(t, &(*l).data)();
            close sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t, &(*l).data))();
        }{
            full_borrow_implies(k, MutexU32_full_borrow_content0(t, l), sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t, &(*l).data)));
        }
        full_borrow_split(k, MutexU32_fbc_inner(l), u32_full_borrow_content(t, &(*l).data));
        open_full_borrow_strong(k, MutexU32_fbc_inner(l), q);
        assert exists(?kstrong);
        produce_lem_ptr_chunk full_borrow_convert_strong(MutexU32_frac_borrow_content(k, t, l), kstrong, MutexU32_fbc_inner(l))() {
            open MutexU32_frac_borrow_content(k, t, l)();
            SysMutex_end_share(&(*l).inner);
            assert (*l).inner |-> ?inner;
            SysMutex_renew(inner, True);
            close MutexU32_fbc_inner(l)();
        }{
            open MutexU32_fbc_inner(l)();
            assert (*l).inner |-> ?inner;
            close full_borrow_wrapper(k, u32_full_borrow_content(t, &(*l).data))();
            SysMutex_renew(inner, full_borrow_wrapper(k, u32_full_borrow_content(t, &(*l).data)));
            SysMutex_share_full(&(*l).inner);
            close MutexU32_frac_borrow_content(k, t, l)();
            close_full_borrow_strong(kstrong, MutexU32_fbc_inner(l), MutexU32_frac_borrow_content(k, t, l));
            full_borrow_into_frac(kstrong, MutexU32_frac_borrow_content(k, t, l));
            frac_borrow_mono(kstrong, k, MutexU32_frac_borrow_content(k, t, l));
            open exists(kstrong); assert [?qfb]frac_borrow(k, MutexU32_frac_borrow_content(k, t, l));
            close [qfb]exists_np(k);
            lifetime_inclusion_refl(k);
            close [qfb]MutexU32_share(k, t, l);
        }
    }
}
@*/

impl MutexU32 {
    /*
        pub fn new(v: u32) -> MutexU32 {
            //@ close SysMutex::new_ghost_arg(True);
            let inner = unsafe { sys::locks::Mutex::new() };
            let data = UnsafeCell::new(v);
            let r = MutexU32 { inner, data };
            // Todo: Dereferencing a pointer of type struct sys::locks::Mutex is not yet supported.
            //@ close MutexU32_own(_t, inner, data);
            r
        }
    */
    /*
    https://doc.rust-lang.org/std/sync/struct.Mutex.html#method.lock
    "The exact behavior on locking a mutex in the thread which already holds the lock is left unspecified.
    However, this function will not return on the second call (it might panic or deadlock, for example)."
    Note that in either case it is not undefined behaviour.
    */
    // Todo: should be safe
    pub unsafe fn lock<'a>(&'a self) -> MutexGuardU32
//@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& [_]MutexU32_share(a, t, self);
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& MutexGuardU32_own(a)(t, self);
    {
        unsafe {
            //@ open MutexU32_share(a, t, self);
            //@ assert [_]exists_np(?klong);
            //@ open_frac_borrow(a, MutexU32_frac_borrow_content(klong, t, self), qa);
            //@ open MutexU32_frac_borrow_content(klong, t, self)();
            self.inner.lock();
            //@ assert [?qp]SysMutex_share(&(*self).inner, _);
            //@ close [qp]MutexU32_frac_borrow_content(klong, t, self)();
            //@ close_frac_borrow(qp, MutexU32_frac_borrow_content(klong, t, self));
            MutexGuardU32::new(self)
        }
    }
}

/* Todo: MutexGuardU32 should be defined as
pub struct MutexGuardU32<'a> {
    lock: &'a MutexU32,
}
*/
struct MutexGuardU32 {
    lock: *const MutexU32,
}

impl !Send for MutexGuardU32 {}
// It is Sync automatically as in our case `T=u32` and `u32:Sync`
// unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}
/*@
// Todo: Is this extra lifetime `klong` necessary here?
pred_ctor MutexGuardU32_own(km: lifetime_t)(t: thread_id_t, lock: *MutexU32) =
    [_]exists_np(?klong) &*& lifetime_inclusion(km, klong) == true &*& [_]frac_borrow(km, MutexU32_frac_borrow_content(klong, t, lock))
    &*& SysMutex_locked(&(*lock).inner, full_borrow_wrapper(klong, u32_full_borrow_content(t, &(*lock).data)), t)
    &*& full_borrow(klong, u32_full_borrow_content(t, &(*lock).data));

pred_ctor MutexGuardU32_fbc_rest(km: lifetime_t, klong: lifetime_t, t: thread_id_t, l: *MutexGuardU32, lock: *MutexU32)() =
    (*l).lock |-> lock &*& lifetime_inclusion(km, klong) == true
    &*& [_]frac_borrow(km, MutexU32_frac_borrow_content(klong, t, lock))
    &*& SysMutex_locked(&(*lock).inner, full_borrow_wrapper(klong, u32_full_borrow_content(t, &(*lock).data)), t);

pred_ctor MutexGuardU32_full_borrow_content0(km: lifetime_t, t: thread_id_t, l: *MutexGuardU32)() =
    (*l).lock |-> ?lock &*& MutexGuardU32_own(km)(t, lock);

pred_ctor MutexGuardU32_share(km: lifetime_t)(k: lifetime_t, t: thread_id_t, l: *MutexGuardU32) = true;

lem MutexGuardU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *MutexGuardU32)
    req lifetime_inclusion(k1, k) == true &*& exists(?km) &*& [_]MutexGuardU32_share(km)(k, t, l);
    ens [_]MutexGuardU32_share(km)(k1, t, l);
{
    close MutexGuardU32_share(km)(k1, t, l);
    leak MutexGuardU32_share(km)(k1, t, l);
}

lem MutexGuardU32_full_share(k: lifetime_t, t: thread_id_t, l: *MutexGuardU32)
    req exists(?km) &*& full_borrow(k, MutexGuardU32_full_borrow_content0(km, t, l)) &*& [?q]lifetime_token(k);
    ens [_]MutexGuardU32_share(km)(k, t, l) &*& [q]lifetime_token(k);
{
    leak full_borrow(_, _);
    close MutexGuardU32_share(km)(k, t, l);
    leak MutexGuardU32_share(km)(k, t, l);
}
@*/
/*@
lem MutexU32_data_ptr_prov(l: *MutexU32);
    req (*l).data |-> ?v;
    ens (*l).data |-> v;
@*/
impl MutexGuardU32 {
    unsafe fn new<'a>(lock: &'a MutexU32) -> MutexGuardU32
/*@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& [_]exists_np(?km) &*& lifetime_inclusion(a, km) == true
    &*& [_]frac_borrow(a, MutexU32_frac_borrow_content(km, t, lock))
    &*& SysMutex_locked(&(*lock).inner, full_borrow_wrapper(km, u32_full_borrow_content(t, &(*lock).data)), t)
    &*& full_borrow(km, u32_full_borrow_content(t, &(*lock).data));
    @*/
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& MutexGuardU32_own(a)(t, lock);
    {
        //@ close MutexGuardU32_own(a)(t, lock);
        MutexGuardU32 { lock }
    }

    /*
    Todo: deref_mut should be in the implementation of the trait `DerefMut`. Support for the implementation for standard library traits is
    needed for that.
    Todo: deref_mut should be a safe function */
    unsafe fn deref_mut<'a>(&'a mut self) -> &'a mut u32
    /*@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& exists(?km)
        &*& full_borrow(a, MutexGuardU32_full_borrow_content0(km, t, self))
        &*& lifetime_inclusion(a, km) == true;
    /* Todo: This inclusion must be generated automatically by translator based on reference and its target lifetimes.
       The target lifetimes always outlive reference lifetime out of compiler guarantees of wellformedness of types.
    */
    @*/
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& full_borrow(a, u32_full_borrow_content(t, result));
    {
        //@ open_full_borrow_strong(a, MutexGuardU32_full_borrow_content0(km, t, self), qa/2);
        //@ assert exists(?kstrong);
        //@ open MutexGuardU32_full_borrow_content0(km, t, self)();
        //@ open MutexGuardU32_own(km)(t, ?lock);

        // We need `(*lock).data |-> _` to get ptr provenance info
        //@ assert [_]exists_np(?kmlong);
        //@ lifetime_inclusion_trans(a, km, kmlong);
        //@ lifetime_token_trade(a, qa/2, kmlong);
        //@ assert [?qkml]lifetime_token(kmlong);
        //@ open_full_borrow(qkml, kmlong, u32_full_borrow_content(t, &(*lock).data));
        //@ open u32_full_borrow_content(t, &(*lock).data)();
        // Todo: Is it possible to not need the following call
        //@ MutexU32_data_ptr_prov(lock);
        //@ close u32_full_borrow_content(t, &(*lock).data)();
        //@ close_full_borrow(u32_full_borrow_content(t, &(*lock).data));
        //@ lifetime_token_trade_back(qkml, kmlong);
        let r = unsafe { &mut *(*self.lock).data.get() };
        /*@
        produce_lem_ptr_chunk full_borrow_convert_strong(
            sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_wrapper(kmlong, u32_full_borrow_content(t, &(*lock).data))),
            kstrong,
            MutexGuardU32_full_borrow_content0(km, t, self))() {
                open sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_wrapper(kmlong, u32_full_borrow_content(t, &(*lock).data)))();
                open MutexGuardU32_fbc_rest(km, kmlong, t, self, lock)();
                open full_borrow_wrapper(kmlong, u32_full_borrow_content(t, &(*lock).data))();
                close exists_np(kmlong); leak exists_np(kmlong);
                close MutexGuardU32_own(km)(t, lock);
                close MutexGuardU32_full_borrow_content0(km, t, self)();
            }{
                close MutexGuardU32_fbc_rest(km, kmlong, t, self, lock)();
                close full_borrow_wrapper(kmlong, u32_full_borrow_content(t, &(*lock).data))();
                close sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_wrapper(kmlong, u32_full_borrow_content(t, &(*lock).data)))();
                close_full_borrow_strong(kstrong, MutexGuardU32_full_borrow_content0(km, t, self),
                    sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_wrapper(kmlong, u32_full_borrow_content(t, &(*lock).data))));
                full_borrow_split(kstrong, MutexGuardU32_fbc_rest(km, kmlong, t, self, lock),
                    full_borrow_wrapper(kmlong, u32_full_borrow_content(t, &(*lock).data)));
                full_borrow_unnest(kstrong, kmlong, u32_full_borrow_content(t, &(*lock).data));
                lifetime_inclusion_glb(a, kstrong, kmlong);
                full_borrow_mono(lifetime_intersection(kstrong, kmlong), a, u32_full_borrow_content(t, &(*lock).data));
            }
        @*/
        //@ leak full_borrow(kstrong, _);
        r
    }
    /* Todo: Since the single parameter of `drop` is a mutable reference, when we open the full borrow and destroy the meaning of `[[T]].OWN`
    we will not be able to close borrow again. It is fine because the value is getting dropped and will not get used after our borrow lifetime ends.
    However, to get our lifetime back we need to close the borrow wich after destroying the `Own` predicate is not always possible.
    One way to handle this is to generate a different contract for `drop` implementations which does not return the lifetime token corresponding to lifetime
    of the mutable reference. It will represent the fact that we know for this special case, i.e. `drop` this external lifetime will immediately end
    after this function call and the original value will not be used afterward too.
    */
    // Todo: It should be an `impl` of `Drop` and a safe function
    unsafe fn drop<'a>(&'a mut self)
    /*@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& exists(?km)
        &*& full_borrow(a, MutexGuardU32_full_borrow_content0(km, t, self)) &*& lifetime_inclusion(a, km) == true;
    @*/
    //@ ens thread_token(t) /* &*& [qa]lifetime_token(a) */; // read the comment above
    {
        //@ open_full_borrow(qa/2, a, MutexGuardU32_full_borrow_content0(km, t, self));
        //@ open MutexGuardU32_full_borrow_content0(km, t, self)();
        //@ open MutexGuardU32_own(km)(t, ?lock);
        //@ assert [_]exists_np(?kmlong);
        //@ lifetime_token_trade(a, qa/2, km);
        //@ assert [?qkm]lifetime_token(km);
        //@ open_frac_borrow(km, MutexU32_frac_borrow_content(kmlong, t, lock), qkm);
        //@ open MutexU32_frac_borrow_content(kmlong, t, lock)();
        unsafe {
            (*self.lock).inner.unlock();
        }
        //@ assert [?qp]SysMutex_share(&(*lock).inner, _);
        //@ close [qp]MutexU32_frac_borrow_content(kmlong, t, lock)();
        //@ close_frac_borrow(qp, MutexU32_frac_borrow_content(kmlong, t, lock));
        //@ lifetime_token_trade_back(qkm, km);
        //@ leak (*self).lock |-> _;
        //@ leak close_full_borrow_token(_, _, _);
        //@ leak [_]lifetime_token(a);
    }
}
// /*
// impl MutexU32 {
//     pub fn new(v: u32) -> MutexU32 {
//         MutexU32 {
//             inner: unsafe { sys::locks::Mutex::new() },
//             data: UnsafeCell::new(v),
//         }
//     }

//     pub fn lock<'a>(&'a self) -> MutexGuardU32/*<'a>*/ {
//         unsafe {
//             self.inner.lock();
//             MutexGuardU32::new(self)
//         }
//     }

//     pub fn unlock<'a>(guard: MutexGuardU32/*<'a>*/) {
//         drop(guard);
//     }
// }
// */
// /*
// impl MutexU32 {
//     pub fn new(v: u32) -> MutexU32 {
//         MutexU32 {
//             inner: sys::locks::Mutex::new(),
//             data: UnsafeCell::new(v),
//         }
//     }

//     pub fn lock<'a>(&'a self) -> MutexGuardU32<'a> {
//         unsafe {
//             self.inner.lock();
//             MutexGuardU32::new(self)
//         }
//     }

//     pub fn unlock<'a>(guard: MutexGuardU32<'a>) {
//         drop(guard);
//     }
// }

// impl<'mutex> MutexGuardU32<'mutex> {
//     unsafe fn new(lock: &'mutex MutexU32) -> MutexGuardU32<'mutex> {
//         MutexGuardU32 { lock }
//     }
// }

// impl Deref for MutexGuardU32<'_> {
//     type Target = u32;
//     fn deref<'a>(&'a self) -> &'a u32 {
//         unsafe { &*self.lock.data.get() }
//     }
// }

// impl DerefMut for MutexGuardU32<'_> {
//     fn deref_mut<'a>(&'a mut self) -> &'a mut u32 {
//         unsafe { &mut *self.lock.data.get() }
//     }
// }

// impl Drop for MutexGuardU32<'_> {
//     fn drop<'a>(&'a mut self) {
//         unsafe {
//             self.lock.inner.unlock();
//         }
//     }
// }
// */
