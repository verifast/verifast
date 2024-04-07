#![feature(negative_impls)]
#![allow(dead_code)]

/*
About the definitions:
    Since to have `MutexU32::lock` verified we need to return the `[qa]lifetime_token(a)` back, we need to close the `frac_borrow` before the method ends.
    To close that `frac_borrow` we need the `SysMutex_share` fraction used to lock the `sys::locks::Mutex` back.
    That means the spec of `sys::locks::Mutex::lock` must return the `SysMutex_share` fraction it receives.
    The latter means neither to have a full chunk of `SysMutex_share` nor a full chunk of `SysMutex` means the mutex is unlocked.
    However, it does not make any problem, because if destroying a locked mutex is an undefined behaviour the implementation of `sys::locks::Mutex::drop`
    just forgets about the mutex.
*/

/*@

pred SysMutex(m: sys::locks::Mutex; P: pred());
pred SysMutex_share(l: *sys::locks::Mutex; P: pred());
lem SysMutex_share_full(l: *sys::locks::Mutex);
    req *l |-> ?m &*& SysMutex(m, ?P);
    ens SysMutex_share(l, P);
lem SysMutex_end_share(l: *sys::locks::Mutex);
   req SysMutex_share(l, ?P);
   ens *l |-> ?m &*& SysMutex(m, P);

pred SysMutex_locked(l: *sys::locks::Mutex, P: pred(); t: thread_id_t);

lem SysMutex_renew(m: sys::locks::Mutex, Q: pred());
    req SysMutex(m, ?P) &*& Q();
    ens SysMutex(m, Q);

/* Justifying the soundness of `SysMutex_renew`:
As mentioned above, with this specification for `sys::locks::Mutex` interface having a full chunk of `SysMutex` or `SysMutex_share`
does not necessarily mean the mutex is not locked. If it was the case the lemma's soundness was easier to justify.
We get `SysMutex(m, ?P)` in the `req` clause so there is not any fraction of `SysMutex(m, P)` or `SysMutex_share(lm, P)` anywhere else.
After applying the lemma the soundness of `sys::locks::Mutex` interface is justified since if:
- The mutex is unlocked and the resource `P()` is protected by mutex; It is in the mutex so to speak. We substitute `P` with `Q`
    and from this point, there will be no `SysMutex`, `SysMutex_share` or `SysMutex_locked` chunk that mentions `P` anywhere.
    It means we leak `P()` and the state is just like after a call to `sys::locks::Mutex::new` to protect `Q()`.

- The mutex is locked, it means there should be a `SysMutex_locked(lm, P, ?t)` and `P()` in resources of some thread(s).
    - `lock` gets verified which is fine because this call never returns. No other thread has `[?q]SysMutex_share(lm, P)`
        to release the mutex.
    - `unlock` cannot get verified with chunks mentioning `P` as there is no `[?q]SysMutex_share(lm, P)` anywhere and verification with
        `SysMutex_locked(lm, Q, ?t)` does not represent a real execution as `lock` never returns.
    - `drop` will get verified and it is sound because `sys::locks::Mutex` implementation of `Drop` does not destroy a locked mutex, but
        simply leaks it. Here `Q()` gets leaked too.
*/

lem SysMutex_share_implies(l: *sys::locks::Mutex, P: pred(), P1: pred());
    req SysMutex_share(l, P) &*& is_implies(?f, P, P1) &*& is_implies(?f1, P1, P);
    ens SysMutex_share(l, P1) &*& is_implies(f, P, P1) &*& is_implies(f1, P1, P);

@*/

mod sys {
    pub mod locks {
        use std::process::abort;
        pub struct Mutex {
            m: *mut u32,
        }

        impl Mutex {
            pub unsafe fn new() -> Mutex
            //@ req exists::<pred()>(?P) &*& P();
            //@ ens SysMutex(result, P);
            {
                abort();
            }

            // TODO: Use `current_thread` var in `SysMutex_locked` like in the `threading.h`. The `SysMutex` interface does not need `thread_token` in the contracts.
            pub unsafe fn lock<'a>(&'a self)
            //@ req thread_token(?t) &*& [?q]SysMutex_share(self, ?P);
            //@ ens thread_token(t) &*& [q]SysMutex_share(self, P) &*& SysMutex_locked(self, P, t) &*& P();
            {
                abort();
            }

            pub unsafe fn unlock<'a>(&'a self)
            //@ req thread_token(?t) &*& SysMutex_locked(self, ?P, t) &*& P() &*& [?q]SysMutex_share(self, P);
            //@ ens thread_token(t) &*& [q]SysMutex_share(self, P);
            {
                abort();
            }

            // TODO: impl Drop for Mutex
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

pub struct MutexU32 {
    inner: sys::locks::Mutex,
    data: UnsafeCell<u32>,
}

/*@

pred True(;) = true;
pred MutexU32_own(t: thread_id_t, inner: sys::locks::Mutex, data: u32) = SysMutex(inner, True);

pred_ctor MutexU32_fbc_inner(l: *MutexU32)(;) = (*l).inner |-> ?inner &*& SysMutex(inner, True) &*& struct_MutexU32_padding(l);

fix t0() -> thread_id_t { default_value }

pred_ctor MutexU32_frac_borrow_content(kfcc: lifetime_t, l: *MutexU32)(;) =
    SysMutex_share(&(*l).inner, full_borrow_(kfcc, u32_full_borrow_content(t0, &(*l).data))) &*& struct_MutexU32_padding(l);

pred MutexU32_share(k: lifetime_t, t: thread_id_t, l: *MutexU32) =
    exists_np(?kfcc) &*& lifetime_inclusion(k, kfcc) == true &*& frac_borrow(k, MutexU32_frac_borrow_content(kfcc, l));

lem MutexU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *MutexU32)
    req lifetime_inclusion(k1, k) == true &*& [_]MutexU32_share(k, t, l);
    ens [_]MutexU32_share(k1, t, l);
{
    open MutexU32_share(k, t, l); assert [_]exists_np(?kfcc);
    frac_borrow_mono(k, k1, MutexU32_frac_borrow_content(kfcc, l));
    assert [?q]frac_borrow(k1, _); close [q]exists_np(kfcc);
    // TODO: Why does VeriFast not just close using any dummy fraction when it is trying to close a dummy fraction?
    lifetime_inclusion_trans(k1, k, kfcc);
    close [q]MutexU32_share(k1, t, l);
}

lem MutexU32_share_full(k: lifetime_t, t: thread_id_t, l: *MutexU32)
    req atomic_mask(Nlft) &*& full_borrow(k, MutexU32_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [_]MutexU32_share(k, t, l) &*& [q]lifetime_token(k);
{

    produce_lem_ptr_chunk implies(sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t0, &(*l).data)), MutexU32_full_borrow_content(t, l))() {
        open sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t0, &(*l).data))();
        open MutexU32_fbc_inner(l)();
        open u32_full_borrow_content(t0, &(*l).data)();
        assert (*l).inner |-> ?inner &*& (*l).data |-> ?data;
        close MutexU32_own(t, inner, data);
        close MutexU32_full_borrow_content(t, l)();
    }{
        produce_lem_ptr_chunk implies(MutexU32_full_borrow_content(t, l), sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t0, &(*l).data)))() {
            open MutexU32_full_borrow_content(t, l)();
            assert (*l).inner |-> ?inner &*& (*l).data |-> ?data;
            open MutexU32_own(t, inner, data);
            close MutexU32_fbc_inner(l)();
            close u32_full_borrow_content(t0, &(*l).data)();
            close sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t0, &(*l).data))();
        }{
            full_borrow_implies(k, MutexU32_full_borrow_content(t, l), sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t0, &(*l).data)));
        }
        full_borrow_split_m(k, MutexU32_fbc_inner(l), u32_full_borrow_content(t0, &(*l).data));
        let kstrong = open_full_borrow_strong_m(k, MutexU32_fbc_inner(l), q);
        produce_lem_ptr_chunk full_borrow_convert_strong(True, MutexU32_frac_borrow_content(k, l), kstrong, MutexU32_fbc_inner(l))() {
            open MutexU32_frac_borrow_content(k, l)();
            SysMutex_end_share(&(*l).inner);
            assert (*l).inner |-> ?inner;
            SysMutex_renew(inner, True);
            close MutexU32_fbc_inner(l)();
        }{
            open MutexU32_fbc_inner(l)();
            assert (*l).inner |-> ?inner;
            close full_borrow_(k, u32_full_borrow_content(t0, &(*l).data))();
            SysMutex_renew(inner, full_borrow_(k, u32_full_borrow_content(t0, &(*l).data)));
            SysMutex_share_full(&(*l).inner);
            close MutexU32_frac_borrow_content(k, l)();
            close_full_borrow_strong_m(kstrong, MutexU32_fbc_inner(l), MutexU32_frac_borrow_content(k, l));
            full_borrow_into_frac_m(kstrong, MutexU32_frac_borrow_content(k, l));
            frac_borrow_mono(kstrong, k, MutexU32_frac_borrow_content(k, l));
            open exists(kstrong); assert [?qfb]frac_borrow(k, MutexU32_frac_borrow_content(k, l));
            close [qfb]exists_np(k);
            lifetime_inclusion_refl(k);
            close [qfb]MutexU32_share(k, t, l);
        }
    }
}

@*/

unsafe impl Send for MutexU32 {}

/*@

lem MutexU32_send(t: thread_id_t, t1: thread_id_t)
    req MutexU32_own(t, ?inner, ?data);
    ens MutexU32_own(t1, inner, data);
{
    open MutexU32_own(t, inner, data);
    close MutexU32_own(t1, inner, data);
}

@*/

unsafe impl Sync for MutexU32 {}

/*@

lem MutexU32_sync(t: thread_id_t, t1: thread_id_t)
    req MutexU32_share(?k, t, ?l);
    ens MutexU32_share(k, t1, l);
{
    open MutexU32_share(k, t, l);
    close MutexU32_share(k, t1, l);
}

@*/

impl MutexU32 {
    pub fn new(v: u32) -> MutexU32 {
        //@ close exists::<pred()>(True);
        let inner = unsafe { sys::locks::Mutex::new() };
        let data = UnsafeCell::new(v);
        let r = MutexU32 { inner, data };
        // TODO: Dereferencing a pointer of type struct sys::locks::Mutex is not yet supported.
        // close MutexU32_own(_t, inner, data); Next line is a workaround
        //@ close MutexU32_own(_t, sys::locks::Mutex { m: inner.m }, data);
        r
    }

    /*
    https://doc.rust-lang.org/std/sync/struct.Mutex.html#method.lock
    "The exact behavior on locking a mutex in the thread which already holds the lock is left unspecified.
    However, this function will not return on the second call (it might panic or deadlock, for example)."
    Note that in either case it is not undefined behaviour.
    */
    // TODO: remove keyword `unsafe`
    pub unsafe fn lock<'a>(&'a self) -> MutexGuardU32
    //@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& [_]MutexU32_share(a, t, self);
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& MutexGuardU32_own(a)(t, result.lock);
    {
        unsafe {
            //@ open MutexU32_share(a, t, self);
            //@ assert [_]exists_np(?klong);
            //@ open_frac_borrow(a, MutexU32_frac_borrow_content(klong, self), qa);
            //@ open MutexU32_frac_borrow_content(klong, self)();
            self.inner.lock();
            //@ assert [?qp]SysMutex_share(&(*self).inner, _);
            //@ close [qp]MutexU32_frac_borrow_content(klong, self)();
            //@ close_frac_borrow(qp, MutexU32_frac_borrow_content(klong, self));
            MutexGuardU32::new(self)
        }
    }
}

/* TODO: MutexGuardU32 should be defined as
pub struct MutexGuardU32<'a> {
    lock: &'a MutexU32,
}
*/
struct MutexGuardU32 {
    lock: *const MutexU32,
}

impl !Send for MutexGuardU32 {}
// unsafe impl<T: ?Sized + Sync> Sync for MutexGuard<'_, T> {}
unsafe impl Sync for MutexGuardU32 {}
/*@
// Proof obligations
lem MutexGuardU32_sync(km: lifetime_t, t: thread_id_t, t1: thread_id_t)
    req MutexGuardU32_share(km)(?k, t, ?l);
    ens MutexGuardU32_share(km)(k, t1, l);
{
    open MutexGuardU32_share(km)(k, t, l);
    close MutexGuardU32_share(km)(k, t1, l);
}
@*/

/*@
// TODO: Is this extra lifetime `klong` necessary here?
pred_ctor MutexGuardU32_own(km: lifetime_t)(t: thread_id_t, lock: *MutexU32) =
    [_]exists_np(?klong) &*& lifetime_inclusion(km, klong) == true &*& [_]frac_borrow(km, MutexU32_frac_borrow_content(klong, lock))
    &*& SysMutex_locked(&(*lock).inner, full_borrow_(klong, u32_full_borrow_content(t0, &(*lock).data)), t)
    &*& full_borrow(klong, u32_full_borrow_content(t0, &(*lock).data));

pred_ctor MutexGuardU32_fbc_rest(km: lifetime_t, klong: lifetime_t, t: thread_id_t, l: *MutexGuardU32, lock: *MutexU32)() =
    (*l).lock |-> lock &*& lifetime_inclusion(km, klong) == true
    &*& [_]frac_borrow(km, MutexU32_frac_borrow_content(klong, lock))
    &*& SysMutex_locked(&(*lock).inner, full_borrow_(klong, u32_full_borrow_content(t0, &(*lock).data)), t);

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
impl MutexGuardU32 {
    unsafe fn new<'a>(lock: &'a MutexU32) -> MutexGuardU32
    /*@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& [_]exists_np(?km) &*& lifetime_inclusion(a, km) == true
        &*& [_]frac_borrow(a, MutexU32_frac_borrow_content(km, lock))
        &*& SysMutex_locked(&(*lock).inner, full_borrow_(km, u32_full_borrow_content(t0, &(*lock).data)), t)
        &*& full_borrow(km, u32_full_borrow_content(t0, &(*lock).data));
    @*/
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& MutexGuardU32_own(a)(t, result.lock);
    {
        //@ close MutexGuardU32_own(a)(t, lock);
        MutexGuardU32 { lock }
    }

    /*
    TODO: deref_mut should be in the implementation of the trait `DerefMut`. Support for the implementation for standard library traits is
    needed for that.
    TODO: deref_mut should be a safe function */
    unsafe fn deref_mut<'a>(&'a mut self) -> &'a mut u32
    /*@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& exists(?km)
        &*& full_borrow(a, MutexGuardU32_full_borrow_content0(km, t, self))
        &*& lifetime_inclusion(a, km) == true;
    /* TODO: This inclusion must be generated automatically by translator based on reference and its target lifetimes.
       The target lifetimes always outlive reference lifetime out of compiler guarantees of wellformedness of types.
    */
    @*/
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& full_borrow(a, u32_full_borrow_content(t, result));
    {
        //@ let kstrong = open_full_borrow_strong(a, MutexGuardU32_full_borrow_content0(km, t, self), qa/2);
        //@ open MutexGuardU32_full_borrow_content0(km, t, self)();
        //@ open MutexGuardU32_own(km)(t, ?lock);

        // We need `(*lock).data |-> _` to get ptr provenance info
        //@ assert [_]exists_np(?kmlong);
        //@ lifetime_inclusion_trans(a, km, kmlong);
        //@ lifetime_token_trade(a, qa/2, kmlong);
        //@ assert [?qkml]lifetime_token(kmlong);
        //@ open_full_borrow(qkml, kmlong, u32_full_borrow_content(t0, &(*lock).data));
        //@ open u32_full_borrow_content(t0, &(*lock).data)();
        //@ integer__limits(&(*lock).data);
        //@ close u32_full_borrow_content(t0, &(*lock).data)();
        //@ close_full_borrow(u32_full_borrow_content(t0, &(*lock).data));
        //@ lifetime_token_trade_back(qkml, kmlong);
        let r = unsafe { &mut *(*self.lock).data.get() };
        /*@
        produce_lem_ptr_chunk full_borrow_convert_strong(True,
            sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_(kmlong, u32_full_borrow_content(t0, &(*lock).data))),
            kstrong,
            MutexGuardU32_full_borrow_content0(km, t, self))() {
                open sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_(kmlong, u32_full_borrow_content(t0, &(*lock).data)))();
                open MutexGuardU32_fbc_rest(km, kmlong, t, self, lock)();
                open full_borrow_(kmlong, u32_full_borrow_content(t0, &(*lock).data))();
                close exists_np(kmlong); leak exists_np(kmlong);
                close MutexGuardU32_own(km)(t, lock);
                close MutexGuardU32_full_borrow_content0(km, t, self)();
            }{
                close MutexGuardU32_fbc_rest(km, kmlong, t, self, lock)();
                close full_borrow_(kmlong, u32_full_borrow_content(t0, &(*lock).data))();
                close sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_(kmlong, u32_full_borrow_content(t0, &(*lock).data)))();
                close_full_borrow_strong(kstrong, MutexGuardU32_full_borrow_content0(km, t, self),
                    sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_(kmlong, u32_full_borrow_content(t0, &(*lock).data))));
                full_borrow_split(kstrong, MutexGuardU32_fbc_rest(km, kmlong, t, self, lock),
                    full_borrow_(kmlong, u32_full_borrow_content(t0, &(*lock).data)));
                full_borrow_unnest(kstrong, kmlong, u32_full_borrow_content(t0, &(*lock).data));
                lifetime_inclusion_glb(a, kstrong, kmlong);
                full_borrow_mono(lifetime_intersection(kstrong, kmlong), a, u32_full_borrow_content(t0, &(*lock).data));
            }
        @*/
        //@ leak full_borrow(kstrong, _);
        /*@
        produce_lem_ptr_chunk implies(u32_full_borrow_content(t0, &(*lock).data), u32_full_borrow_content(t, &(*lock).data))() {
            open u32_full_borrow_content(t0, &(*lock).data)();
            close u32_full_borrow_content(t, &(*lock).data)();
        } {
            produce_lem_ptr_chunk implies(u32_full_borrow_content(t, &(*lock).data), u32_full_borrow_content(t0, &(*lock).data))() {
                open u32_full_borrow_content(t, &(*lock).data)();
                close u32_full_borrow_content(t0, &(*lock).data)();
            } {
                full_borrow_implies(a, u32_full_borrow_content(t0, &(*lock).data), u32_full_borrow_content(t, &(*lock).data));
            }
        }
        @*/
        r
    }

    // TODO: It should be an `impl` of `Drop` and a safe function
    unsafe fn drop<'a>(&'a mut self)
    //@ req thread_token(?t) &*& exists(?km) &*& [?qkm]lifetime_token(km) &*& MutexGuardU32_full_borrow_content0(km, t, self)();
    //@ ens thread_token(t) &*& [qkm]lifetime_token(km) &*& (*self).lock |-> ?lock &*& [_]MutexU32_share(km, t, lock);
    {
        //@ open MutexGuardU32_full_borrow_content0(km, t, self)();
        //@ open MutexGuardU32_own(km)(t, ?lock);
        //@ open [_]exists_np(?kmlong);
        //@ open_frac_borrow(km, MutexU32_frac_borrow_content(kmlong, lock), qkm);
        //@ open MutexU32_frac_borrow_content(kmlong, lock)();
        unsafe {
            (*self.lock).inner.unlock();
        }
        //@ assert [?qp]SysMutex_share(&(*lock).inner, _);
        //@ close_frac_borrow(qp, MutexU32_frac_borrow_content(kmlong, lock));
        //@ assert [?qfrac]frac_borrow(km, _);
        //@ close [qfrac]exists_np(kmlong);
        //@ close [qfrac]MutexU32_share(km, t, lock);
    }
}
