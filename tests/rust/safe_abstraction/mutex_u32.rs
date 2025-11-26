// verifast_options{ignore_unwind_paths ignore_ref_creation extern:../unverified/sys}

#![feature(negative_impls)]
#![allow(dead_code)]

use std::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
};

//@ use sys::locks::*;

pub struct MutexU32 {
    inner: sys::locks::Mutex,
    data: UnsafeCell<u32>,
}

/*@

pred <MutexU32>.own(t, mutexU32) = SysMutex(mutexU32.inner, True);

lem MutexU32_drop()
    req MutexU32_own(?t, ?mutexU32);
    ens sys::locks::Mutex_own(t, mutexU32.inner);
{
    open MutexU32_own(t, mutexU32);
    SysMutex_to_own(t);
}

pred_ctor MutexU32_fbc_inner(l: *MutexU32)(;) = (*l).inner |-> ?inner &*& SysMutex(inner, True) &*& struct_MutexU32_padding(l);

fix t0() -> thread_id_t { default_value }

pred_ctor MutexU32_frac_borrow_content(kfcc: lifetime_t, l: *MutexU32)(;) =
    SysMutex_share(&(*l).inner, full_borrow_(kfcc, u32_full_borrow_content(t0, ref_origin(&(*l).data)))) &*& struct_MutexU32_padding(l);

pred <MutexU32>.share(k, t, l) =
    pointer_within_limits(&(*l).inner) == true &*&
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
    req atomic_mask(MaskTop) &*& full_borrow(k, MutexU32_full_borrow_content(t, l)) &*& [?q]lifetime_token(k) &*& ref_origin(l) == l;
    ens atomic_mask(MaskTop) &*& [_]MutexU32_share(k, t, l) &*& [q]lifetime_token(k);
{

    produce_lem_ptr_chunk implies(sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t0, &(*l).data)), MutexU32_full_borrow_content(t, l))() {
        open sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t0, &(*l).data))();
        open MutexU32_fbc_inner(l)();
        open u32_full_borrow_content(t0, &(*l).data)();
        assert (*l).inner |-> ?inner &*& (*l).data |-> ?data;
        close MutexU32_own(t, MutexU32 { inner, data });
        close MutexU32_full_borrow_content(t, l)();
    }{
        produce_lem_ptr_chunk implies(MutexU32_full_borrow_content(t, l), sep(MutexU32_fbc_inner(l), u32_full_borrow_content(t0, &(*l).data)))() {
            open MutexU32_full_borrow_content(t, l)();
            assert (*l).inner |-> ?inner &*& (*l).data |-> ?data;
            open MutexU32_own(t, MutexU32 { inner, data });
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
            points_to_limits(&(*l).inner);
            close full_borrow_(k, u32_full_borrow_content(t0, ref_origin(&(*l).data)))();
            SysMutex_renew(inner, full_borrow_(k, u32_full_borrow_content(t0, ref_origin(&(*l).data))));
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

lem init_ref_MutexU32(p: *MutexU32)
    req atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]MutexU32_share(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]MutexU32_share(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false);
}

@*/

unsafe impl Send for MutexU32 {}

/*@

lem MutexU32_send(t1: thread_id_t)
    req MutexU32_own(?t, ?mutexU32);
    ens MutexU32_own(t1, mutexU32);
{
    open MutexU32_own(t, mutexU32);
    close MutexU32_own(t1, mutexU32);
}

@*/

unsafe impl Sync for MutexU32 {}

impl MutexU32 {
    pub fn new(v: u32) -> MutexU32 {
        //@ close exists::<pred()>(True);
        let inner = unsafe { sys::locks::Mutex::new() };
        let data = UnsafeCell::new(v);
        let r = MutexU32 { inner, data };
        //@ close MutexU32_own(_t, r);
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
    //@ req thread_token(?t) &*& t == currentThread &*& [?qa]lifetime_token(?a) &*& [_]MutexU32_share(a, t, self);
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& MutexGuardU32_own_(a)(t, result.lock);
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
    req MutexGuardU32_share_(km)(?k, t, ?l);
    ens MutexGuardU32_share_(km)(k, t1, l);
{
    open MutexGuardU32_share_(km)(k, t, l);
    close MutexGuardU32_share_(km)(k, t1, l);
}
@*/

/*@
// TODO: Is this extra lifetime `klong` necessary here?
pred_ctor MutexGuardU32_own_(km: lifetime_t)(t: thread_id_t, lock: *MutexU32) =
    pointer_within_limits(&(*lock).inner) == true &*&
    [_]exists_np(?klong) &*& lifetime_inclusion(km, klong) == true &*& [_]frac_borrow(km, MutexU32_frac_borrow_content(klong, lock))
    &*& SysMutex_locked(&(*lock).inner, full_borrow_(klong, u32_full_borrow_content(t0, ref_origin(&(*lock).data))), t)
    &*& full_borrow(klong, u32_full_borrow_content(t0, ref_origin(&(*lock).data)));

pred_ctor MutexGuardU32_fbc_rest(km: lifetime_t, klong: lifetime_t, t: thread_id_t, l: *MutexGuardU32, lock: *MutexU32)() =
    (*l).lock |-> lock &*& lifetime_inclusion(km, klong) == true
    &*& [_]frac_borrow(km, MutexU32_frac_borrow_content(klong, lock))
    &*& SysMutex_locked(&(*lock).inner, full_borrow_(klong, u32_full_borrow_content(t0, ref_origin(&(*lock).data))), t);

pred_ctor MutexGuardU32_full_borrow_content0(km: lifetime_t, t: thread_id_t, l: *MutexGuardU32)() =
    (*l).lock |-> ?lock &*& MutexGuardU32_own_(km)(t, lock);

pred_ctor MutexGuardU32_share_(km: lifetime_t)(k: lifetime_t, t: thread_id_t, l: *MutexGuardU32) = true;

lem MutexGuardU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *MutexGuardU32)
    req lifetime_inclusion(k1, k) == true &*& exists(?km) &*& [_]MutexGuardU32_share_(km)(k, t, l);
    ens [_]MutexGuardU32_share_(km)(k1, t, l);
{
    close MutexGuardU32_share_(km)(k1, t, l);
    leak MutexGuardU32_share_(km)(k1, t, l);
}

lem MutexGuardU32_full_share(k: lifetime_t, t: thread_id_t, l: *MutexGuardU32)
    req exists(?km) &*& full_borrow(k, MutexGuardU32_full_borrow_content0(km, t, l)) &*& [?q]lifetime_token(k);
    ens [_]MutexGuardU32_share_(km)(k, t, l) &*& [q]lifetime_token(k);
{
    leak full_borrow(_, _);
    close MutexGuardU32_share_(km)(k, t, l);
    leak MutexGuardU32_share_(km)(k, t, l);
}
@*/
impl MutexGuardU32 {
    unsafe fn new<'a>(lock: &'a MutexU32) -> MutexGuardU32
    /*@ req thread_token(?t) &*& [_]exists_np(?km)
        &*& [_]frac_borrow(?a, MutexU32_frac_borrow_content(km, lock)) &*& [?qa]lifetime_token(a)
        &*& lifetime_inclusion(a, km) == true
        &*& pointer_within_limits(&(*lock).inner) == true
        &*& SysMutex_locked(&(*lock).inner, full_borrow_(km, u32_full_borrow_content(t0, ref_origin(&(*lock).data))), t)
        &*& full_borrow(km, u32_full_borrow_content(t0, ref_origin(&(*lock).data)));
    @*/
    //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& MutexGuardU32_own_(a)(t, result.lock);
    {
        //@ close MutexGuardU32_own_(a)(t, lock);
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
        //@ open MutexGuardU32_own_(km)(t, ?lock);

        // We need `(*lock).data |-> _` to get ptr provenance info
        //@ assert [_]exists_np(?kmlong);
        //@ lifetime_inclusion_trans(a, km, kmlong);
        //@ lifetime_token_trade(a, qa/2, kmlong);
        //@ assert [?qkml]lifetime_token(kmlong);
        //@ open_full_borrow(qkml, kmlong, u32_full_borrow_content(t0, ref_origin(&(*lock).data)));
        //@ open u32_full_borrow_content(t0, ref_origin(&(*lock).data))();
        //@ points_to_limits(ref_origin(&(*lock).data));
        //@ close u32_full_borrow_content(t0, ref_origin(&(*lock).data))();
        //@ close_full_borrow(u32_full_borrow_content(t0, ref_origin(&(*lock).data)));
        //@ lifetime_token_trade_back(qkml, kmlong);
        let r = unsafe { &mut *(*self.lock).data.get() };
        /*@
        produce_lem_ptr_chunk full_borrow_convert_strong(True,
            sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_(kmlong, u32_full_borrow_content(t0, ref_origin(&(*lock).data)))),
            kstrong,
            MutexGuardU32_full_borrow_content0(km, t, self))() {
                open sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_(kmlong, u32_full_borrow_content(t0, ref_origin(&(*lock).data))))();
                open MutexGuardU32_fbc_rest(km, kmlong, t, self, lock)();
                open full_borrow_(kmlong, u32_full_borrow_content(t0, ref_origin(&(*lock).data)))();
                close exists_np(kmlong); leak exists_np(kmlong);
                close MutexGuardU32_own_(km)(t, lock);
                close MutexGuardU32_full_borrow_content0(km, t, self)();
            }{
                close MutexGuardU32_fbc_rest(km, kmlong, t, self, lock)();
                close full_borrow_(kmlong, u32_full_borrow_content(t0, ref_origin(&(*lock).data)))();
                close sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_(kmlong, u32_full_borrow_content(t0, ref_origin(&(*lock).data))))();
                close_full_borrow_strong(kstrong, MutexGuardU32_full_borrow_content0(km, t, self),
                    sep(MutexGuardU32_fbc_rest(km, kmlong, t, self, lock), full_borrow_(kmlong, u32_full_borrow_content(t0, ref_origin(&(*lock).data)))));
                full_borrow_split(kstrong, MutexGuardU32_fbc_rest(km, kmlong, t, self, lock),
                    full_borrow_(kmlong, u32_full_borrow_content(t0, ref_origin(&(*lock).data))));
                full_borrow_unnest(kstrong, kmlong, u32_full_borrow_content(t0, ref_origin(&(*lock).data)));
                lifetime_inclusion_glb(a, kstrong, kmlong);
                full_borrow_mono(lifetime_intersection(kstrong, kmlong), a, u32_full_borrow_content(t0, ref_origin(&(*lock).data)));
            }
        @*/
        //@ leak full_borrow(kstrong, _);
        /*@
        produce_lem_ptr_chunk implies(u32_full_borrow_content(t0, ref_origin(&(*lock).data)), u32_full_borrow_content(t, ref_origin(&(*lock).data)))() {
            open u32_full_borrow_content(t0, ref_origin(&(*lock).data))();
            close u32_full_borrow_content(t, ref_origin(&(*lock).data))();
        } {
            produce_lem_ptr_chunk implies(u32_full_borrow_content(t, ref_origin(&(*lock).data)), u32_full_borrow_content(t0, ref_origin(&(*lock).data)))() {
                open u32_full_borrow_content(t, ref_origin(&(*lock).data))();
                close u32_full_borrow_content(t0, ref_origin(&(*lock).data))();
            } {
                full_borrow_implies(a, u32_full_borrow_content(t0, ref_origin(&(*lock).data)), u32_full_borrow_content(t, ref_origin(&(*lock).data)));
            }
        }
        @*/
        r
    }

    // TODO: It should be an `impl` of `Drop` and a safe function
    unsafe fn drop<'a>(&'a mut self)
    //@ req thread_token(?t) &*& t == currentThread &*& exists(?km) &*& [?qkm]lifetime_token(km) &*& MutexGuardU32_full_borrow_content0(km, t, self)();
    //@ ens thread_token(t) &*& [qkm]lifetime_token(km) &*& (*self).lock |-> ?lock &*& [_]MutexU32_share(km, t, lock);
    {
        //@ open MutexGuardU32_full_borrow_content0(km, t, self)();
        //@ open MutexGuardU32_own_(km)(t, ?lock);
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
