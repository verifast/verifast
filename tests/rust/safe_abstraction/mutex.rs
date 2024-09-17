#![feature(negative_impls)]
#![allow(dead_code)]

use std::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
};

pub struct Mutex<T: Send> {
    inner: sys::locks::Mutex,
    data: UnsafeCell<T>,
}

/*@

pred True(;) = true;
pred Mutex_own<T>(t: thread_id_t, inner: sys::locks::Mutex, data: T) =
    sys::locks::SysMutex(inner, True) &*& <T>.own(t, data);

pred_ctor Mutex_fbc_inner<T>(l: *Mutex<T>)(;) = (*l).inner |-> ?inner &*& sys::locks::SysMutex(inner, True) &*& struct_Mutex_padding(l);

fix t0() -> thread_id_t { default_value }

pred_ctor Mutex_frac_borrow_content<T>(kfcc: lifetime_t, l: *Mutex<T>)(;) =
    sys::locks::SysMutex_share(&(*l).inner, full_borrow_(kfcc, <T>.full_borrow_content(t0, &(*l).data))) &*& struct_Mutex_padding(l);

pred Mutex_share<T>(k: lifetime_t, t: thread_id_t, l: *Mutex<T>) =
    exists_np(?kfcc) &*& lifetime_inclusion(k, kfcc) == true &*& frac_borrow(k, Mutex_frac_borrow_content::<T>(kfcc, l));

lem Mutex_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Mutex<T>)
    req lifetime_inclusion(k1, k) == true &*& [_]Mutex_share(k, t, l);
    ens [_]Mutex_share(k1, t, l);
{
    open Mutex_share(k, t, l);
    assert [_]exists_np(?kfcc);
    frac_borrow_mono(k, k1, Mutex_frac_borrow_content(kfcc, l));
    assert [?q]frac_borrow(k1, _);
    close [q]exists_np(kfcc);
    // TODO: Why does VeriFast not just close using any dummy fraction when it is trying to close a dummy fraction?
    lifetime_inclusion_trans(k1, k, kfcc);
    close [q]Mutex_share(k1, t, l);
}

lem Mutex_share_full<T>(k: lifetime_t, t: thread_id_t, l: *Mutex<T>)
    req is_Send(typeid(T)) == true &*& type_interp::<T>() &*& atomic_mask(Nlft) &*& full_borrow(k, Mutex_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [_]Mutex_share(k, t, l) &*& [q]lifetime_token(k);
{
    produce_lem_ptr_chunk implies(sep(Mutex_fbc_inner(l), <T>.full_borrow_content(t0, &(*l).data)), Mutex_full_borrow_content(t, l))() {
        open sep(Mutex_fbc_inner(l), <T>.full_borrow_content(t0, &(*l).data))();
        open Mutex_fbc_inner::<T>(l)();
        open_full_borrow_content::<T>(t0, &(*l).data);
        close Mutex_data(l, _);
        assert (*l).inner |-> ?inner &*& (*l).data |-> ?data;
        ghost_rec_perm_top_weaken(type_depth(typeid(T)));
        Send::send(t0, t, data);
        ghost_rec_perm_top_unweaken();
        close Mutex_own(t, inner, data);
        close Mutex_full_borrow_content::<T>(t, l)();
    }{
        produce_lem_ptr_chunk implies(Mutex_full_borrow_content(t, l), sep(Mutex_fbc_inner(l), <T>.full_borrow_content(t0, &(*l).data)))() {
            open Mutex_full_borrow_content::<T>(t, l)();
            assert (*l).inner |-> ?inner &*& (*l).data |-> ?data;
            open Mutex_own(t, inner, data);
            close Mutex_fbc_inner::<T>(l)();
            open Mutex_data(l, _);
            ghost_rec_perm_top_weaken(type_depth(typeid(T)));
            Send::send(t, t0, data);
            ghost_rec_perm_top_unweaken();
            close_full_borrow_content::<T>(t0, &(*l).data);
            close sep(Mutex_fbc_inner(l), <T>.full_borrow_content(t0, &(*l).data))();
        }{
            full_borrow_implies(k, Mutex_full_borrow_content(t, l), sep(Mutex_fbc_inner(l), <T>.full_borrow_content(t0, &(*l).data)));
        }
        full_borrow_split_m(k, Mutex_fbc_inner(l), <T>.full_borrow_content(t0, &(*l).data));
        let kstrong = open_full_borrow_strong_m(k, Mutex_fbc_inner(l), q);
        produce_lem_ptr_chunk full_borrow_convert_strong(True, Mutex_frac_borrow_content(k, l), kstrong, Mutex_fbc_inner(l))() {
            open Mutex_frac_borrow_content::<T>(k, l)();
            sys::locks::SysMutex_end_share(&(*l).inner);
            assert (*l).inner |-> ?inner;
            sys::locks::SysMutex_renew(inner, True);
            close Mutex_fbc_inner::<T>(l)();
        }{
            open Mutex_fbc_inner::<T>(l)();
            assert (*l).inner |-> ?inner;
            close full_borrow_(k, <T>.full_borrow_content(t0, &(*l).data))();
            sys::locks::SysMutex_renew(inner, full_borrow_(k, <T>.full_borrow_content(t0, &(*l).data)));
            sys::locks::SysMutex_share_full(&(*l).inner);
            close Mutex_frac_borrow_content::<T>(k, l)();
            close_full_borrow_strong_m(kstrong, Mutex_fbc_inner(l), Mutex_frac_borrow_content(k, l));
            full_borrow_into_frac_m(kstrong, Mutex_frac_borrow_content(k, l));
            frac_borrow_mono(kstrong, k, Mutex_frac_borrow_content(k, l));
            open exists(kstrong);
            assert [?qfb]frac_borrow(k, Mutex_frac_borrow_content(k, l));
            close [qfb]exists_np(k);
            lifetime_inclusion_refl(k);
            close [qfb]Mutex_share(k, t, l);
        }
    }
}

@*/

unsafe impl<T: Send> Send for Mutex<T> {}

/*@

lem Mutex_send<T>(t: thread_id_t, t1: thread_id_t) // TODO: Enforce this proof obligation
    req is_Send(typeid(T)) == true &*& type_interp::<T>() &*& Mutex_own::<T>(t, ?inner, ?data);
    ens type_interp::<T>() &*& Mutex_own(t1, inner, data);
{
    open Mutex_own(t, inner, data);
    Send::send::<T>(t, t1, data);
    close Mutex_own(t1, inner, data);
}

@*/

unsafe impl<T: Send> Sync for Mutex<T> {}

/*@

lem Mutex_sync<T>(t: thread_id_t, t1: thread_id_t) // TODO: Enforce this proof obligation
    req Mutex_share::<T>(?k, t, ?l);
    ens Mutex_share(k, t1, l);
{
    open Mutex_share(k, t, l);
    close Mutex_share(k, t1, l);
}

@*/

pub struct MutexGuard<'a, T: Send> {
    lock: &'a Mutex<T>,
}

/*@

// TODO: Is this extra lifetime `klong` necessary here?
pred MutexGuard_own<'a, T>(t: thread_id_t, lock: *Mutex<T>) =
    [_]exists_np(?klong) &*& lifetime_inclusion('a, klong) == true &*& [_]frac_borrow('a, Mutex_frac_borrow_content(klong, lock))
    &*& sys::locks::SysMutex_locked(&(*lock).inner, full_borrow_(klong, <T>.full_borrow_content(t0, &(*lock).data)), t)
    &*& full_borrow(klong, <T>.full_borrow_content(t0, &(*lock).data));

pred_ctor MutexGuard_fbc_rest<'a, T>(klong: lifetime_t, t: thread_id_t, l: *MutexGuard<'a, T>, lock: *Mutex<T>)() =
    (*l).lock |-> lock &*& lifetime_inclusion('a, klong) == true &*& struct_MutexGuard_padding(l)
    &*& [_]frac_borrow('a, Mutex_frac_borrow_content(klong, lock))
    &*& sys::locks::SysMutex_locked(&(*lock).inner, full_borrow_(klong, <T>.full_borrow_content(t0, &(*lock).data)), t);

pred MutexGuard_share<'a, T>(k: lifetime_t, t: thread_id_t, l: *MutexGuard<'a, T>) = true;

lem MutexGuard_share_mono<'a, T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *MutexGuard<'a, T>)
    req lifetime_inclusion(k1, k) == true &*& [_]MutexGuard_share::<'a, T>(k, t, l);
    ens [_]MutexGuard_share::<'a, T>(k1, t, l);
{
    close MutexGuard_share::<'a, T>(k1, t, l);
    leak MutexGuard_share::<'a, T>(k1, t, l);
}

lem MutexGuard_share_full<'a, T>(k: lifetime_t, t: thread_id_t, l: *MutexGuard<'a, T>)
    req full_borrow(k, MutexGuard_full_borrow_content::<'a, T>(t, l)) &*& [?q]lifetime_token(k);
    ens [_]MutexGuard_share::<'a, T>(k, t, l) &*& [q]lifetime_token(k);
{
    leak full_borrow(_, _);
    close MutexGuard_share::<'a, T>(k, t, l);
    leak MutexGuard_share::<'a, T>(k, t, l);
}

@*/

impl<'a, T: Send> !Send for MutexGuard<'a, T> {}

unsafe impl<'a, T: Send> Sync for MutexGuard<'a, T> {}

/*@

lem MutexGuard_sync<'a, T>(t: thread_id_t, t1: thread_id_t)
    req MutexGuard_share::<'a, T>(?k, t, ?l);
    ens MutexGuard_share::<'a, T>(k, t1, l);
{
    open MutexGuard_share::<'a, T>(k, t, l);
    close MutexGuard_share::<'a, T>(k, t1, l);
}

@*/

impl<T: Send> Mutex<T> {
    pub fn new(v: T) -> Mutex<T> {
        //@ close exists::<pred()>(True);
        let inner = unsafe { sys::locks::Mutex::new() };
        let data = UnsafeCell::new(v);
        let r = Mutex { inner, data };
        //@ close Mutex_own(_t, inner, data);
        r
    }

    /*
    https://doc.rust-lang.org/std/sync/struct.Mutex.html#method.lock
    "The exact behavior on locking a mutex in the thread which already holds the lock is left unspecified.
    However, this function will not return on the second call (it might panic or deadlock, for example)."
    Note that in either case it is not undefined behaviour.
    */
    pub fn lock<'a>(&'a self) -> MutexGuard<'a, T>
    //@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*& [_]Mutex_share('a, t, self);
    //@ ens thread_token(t) &*& [qa]lifetime_token('a) &*& MutexGuard_own::<'a, T>(t, result.lock);
    {
        unsafe {
            //@ open Mutex_share('a, t, self);
            //@ assert [_]exists_np(?klong);
            //@ open_frac_borrow('a, Mutex_frac_borrow_content(klong, self), qa);
            //@ open Mutex_frac_borrow_content::<T>(klong, self)();
            self.inner.lock/*@::<'a> @*/();
            //@ assert [?qp]sys::locks::SysMutex_share(&(*self).inner, _);
            //@ close [qp]Mutex_frac_borrow_content::<T>(klong, self)();
            //@ close_frac_borrow(qp, Mutex_frac_borrow_content(klong, self));
            //@ close MutexGuard_own::<'a, T>(t, self);
            MutexGuard { lock: self }
        }
    }
}

impl<'b, T: Send> Deref for MutexGuard<'b, T> {

    type Target = T;
    
    fn deref<'a>(&'a self) -> &'a T
    {
        //@ assert lifetime_inclusion('a, 'b) == true;
        //@ assume(false); //~allow_dead_code
        unsafe { &*(*self.lock).data.get() } //~allow_dead_code
    } //~allow_dead_code

}
    
impl<'b, T: Send> DerefMut for MutexGuard<'b, T> {

    fn deref_mut<'a>(&'a mut self) -> &'a mut T
    /*@
    req
        is_Send(typeid(T)) == true &*&
        thread_token(?t) &*& [?qa]lifetime_token('a) &*& [?qb]lifetime_token('b)
        &*& full_borrow('a, MutexGuard_full_borrow_content::<'b, T>(t, self))
        &*& lifetime_inclusion('a, 'b) == true;
    @*/
    //@ ens thread_token(t) &*& [qa]lifetime_token('a) &*& [qb]lifetime_token('b) &*& full_borrow('a, <T>.full_borrow_content(t, result));
    {
        //@ let kstrong = open_full_borrow_strong('a, MutexGuard_full_borrow_content::<'b, T>(t, self), qa/2);
        //@ open MutexGuard_full_borrow_content::<'b, T>(t, self)();
        //@ open MutexGuard_own::<'b, T>(t, ?lock);
        // We need `(*lock).data |-> _` to get ptr provenance info
        //@ assert [_]exists_np(?kmlong);
        //@ lifetime_inclusion_trans('a, 'b, kmlong);
        //@ lifetime_token_trade('a, qa/2, kmlong);
        //@ assert [?qkml]lifetime_token(kmlong);
        //@ open_full_borrow(qkml, kmlong, <T>.full_borrow_content(t0, &(*lock).data));
        //@ open_full_borrow_content::<T>(t0, &(*lock).data);
        //@ points_to_limits(&(*lock).data);
        //@ close_full_borrow_content::<T>(t0, &(*lock).data);
        //@ close_full_borrow(<T>.full_borrow_content(t0, &(*lock).data));
        //@ lifetime_token_trade_back(qkml, kmlong);
        let r = unsafe { &mut *(*self.lock).data.get() };
        /*@
        produce_lem_ptr_chunk full_borrow_convert_strong(True,
            sep(MutexGuard_fbc_rest::<'b, T>(kmlong, t, self, lock), full_borrow_(kmlong, <T>.full_borrow_content(t0, &(*lock).data))),
            kstrong,
            MutexGuard_full_borrow_content::<'b, T>(t, self))() {
                open sep(MutexGuard_fbc_rest::<'b, T>(kmlong, t, self, lock), full_borrow_(kmlong, <T>.full_borrow_content(t0, &(*lock).data)))();
                open MutexGuard_fbc_rest::<'b, T>(kmlong, t, self, lock)();
                open full_borrow_(kmlong, <T>.full_borrow_content(t0, &(*lock).data))();
                close exists_np(kmlong); leak exists_np(kmlong);
                close MutexGuard_own::<'b, T>(t, lock);
                close MutexGuard_full_borrow_content::<'b, T>(t, self)();
            }{
                close MutexGuard_fbc_rest::<'b, T>(kmlong, t, self, lock)();
                close full_borrow_(kmlong, <T>.full_borrow_content(t0, &(*lock).data))();
                close sep(MutexGuard_fbc_rest::<'b, T>(kmlong, t, self, lock), full_borrow_(kmlong, <T>.full_borrow_content(t0, &(*lock).data)))();
                close_full_borrow_strong(kstrong, MutexGuard_full_borrow_content::<'b, T>(t, self),
                    sep(MutexGuard_fbc_rest::<'b, T>(kmlong, t, self, lock), full_borrow_(kmlong, <T>.full_borrow_content(t0, &(*lock).data))));
                full_borrow_split(kstrong, MutexGuard_fbc_rest::<'b, T>(kmlong, t, self, lock),
                    full_borrow_(kmlong, <T>.full_borrow_content(t0, &(*lock).data)));
                full_borrow_unnest(kstrong, kmlong, <T>.full_borrow_content(t0, &(*lock).data));
                lifetime_inclusion_glb('a, kstrong, kmlong);
                full_borrow_mono(lifetime_intersection(kstrong, kmlong), 'a, <T>.full_borrow_content(t0, &(*lock).data));
            }
        @*/
        //@ leak full_borrow(kstrong, _);
        /*@
        produce_lem_ptr_chunk implies(<T>.full_borrow_content(t0, &(*lock).data), <T>.full_borrow_content(t, &(*lock).data))() {
            open_full_borrow_content(t0, &(*lock).data);
            ghost_rec_perm_top_weaken(type_depth(typeid(T)));
            assert *(&(*lock).data) |-> ?data;
            Send::send(t0, t, data);
            ghost_rec_perm_top_unweaken();
            close_full_borrow_content(t, &(*lock).data);
        } {
            produce_lem_ptr_chunk implies(<T>.full_borrow_content(t, &(*lock).data), <T>.full_borrow_content(t0, &(*lock).data))() {
                open_full_borrow_content(t, &(*lock).data);
                ghost_rec_perm_top_weaken(type_depth(typeid(T)));
                assert *(&(*lock).data) |-> ?data;
                Send::send(t, t0, data);
                ghost_rec_perm_top_unweaken();
                close_full_borrow_content(t0, &(*lock).data);
            } {
                full_borrow_implies('a, <T>.full_borrow_content(t0, &(*lock).data), <T>.full_borrow_content(t, &(*lock).data));
            }
        }
        @*/
        r
    }

}

impl<'a, T: Send> Drop for MutexGuard<'a, T> {

    fn drop<'b>(self: &'b mut MutexGuard<'a, T>)
    //@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*& MutexGuard_full_borrow_content::<'a, T>(t, self)();
    //@ ens thread_token(t) &*& [qa]lifetime_token('a) &*& (*self).lock |-> ?lock &*& [_]Mutex_share('a, t, lock) &*& struct_MutexGuard_padding(self);
    {
        //@ open MutexGuard_full_borrow_content::<'a, T>(t, self)();
        //@ open MutexGuard_own::<'a, T>(t, ?lock);
        //@ open [_]exists_np(?kmlong);
        //@ open_frac_borrow('a, Mutex_frac_borrow_content(kmlong, lock), qa);
        //@ open Mutex_frac_borrow_content::<T>(kmlong, lock)();
        unsafe {
            (*self.lock).inner.unlock/*@::<'a> @*/();
        }
        //@ assert [?qp]sys::locks::SysMutex_share(&(*lock).inner, _);
        //@ close [qp]Mutex_frac_borrow_content::<T>(kmlong, lock)();
        //@ close_frac_borrow(qp, Mutex_frac_borrow_content(kmlong, lock));
        //@ assert [?qfrac]frac_borrow('a, _);
        //@ close [qfrac]exists_np(kmlong);
        //@ close [qfrac]Mutex_share('a, t, lock);
    }

}
