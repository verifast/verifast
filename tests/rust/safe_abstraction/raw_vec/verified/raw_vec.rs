#![unstable(feature = "raw_vec_internals", reason = "unstable const warnings", issue = "none")]
#![cfg_attr(test, allow(dead_code))]

//@ use std::num::{niche_types::UsizeNoHighBit, NonZero};
//@ use std::ptr::{NonNull, NonNull_ptr, Unique, Alignment};
//@ use std::alloc::{Layout, alloc_id_t, Allocator, alloc_block_in};
//@ use std::option::Option;

// Note: This module is also included in the alloctests crate using #[path] to
// run the tests. See the comment there for an explanation why this is the case.

use core::marker::PhantomData;
use core::mem::{ManuallyDrop, MaybeUninit, SizedTypeProperties};
use core::ptr::{self, Alignment, NonNull, Unique};
use core::{cmp, hint};

#[cfg(not(no_global_oom_handling))]
use crate::alloc::handle_alloc_error;
use crate::alloc::{Allocator, Global, Layout};
use crate::boxed::Box;
use crate::collections::TryReserveError;
use crate::collections::TryReserveErrorKind::*;

//@ use std::collections::{TryReserveError, TryReserveErrorKind};

#[cfg(test)]
mod tests;

/*@

lem mul_zero(x: i32, y: i32)
    req 0 <= x &*& 0 <= y;
    ens (x * y == 0) == (x == 0 || y == 0);
{
    if x == 0 {
        if y == 0 {
        } else {
        }
    } else {
        if y == 0 {
        } else {
            mul_mono_l(1, y, x);
        }
    }
}

@*/

// One central function responsible for reporting capacity overflows. This'll
// ensure that the code generation related to these panics is minimal as there's
// only one location which panics rather than a bunch throughout the module.
#[cfg(not(no_global_oom_handling))]
#[cfg_attr(not(panic = "immediate-abort"), inline(never))]
fn capacity_overflow() -> !
//@ req thread_token(?t);
//@ ens false;
{
    panic!("capacity overflow");
}

enum AllocInit {
    /// The contents of the new memory are uninitialized.
    Uninitialized,
    #[cfg(not(no_global_oom_handling))]
    /// The new memory is guaranteed to be zeroed.
    Zeroed,
}

type Cap = core::num::niche_types::UsizeNoHighBit;

//@ fix Cap::new(n: usize) -> UsizeNoHighBit { UsizeNoHighBit::new(n) }

const ZERO_CAP: Cap = unsafe { Cap::new_unchecked(0) };

/// `Cap(cap)`, except if `T` is a ZST then `Cap::ZERO`.
///
/// # Safety: cap must be <= `isize::MAX`.
unsafe fn new_cap<T>(cap: usize) -> Cap
//@ req std::mem::size_of::<T>() == 0 || cap <= isize::MAX;
//@ ens result == if std::mem::size_of::<T>() == 0 { Cap::new(0) } else { Cap::new(cap) };
//@ on_unwind_ens false;
{
    if T::IS_ZST { ZERO_CAP } else { unsafe { Cap::new_unchecked(cap) } }
}

/// A low-level utility for more ergonomically allocating, reallocating, and deallocating
/// a buffer of memory on the heap without having to worry about all the corner cases
/// involved. This type is excellent for building your own data structures like Vec and VecDeque.
/// In particular:
///
/// * Produces `Unique::dangling()` on zero-sized types.
/// * Produces `Unique::dangling()` on zero-length allocations.
/// * Avoids freeing `Unique::dangling()`.
/// * Catches all overflows in capacity computations (promotes them to "capacity overflow" panics).
/// * Guards against 32-bit systems allocating more than `isize::MAX` bytes.
/// * Guards against overflowing your length.
/// * Calls `handle_alloc_error` for fallible allocations.
/// * Contains a `ptr::Unique` and thus endows the user with all related benefits.
/// * Uses the excess returned from the allocator to use the largest available capacity.
///
/// This type does not in anyway inspect the memory that it manages. When dropped it *will*
/// free its memory, but it *won't* try to drop its contents. It is up to the user of `RawVec`
/// to handle the actual things *stored* inside of a `RawVec`.
///
/// Note that the excess of a zero-sized types is always infinite, so `capacity()` always returns
/// `usize::MAX`. This means that you need to be careful when round-tripping this type with a
/// `Box<[T]>`, since `capacity()` won't yield the length.
#[allow(missing_debug_implementations)]
pub(crate) struct RawVec<T, A: Allocator = Global> {
    inner: RawVecInner<A>,
    _marker: PhantomData<T>,
}

/// Like a `RawVec`, but only generic over the allocator, not the type.
///
/// As such, all the methods need the layout passed-in as a parameter.
///
/// Having this separation reduces the amount of code we need to monomorphize,
/// as most operations don't need the actual type, just its layout.
#[allow(missing_debug_implementations)]
struct RawVecInner<A: Allocator = Global> {
    ptr: Unique<u8>,
    /// Never used for ZSTs; it's `capacity()`'s responsibility to return usize::MAX in that case.
    ///
    /// # Safety
    ///
    /// `cap` must be in the `0..=isize::MAX` range.
    cap: Cap,
    alloc: A,
}

/*@

fix logical_capacity(cap: UsizeNoHighBit, elem_size: usize) -> usize {
    if elem_size == 0 { usize::MAX } else { cap.as_inner() }
}

pred RawVecInner<A>(t: thread_id_t, self: RawVecInner<A>, elemLayout: Layout, alloc_id: alloc_id_t, ptr: *u8, capacity: usize) =
    Allocator(t, self.alloc, alloc_id) &*&
    capacity == logical_capacity(self.cap, elemLayout.size()) &*&
    ptr == self.ptr.as_non_null_ptr().as_ptr() &*&
    ptr as usize % elemLayout.align() == 0 &*&
    pointer_within_limits(ptr) == true &*&
    elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride)) &*&
    if capacity * elemLayout.size() == 0 {
        true
    } else {
        alloc_block_in(alloc_id, ptr, allocLayout)
    };

pred_ctor RawVecInner_full_borrow_content_<A>(t: thread_id_t, l: *RawVecInner<A>, elemLayout: Layout, alloc_id: alloc_id_t, ptr: *u8, capacity: usize)() =
    *l |-> ?self_ &*& RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);

pred RawVecInner_full_borrow<A>(k: lifetime_t, t: thread_id_t, l: *RawVecInner<A>, elemLayout: Layout, alloc_id: alloc_id_t, ptr: *u8, capacity: usize) =
    full_borrow(k, RawVecInner_full_borrow_content_(t, l, elemLayout, alloc_id, ptr, capacity));

lem RawVecInner_send_<A>(t1: thread_id_t)
    req type_interp::<A>() &*& is_Send(typeid(A)) == true &*& RawVecInner::<A>(?t0, ?self_, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    ens type_interp::<A>() &*& RawVecInner::<A>(t1, self_, elemLayout, alloc_id, ptr, capacity);
{
    open RawVecInner(t0, self_, elemLayout, alloc_id, ptr, capacity);
    std::alloc::Allocator_send(t1, self_.alloc);
    close RawVecInner(t1, self_, elemLayout, alloc_id, ptr, capacity);
}

pred RawVecInner0<A>(self: RawVecInner<A>, elemLayout: Layout, ptr: *u8, capacity: usize) =
    capacity == logical_capacity(self.cap, elemLayout.size()) &*&
    ptr == self.ptr.as_non_null_ptr().as_ptr() &*&
    ptr as usize % elemLayout.align() == 0 &*&
    pointer_within_limits(ptr) == true &*&
    elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride));

pred<A> <RawVecInner<A>>.own(t, self_) =
    <A>.own(t, self_.alloc) &*&
    RawVecInner0(self_, ?elemLayout, ?ptr, ?capacity);    

lem RawVecInner_drop<A>()
    req RawVecInner_own::<A>(?_t, ?_v);
    ens std::ptr::Unique_own::<u8>(_t, _v.ptr) &*& std::num::niche_types::UsizeNoHighBit_own(_t, _v.cap) &*& <A>.own(_t, _v.alloc);
{
    open RawVecInner_own::<A>(_t, _v);
    open RawVecInner0(_, _, _, _);
    std::ptr::close_Unique_own::<u8>(_t, _v.ptr);
    std::num::niche_types::close_UsizeNoHighBit_own(_t, _v.cap);
}

lem RawVecInner_own_mono<A0, A1>()
    req type_interp::<A0>() &*& type_interp::<A1>() &*& RawVecInner_own::<A0>(?t, ?v) &*& is_subtype_of::<A0, A1>() == true;
    ens type_interp::<A0>() &*& type_interp::<A1>() &*& RawVecInner_own::<A1>(t, RawVecInner::<A1> { ptr: upcast(v.ptr), cap: upcast(v.cap), alloc: upcast(v.alloc) });
{
    assume(false); // https://github.com/verifast/verifast/issues/610
}

lem RawVecInner_send<A>(t1: thread_id_t)
    req type_interp::<A>() &*& is_Send(typeid(A)) == true &*& RawVecInner_own::<A>(?t0, ?v);
    ens type_interp::<A>() &*& RawVecInner_own::<A>(t1, v);
{
    open RawVecInner_own::<A>(t0, v);
    Send::send::<A>(t0, t1, v.alloc);
    close RawVecInner_own::<A>(t1, v);
}

lem_auto RawVecInner_inv<A: ?Sized>()
    req RawVecInner::<A>(?t, ?self_, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    ens RawVecInner::<A>(t, self_, elemLayout, alloc_id, ptr, capacity) &*&
        lifetime_inclusion(lft_of_type::<A>(), alloc_id.lft) == true &*&
        ptr != 0 &*& ptr as usize % elemLayout.align() == 0 &*&
        elemLayout.repeat(capacity) != none &*&
        0 <= capacity &*& capacity <= usize::MAX;
{
    open RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
    std::num::niche_types::UsizeNoHighBit_inv(self_.cap);
    std::alloc::Allocator_inv();
    std::alloc::Layout_inv(elemLayout);
    close RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
}

lem RawVecInner_inv2<A>()
    req RawVecInner::<A>(?t, ?self_, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    ens RawVecInner::<A>(t, self_, elemLayout, alloc_id, ptr, capacity) &*&
        pointer_within_limits(ptr) == true &*& ptr as usize % elemLayout.align() == 0 &*&
        0 <= capacity &*& capacity <= usize::MAX &*&
        if elemLayout.size() == 0 { capacity == usize::MAX } else { capacity <= isize::MAX };
{
    open RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
    std::num::niche_types::UsizeNoHighBit_inv(self_.cap);
    close RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
}

pred_ctor RawVecInner_frac_borrow_content<A>(l: *RawVecInner<A>, elemLayout: Layout, ptr: *u8, capacity: usize)(;) =
    struct_RawVecInner_padding(l) &*&
    (*l).ptr |-> ?u &*&
    (*l).cap |-> ?cap &*&
    capacity == logical_capacity(cap, elemLayout.size()) &*&
    ptr == u.as_non_null_ptr().as_ptr() &*&
    ptr as usize % elemLayout.align() == 0 &*&
    pointer_within_limits(ptr) == true &*&
    elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride));

pred RawVecInner_share_<A>(k: lifetime_t, t: thread_id_t, l: *RawVecInner<A>, elemLayout: Layout, alloc_id: alloc_id_t, ptr: *u8, capacity: usize) =
    pointer_within_limits(&(*l).alloc) == true &*&
    [_]std::alloc::Allocator_share(k, t, &(*l).alloc, alloc_id) &*&
    elemLayout.repeat(capacity) != none &*& capacity <= usize::MAX &*&
    [_]frac_borrow(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)) &*& ptr != 0;

lem RawVecInner_share__inv<A>()
    req [_]RawVecInner_share_::<A>(?k, ?t, ?l, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    ens ptr != 0 &*& elemLayout.repeat(capacity) != none &*& capacity <= usize::MAX;
{
    open RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
}

lem RawVecInner_share__mono<A>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *RawVecInner<A>)
    req type_interp::<A>() &*& lifetime_inclusion(k1, k) == true &*& [_]RawVecInner_share_::<A>(k, t, l, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    ens type_interp::<A>() &*& [_]RawVecInner_share_::<A>(k1, t, l, elemLayout, alloc_id, ptr, capacity);
{
    open [_]RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
    std::alloc::Allocator_share_mono::<A>(k, k1, t, &(*l).alloc);
    frac_borrow_mono(k, k1, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    close RawVecInner_share_::<A>(k1, t, l, elemLayout, alloc_id, ptr, capacity);
    leak RawVecInner_share_::<A>(k1, t, l, elemLayout, alloc_id, ptr, capacity);
}

lem RawVecInner_sync_<A>(t1: thread_id_t)
    req type_interp::<A>() &*& is_Sync(typeid(A)) == true &*& [_]RawVecInner_share_::<A>(?k, ?t0, ?l, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    ens type_interp::<A>() &*& [_]RawVecInner_share_::<A>(k, t1, l, elemLayout, alloc_id, ptr, capacity);
{
    open RawVecInner_share_(k, t0, l, elemLayout, alloc_id, ptr, capacity);
    std::alloc::Allocator_sync::<A>(t1);
    close RawVecInner_share_(k, t1, l, elemLayout, alloc_id, ptr, capacity);
    leak RawVecInner_share_(k, t1, l, elemLayout, alloc_id, ptr, capacity);
}

pred RawVecInner_share_end_token<A>(k: lifetime_t, t: thread_id_t, l: *RawVecInner<A>, elemLayout: Layout, alloc_id: alloc_id_t, ptr: *u8, capacity: usize) =
    borrow_end_token(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id)) &*&
    borrow_end_token(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)) &*&
    elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride)) &*&
    if capacity * elemLayout.size() == 0 {
        true
    } else {
        alloc_block_in(alloc_id, ptr, allocLayout)
    };

pred RawVecInner_share0_end_token<A>(k: lifetime_t, t: thread_id_t, l: *RawVecInner<A>, elemLayout: Layout, alloc_id: alloc_id_t, ptr: *u8, capacity: usize) =
    borrow_end_token(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id)) &*&
    borrow_end_token(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)) &*&
    elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride));

lem RawVecInner_share_full_<A>(k: lifetime_t, l: *RawVecInner<A>)
    req type_interp::<A>() &*& atomic_mask(MaskTop) &*& [?q]lifetime_token(k) &*&
        RawVecInner_full_borrow(k, ?t, l, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    ens type_interp::<A>() &*& atomic_mask(MaskTop) &*& [q]lifetime_token(k) &*&
        [_]RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
{
    open RawVecInner_full_borrow(k, t, l, elemLayout, alloc_id, ptr, capacity);
    let klong = open_full_borrow_strong_m(k, RawVecInner_full_borrow_content_(t, l, elemLayout, alloc_id, ptr, capacity), q);
    open RawVecInner_full_borrow_content_::<A>(t, l, elemLayout, alloc_id, ptr, capacity)();
    assert *l |-> ?self_;
    open_points_to(l);
    points_to_limits(&(*l).alloc);
    open RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
    close RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
    std::alloc::close_Allocator_full_borrow_content_(t, &(*l).alloc);
    close sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity))();
    {
        pred Ctx() =
            elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride)) &*&
            if capacity * elemLayout.size() == 0 {
                true
            } else {
                alloc_block_in(alloc_id, ptr, allocLayout)
            };
        close Ctx();
        produce_lem_ptr_chunk full_borrow_convert_strong(
            Ctx,
            sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)),
            klong,
            RawVecInner_full_borrow_content_(t, l, elemLayout, alloc_id, ptr, capacity)
        )() {
            open Ctx();
            open sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity))();
            std::alloc::open_Allocator_full_borrow_content_::<A>(t, &(*l).alloc, alloc_id);
            open RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
            let self1 = *l;
            close RawVecInner(t, self1, elemLayout, alloc_id, ptr, capacity);
            close RawVecInner_full_borrow_content_::<A>(t, l, elemLayout, alloc_id, ptr, capacity)();
        } {
            close_full_borrow_strong_m(
                klong,
                RawVecInner_full_borrow_content_(t, l, elemLayout, alloc_id, ptr, capacity),
                sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity))
            );
            full_borrow_mono(klong, k, sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)));
        }
    }
    full_borrow_split_m(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity));
    full_borrow_into_frac_m(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    std::alloc::share_Allocator_full_borrow_content_m(k, t, &(*l).alloc, alloc_id);
    close RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
    leak RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
}

lem share_RawVecInner<A>(k: lifetime_t, l: *RawVecInner<A>)
    nonghost_callers_only
    req [?q]lifetime_token(k) &*&
        *l |-> ?self_ &*&
        RawVecInner(?t, self_, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    ens [q]lifetime_token(k) &*&
        [_]RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity) &*&
        RawVecInner_share_end_token(k, t, l, elemLayout, alloc_id, ptr, capacity);
{
    open RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
    close RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
    borrow(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    full_borrow_into_frac(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    points_to_limits(&(*l).alloc);
    std::alloc::close_Allocator_full_borrow_content_(t, &(*l).alloc);
    borrow(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id));
    std::alloc::share_Allocator_full_borrow_content_(k, t, &(*l).alloc, alloc_id);
    close RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
    close RawVecInner_share_end_token(k, t, l, elemLayout, alloc_id, ptr, capacity);
    leak RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
}

lem end_share_RawVecInner<A>(l: *RawVecInner<A>)
    nonghost_callers_only
    req RawVecInner_share_end_token(?k, ?t, l, ?elemLayout, ?alloc_id, ?ptr, ?capacity) &*& [_]lifetime_dead_token(k);
    ens *l |-> ?self_ &*& RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
{
    open RawVecInner_share_end_token(k, t, l, elemLayout, alloc_id, ptr, capacity);
    borrow_end(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id));
    std::alloc::open_Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id);
    borrow_end(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    open RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
    close RawVecInner(t, *l, elemLayout, alloc_id, ptr, capacity);
}

lem share_RawVecInner0<A>(k: lifetime_t, l: *RawVecInner<A>, elemLayout: Layout, ptr: *u8, capacity: usize)
    nonghost_callers_only
    req [?q]lifetime_token(k) &*&
        *l |-> ?self_ &*&
        Allocator(?t, self_.alloc, ?alloc_id) &*&
        capacity == logical_capacity(self_.cap, elemLayout.size()) &*&
        ptr == self_.ptr.as_non_null_ptr().as_ptr() &*&
        ptr as usize % elemLayout.align() == 0 &*&
        pointer_within_limits(ptr) == true &*&
        elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride));
    ens [q]lifetime_token(k) &*&
        [_]RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity) &*&
        RawVecInner_share0_end_token(k, t, l, elemLayout, alloc_id, ptr, capacity);
{
    close RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
    borrow(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    full_borrow_into_frac(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    points_to_limits(&(*l).alloc);
    std::alloc::close_Allocator_full_borrow_content_(t, &(*l).alloc);
    borrow(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id));
    std::alloc::share_Allocator_full_borrow_content_(k, t, &(*l).alloc, alloc_id);
    std::num::niche_types::UsizeNoHighBit_inv(self_.cap);
    close RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
    close RawVecInner_share0_end_token(k, t, l, elemLayout, alloc_id, ptr, capacity);
    leak RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
}

lem end_share_RawVecInner0<A>(l: *RawVecInner<A>)
    nonghost_callers_only
    req RawVecInner_share0_end_token(?k, ?t, l, ?elemLayout, ?alloc_id, ?ptr, ?capacity) &*& [_]lifetime_dead_token(k);
    ens *l |-> ?self_ &*&
        Allocator(t, self_.alloc, alloc_id) &*&
        capacity == logical_capacity(self_.cap, elemLayout.size()) &*&
        ptr == self_.ptr.as_non_null_ptr().as_ptr() &*&
        ptr as usize % elemLayout.align() == 0 &*&
        pointer_within_limits(ptr) == true &*&
        elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride));
{
    open RawVecInner_share0_end_token(k, t, l, elemLayout, alloc_id, ptr, capacity);
    borrow_end(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id));
    std::alloc::open_Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id);
    borrow_end(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    open RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
}

lem init_ref_RawVecInner_<A>(l: *RawVecInner<A>)
    nonghost_callers_only
    req ref_init_perm(l, ?l0) &*&
        [_]RawVecInner_share_(?k, ?t, l0, ?elemLayout, ?alloc_id, ?ptr, ?capacity) &*&
        [?q]lifetime_token(k);
    ens [q]lifetime_token(k) &*&
        [_]RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity) &*&
        [_]frac_borrow(k, ref_initialized_(l));
{
    open_ref_init_perm_RawVecInner(l);
    open RawVecInner_share_(k, t, l0, elemLayout, alloc_id, ptr, capacity);
    std::alloc::init_ref_Allocator_share(k, t, &(*l).alloc);
    frac_borrow_sep(k, RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc));
    open_frac_borrow_strong_(
        k,
        sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc)),
        q);
    open [?f]sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc))();
    open [f]RawVecInner_frac_borrow_content::<A>(l0, elemLayout, ptr, capacity)();
    open [f]ref_initialized_::<A>(&(*l).alloc)();
    let ptr_ = (*l0).ptr;
    let cap_ = (*l0).cap;
    init_ref_readonly(&(*l).ptr, 1/2);
    init_ref_readonly(&(*l).cap, 1/2);
    init_ref_padding_RawVecInner(l, 1/2);
    {
        pred P() = ref_padding_initialized(l);
        close [1 - f]P();
        close_ref_initialized_RawVecInner(l);
        open P();
    }
    close [f/2]RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
    close scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))();
    close [f]ref_initialized_::<RawVecInner<A>>(l)();
    close scaledp(f, ref_initialized_(l))();
    close sep_(scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)), scaledp(f, ref_initialized_(l)))();
    
    {
        pred Ctx() =
            ref_padding_end_token(l, l0, f/2) &*& [f/2]struct_RawVecInner_padding(l0) &*& [1 - f]ref_padding_initialized(l) &*&
            ref_readonly_end_token(&(*l).ptr, &(*l0).ptr, f/2) &*& [f/2](*l0).ptr |-> ptr_ &*& [1 - f]ref_initialized(&(*l).ptr) &*&
            ref_readonly_end_token(&(*l).cap, &(*l0).cap, f/2) &*& [f/2](*l0).cap |-> cap_ &*& [1 - f]ref_initialized(&(*l).cap);
        close Ctx();
        produce_lem_ptr_chunk restore_frac_borrow(
                Ctx,
                sep_(scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)), scaledp(f, ref_initialized_(l))),
                f,
                sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc)))() {
            open sep_(scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)), scaledp(f, ref_initialized_(l)))();
            open scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))();
            open RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
            open scaledp(f, ref_initialized_(l))();
            open ref_initialized_::<RawVecInner<A>>(l)();
            open Ctx();
            open_ref_initialized_RawVecInner(l);
            end_ref_readonly(&(*l).ptr);
            end_ref_readonly(&(*l).cap);
            end_ref_padding_RawVecInner(l);
            close [f]RawVecInner_frac_borrow_content::<A>(l0, elemLayout, ptr, capacity)();
            close [f]ref_initialized_::<A>(&(*l).alloc)();
            close [f]sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc))();
        } {
            close_frac_borrow_strong_();
        }
    }
    full_borrow_into_frac(k, sep_(scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)), scaledp(f, ref_initialized_(l))));
    frac_borrow_split(k, scaledp(f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)), scaledp(f, ref_initialized_(l)));
    frac_borrow_implies_scaled(k, f/2, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    frac_borrow_implies_scaled(k, f, ref_initialized_(l));
    assert pointer_within_limits(ref_origin(&(*l0).alloc)) == true;
    close RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
    leak RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
}

lem init_ref_RawVecInner_m<A>(l: *RawVecInner<A>)
    req type_interp::<A>() &*& atomic_mask(Nlft) &*& ref_init_perm(l, ?l0) &*& [_]RawVecInner_share_(?k, ?t, l0, ?elemLayout, ?alloc_id, ?ptr, ?capacity) &*& [?q]lifetime_token(k);
    ens type_interp::<A>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity) &*& [_]frac_borrow(k, ref_initialized_(l));
{
    open_ref_init_perm_RawVecInner(l);
    open RawVecInner_share_(k, t, l0, elemLayout, alloc_id, ptr, capacity);
    std::alloc::init_ref_Allocator_share_m(k, t, &(*l).alloc);
    frac_borrow_sep(k, RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc));
    let klong = open_frac_borrow_strong_m(k, sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc)), q);
    open [?f]sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc))();
    open [f]RawVecInner_frac_borrow_content::<A>(l0, elemLayout, ptr, capacity)();
    let ptr_ = (*l0).ptr;
    let cap_ = (*l0).cap;
    open [f]ref_initialized_::<A>(&(*l).alloc)();
    std::ptr::init_ref_Unique(&(*l).ptr, 1/2);
    std::num::niche_types::init_ref_UsizeNoHighBit(&(*l).cap, 1/2);
    init_ref_padding_RawVecInner(l, 1/2);
    {
        pred P() = ref_padding_initialized(l);
        close [1 - f/2]P();
        close_ref_initialized_RawVecInner(l);
        open P();
    }
    {
        pred Ctx() =
            [f/2]ref_initialized(&(*l).alloc) &*&
            ref_padding_end_token(l, l0, f/2) &*& [f/2]struct_RawVecInner_padding(l0) &*& [1 - f/2]ref_padding_initialized(l) &*&
            std::ptr::end_ref_Unique_token(&(*l).ptr, &(*l0).ptr, f/2) &*& [f/2](*l0).ptr |-> ptr_ &*& [1 - f/2]ref_initialized(&(*l).ptr) &*&
            std::num::niche_types::end_ref_UsizeNoHighBit_token(&(*l).cap, &(*l0).cap, f/2) &*& [f/2](*l0).cap |-> cap_ &*& [1 - f/2]ref_initialized(&(*l).cap);
        produce_lem_ptr_chunk frac_borrow_convert_strong(Ctx, scaledp(f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))), klong, f, sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc)))() {
            open scaledp(f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)))();
            open sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))();
            open ref_initialized_::<RawVecInner<A>>(l)();
            open RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
            open_ref_initialized_RawVecInner(l);
            open Ctx();
            std::ptr::end_ref_Unique(&(*l).ptr);
            std::num::niche_types::end_ref_UsizeNoHighBit(&(*l).cap);
            end_ref_padding_RawVecInner(l);
            close [f]RawVecInner_frac_borrow_content::<A>(l0, elemLayout, ptr, capacity)();
            close [f]ref_initialized_::<A>(&(*l).alloc)();
            close [f]sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc))();
        } {
            close Ctx();
            close [f/2]ref_initialized_::<RawVecInner<A>>(l)();
            close [f/2]RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
            close [f/2]sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))();
            close scaledp(f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)))();
            close_frac_borrow_strong_m();
            full_borrow_mono(klong, k, scaledp(f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))));
        }
    }
    full_borrow_into_frac_m(k, scaledp(f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))));
    frac_borrow_implies_scaled(k, f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)));
    frac_borrow_split(k, ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    assert pointer_within_limits(ref_origin(&(*l0).alloc)) == true;
    close RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
    leak RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
}

pred<A> <RawVecInner<A>>.share(k, t, l) = [_]RawVecInner_share_(k, t, l, _, _, _, _);

lem RawVecInner_share_mono<A>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *RawVecInner<A>)
    req type_interp::<A>() &*& lifetime_inclusion(k1, k) == true &*& [_]RawVecInner_share::<A>(k, t, l);
    ens type_interp::<A>() &*& [_]RawVecInner_share::<A>(k1, t, l);
{
    open RawVecInner_share::<A>(k, t, l);
    RawVecInner_share__mono(k, k1, t, l);
    close RawVecInner_share::<A>(k1, t, l);
    leak RawVecInner_share::<A>(k1, t, l);
}

lem RawVecInner_share_full<A>(k: lifetime_t, t: thread_id_t, l: *RawVecInner<A>)
    req type_interp::<A>() &*& atomic_mask(MaskTop) &*& full_borrow(k, RawVecInner_full_borrow_content::<A>(t, l)) &*& [?q]lifetime_token(k) &*& ref_origin(l) == l;
    ens type_interp::<A>() &*& atomic_mask(MaskTop) &*& [_]RawVecInner_share::<A>(k, t, l) &*& [q]lifetime_token(k);
{
    let klong = open_full_borrow_strong_m(k, RawVecInner_full_borrow_content(t, l), q);
    open RawVecInner_full_borrow_content::<A>(t, l)();
    open <RawVecInner<A>>.own(t, *l);
    std::alloc::open_Allocator_own((*l).alloc);
    assert Allocator(_, _, ?alloc_id);
    open RawVecInner0(?self_, ?elemLayout, ?ptr, ?capacity);
    {
        pred Ctx() = true;
        produce_lem_ptr_chunk full_borrow_convert_strong(Ctx, sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)), klong, RawVecInner_full_borrow_content(t, l))() {
            open Ctx();
            open sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))();
            std::alloc::open_Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id);
            open RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
            std::alloc::Allocator_to_own((*l).alloc);
            close RawVecInner0(*l, elemLayout, ptr, capacity);
            close <RawVecInner<A>>.own(t, *l);
            close RawVecInner_full_borrow_content::<A>(t, l)();
        } {
            close Ctx();
            std::alloc::close_Allocator_full_borrow_content_(t, &(*l).alloc);
            close RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
            close sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))();
            close_full_borrow_strong_m(klong, RawVecInner_full_borrow_content(t, l), sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)));
            full_borrow_mono(klong, k, sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)));
            full_borrow_split_m(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).alloc, alloc_id), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
        }
    }
    std::alloc::share_Allocator_full_borrow_content_m(k, t, &(*l).alloc, alloc_id);
    full_borrow_into_frac_m(k, RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    std::num::niche_types::UsizeNoHighBit_inv(self_.cap);
    close RawVecInner_share_::<A>(k, t, l, elemLayout, alloc_id, ptr, capacity);
    leak RawVecInner_share_::<A>(k, t, l, elemLayout, alloc_id, ptr, capacity);
    close RawVecInner_share::<A>(k, t, l);
    leak RawVecInner_share::<A>(k, t, l);
}

lem init_ref_RawVecInner<A>(l: *RawVecInner<A>)
    req type_interp::<A>() &*& atomic_mask(Nlft) &*& ref_init_perm(l, ?l0) &*& [_]RawVecInner_share::<A>(?k, ?t, l0) &*& [?q]lifetime_token(k);
    ens type_interp::<A>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]RawVecInner_share::<A>(k, t, l) &*& [_]frac_borrow(k, ref_initialized_(l));
{
    open RawVecInner_share::<A>(k, t, l0);
    open_ref_init_perm_RawVecInner(l);
    open RawVecInner_share_(k, t, l0, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    std::alloc::init_ref_Allocator_share_m(k, t, &(*l).alloc);
    frac_borrow_sep(k, RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc));
    let klong = open_frac_borrow_strong_m(k, sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc)), q);
    open [?f]sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc))();
    open [f]RawVecInner_frac_borrow_content::<A>(l0, elemLayout, ptr, capacity)();
    let ptr_ = (*l0).ptr;
    let cap_ = (*l0).cap;
    open [f]ref_initialized_::<A>(&(*l).alloc)();
    std::ptr::init_ref_Unique(&(*l).ptr, 1/2);
    std::num::niche_types::init_ref_UsizeNoHighBit(&(*l).cap, 1/2);
    init_ref_padding_RawVecInner(l, 1/2);
    {
        pred P() = ref_padding_initialized(l);
        close [1 - f/2]P();
        close_ref_initialized_RawVecInner(l);
        open P();
    }
    {
        pred Ctx() =
            [f/2]ref_initialized(&(*l).alloc) &*&
            ref_padding_end_token(l, l0, f/2) &*& [f/2]struct_RawVecInner_padding(l0) &*& [1 - f/2]ref_padding_initialized(l) &*&
            std::ptr::end_ref_Unique_token(&(*l).ptr, &(*l0).ptr, f/2) &*& [f/2](*l0).ptr |-> ptr_ &*& [1 - f/2]ref_initialized(&(*l).ptr) &*&
            std::num::niche_types::end_ref_UsizeNoHighBit_token(&(*l).cap, &(*l0).cap, f/2) &*& [f/2](*l0).cap |-> cap_ &*& [1 - f/2]ref_initialized(&(*l).cap);
        produce_lem_ptr_chunk frac_borrow_convert_strong(Ctx, scaledp(f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))), klong, f, sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc)))() {
            open scaledp(f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)))();
            open sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))();
            open ref_initialized_::<RawVecInner<A>>(l)();
            open RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
            open_ref_initialized_RawVecInner(l);
            open Ctx();
            std::ptr::end_ref_Unique(&(*l).ptr);
            std::num::niche_types::end_ref_UsizeNoHighBit(&(*l).cap);
            end_ref_padding_RawVecInner(l);
            close [f]RawVecInner_frac_borrow_content::<A>(l0, elemLayout, ptr, capacity)();
            close [f]ref_initialized_::<A>(&(*l).alloc)();
            close [f]sep_(RawVecInner_frac_borrow_content(l0, elemLayout, ptr, capacity), ref_initialized_(&(*l).alloc))();
        } {
            close Ctx();
            close [f/2]ref_initialized_::<RawVecInner<A>>(l)();
            close [f/2]RawVecInner_frac_borrow_content::<A>(l, elemLayout, ptr, capacity)();
            close [f/2]sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))();
            close scaledp(f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)))();
            close_frac_borrow_strong_m();
            full_borrow_mono(klong, k, scaledp(f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))));
        }
    }
    full_borrow_into_frac_m(k, scaledp(f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity))));
    frac_borrow_implies_scaled(k, f/2, sep_(ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity)));
    frac_borrow_split(k, ref_initialized_(l), RawVecInner_frac_borrow_content(l, elemLayout, ptr, capacity));
    assert pointer_within_limits(ref_origin(&(*l0).alloc)) == true;
    close RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
    leak RawVecInner_share_(k, t, l, elemLayout, alloc_id, ptr, capacity);
    close RawVecInner_share::<A>(k, t, l);
    leak RawVecInner_share(k, t, l);
}

lem RawVecInner_sync<A>(t1: thread_id_t)
    req type_interp::<A>() &*& is_Sync(typeid(A)) == true &*& [_]RawVecInner_share::<A>(?k, ?t0, ?l);
    ens type_interp::<A>() &*& [_]RawVecInner_share::<A>(k, t1, l);
{
    open RawVecInner_share::<A>(k, t0, l);
    RawVecInner_sync_::<A>(t1);
    close RawVecInner_share::<A>(k, t1, l);
    leak RawVecInner_share(k, t1, l);
}

fix RawVecInner::alloc<A>(self_: RawVecInner<A>) -> A { self_.alloc }

lem RawVecInner_into_raw_parts<A>(self_: RawVecInner<A>)
    req RawVecInner(?t, self_, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
    ens Allocator(t, self_.alloc(), alloc_id) &*&
        if capacity * elemLayout.size() == 0 {
            true
        } else {
            elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride)) &*&
            alloc_block_in(alloc_id, ptr, allocLayout)
        };
{
    open RawVecInner(t, self_, elemLayout, alloc_id, ptr, capacity);
}

@*/

/*@

pred RawVec<T, A>(t: thread_id_t, self: RawVec<T, A>, alloc_id: alloc_id_t, ptr: *T, capacity: usize) =
    RawVecInner(t, self.inner, Layout::new::<T>, alloc_id, ?ptr_, capacity) &*& ptr == ptr_ as *T;

fix RawVec_full_borrow_content_<T, A>(t: thread_id_t, l: *RawVec<T, A>, alloc_id: alloc_id_t, ptr: *T, capacity: usize) -> pred() {
    RawVecInner_full_borrow_content_(t, &(*l).inner, Layout::new::<T>(), alloc_id, ptr as *u8, capacity)
}

lem close_RawVec_full_borrow_content_<T, A>(t: thread_id_t, l: *RawVec<T, A>, alloc_id: alloc_id_t, ptr: *T, capacity: usize)
    req *l |-> ?self_ &*& RawVec(t, self_, alloc_id, ptr, capacity);
    ens RawVec_full_borrow_content_::<T, A>(t, l, alloc_id, ptr, capacity)();
{
    open RawVec(t, self_, alloc_id, ptr, capacity);
    open_points_to(l);
    close RawVecInner_full_borrow_content_::<A>(t, &(*l).inner, Layout::new::<T>(), alloc_id, ptr as *u8, capacity)();
}

lem open_RawVec_full_borrow_content_<T, A>(t: thread_id_t, l: *RawVec<T, A>, alloc_id: alloc_id_t, ptr: *T, capacity: usize)
    req RawVec_full_borrow_content_::<T, A>(t, l, alloc_id, ptr, capacity)();
    ens *l |-> ?self_ &*& RawVec(t, self_, alloc_id, ptr, capacity);
{
    open RawVecInner_full_borrow_content_::<A>(t, &(*l).inner, Layout::new::<T>(), alloc_id, ptr as *u8, capacity)();
    close RawVec(t, *l, alloc_id, ptr, capacity);
    close_points_to(l);
}

pred RawVec_full_borrow<T, A>(k: lifetime_t, t: thread_id_t, l: *RawVec<T, A>, alloc_id: alloc_id_t, ptr: *T, capacity: usize) =
    RawVecInner_full_borrow(k, t, &(*l).inner, Layout::new::<T>(), alloc_id, ptr as *u8, capacity);

lem close_RawVec_full_borrow<T, A>(k: lifetime_t, t: thread_id_t, l: *RawVec<T, A>, alloc_id: alloc_id_t, ptr: *T, capacity: usize)
    req full_borrow(k, RawVec_full_borrow_content_::<T, A>(t, l, alloc_id, ptr, capacity));
    ens RawVec_full_borrow(k, t, l, alloc_id, ptr, capacity);
{
    close RawVecInner_full_borrow(k, t, &(*l).inner, Layout::new::<T>(), alloc_id, ptr as *u8, capacity);
    close RawVec_full_borrow(k, t, l, alloc_id, ptr, capacity);
}

pred<T, A> <RawVec<T, A>>.own(t, self_) = RawVec(t, self_, ?alloc_id, ?ptr, ?capacity) &*& array_at_lft_(alloc_id.lft, ptr, capacity, _);

lem RawVec_own_mono<T0, T1, A0, A1>()
    req type_interp::<T0>() &*& type_interp::<T1>() &*& type_interp::<A0>() &*& type_interp::<A1>() &*& RawVec_own::<T0, A0>(?t, ?v) &*& is_subtype_of::<T0, T1>() == true &*& is_subtype_of::<A0, A1>() == true;
    ens type_interp::<T0>() &*& type_interp::<T1>() &*& type_interp::<A0>() &*& type_interp::<A1>() &*& RawVec_own::<T1, A1>(t, RawVec::<T1, A1> { inner: upcast(v.inner) });
{
    assume(false); // https://github.com/verifast/verifast/issues/610
}

lem RawVec_send_<T, A>(t1: thread_id_t)
    req type_interp::<A>() &*& is_Send(typeid(A)) == true &*& RawVec::<T, A>(?t0, ?v, ?alloc_id, ?ptr, ?capacity);
    ens type_interp::<A>() &*& RawVec::<T, A>(t1, v, alloc_id, ptr, capacity);
{
    open RawVec(t0, v, alloc_id, ptr, capacity);
    RawVecInner_send_::<A>(t1);
    close RawVec(t1, v, alloc_id, ptr, capacity);
}

lem RawVec_send<T, A>(t1: thread_id_t)
    req type_interp::<T>() &*& type_interp::<A>() &*& is_Send(typeid(RawVec<T, A>)) == true &*& RawVec_own::<T, A>(?t0, ?v);
    ens type_interp::<T>() &*& type_interp::<A>() &*& RawVec_own::<T, A>(t1, v);
{
    open <RawVec<T, A>>.own(t0, v);
    RawVec_send_(t1);
    close <RawVec<T, A>>.own(t1, v);
}

lem RawVec_inv<T, A>()
    req RawVec::<T, A>(?t, ?self_, ?alloc_id, ?ptr, ?capacity);
    ens RawVec::<T, A>(t, self_, alloc_id, ptr, capacity) &*&
        lifetime_inclusion(lft_of_type::<A>(), alloc_id.lft) == true &*&
        ptr != 0 &*& ptr as usize % std::mem::align_of::<T>() == 0 &*&
        0 <= capacity &*& capacity <= usize::MAX;
{
    open RawVec(t, self_, alloc_id, ptr, capacity);
    RawVecInner_inv();
    close RawVec(t, self_, alloc_id, ptr, capacity);
}

lem RawVec_inv2<T, A>()
    req RawVec::<T, A>(?t, ?self_, ?alloc_id, ?ptr, ?capacity);
    ens RawVec::<T, A>(t, self_, alloc_id, ptr, capacity) &*&
        lifetime_inclusion(lft_of_type::<A>(), alloc_id.lft) == true &*&
        ptr != 0 &*& ptr as usize % std::mem::align_of::<T>() == 0 &*&
        0 <= capacity &*&
        Layout::new::<T>().repeat(capacity) != none &*&
        if std::mem::size_of::<T>() == 0 { capacity == usize::MAX } else { capacity <= isize::MAX };
{
    open RawVec(t, self_, alloc_id, ptr, capacity);
    RawVecInner_inv2();
    close RawVec(t, self_, alloc_id, ptr, capacity);
}

lem RawVec_to_own<T, A>(self_: RawVec<T, A>)
    req RawVec(?t, self_, ?alloc_id, ?ptr, ?capacity) &*& array_at_lft_(alloc_id.lft, ptr, capacity, _);
    ens <RawVec<T, A>>.own(t, self_);
{
    close <RawVec<T, A>>.own(t, self_);
}

lem open_RawVec_own<T, A>(self_: RawVec<T, A>)
    req <RawVec<T, A>>.own(?t, self_);
    ens RawVec(t, self_, ?alloc_id, ?ptr, ?capacity) &*& array_at_lft_(alloc_id.lft, ptr, capacity, _);
{
    open <RawVec<T, A>>.own(t, self_);
}

pred RawVec_share_<T, A>(k: lifetime_t, t: thread_id_t, l: *RawVec<T, A>, alloc_id: alloc_id_t, ptr: *T, capacity: usize) =
    [_]RawVecInner_share_(k, t, &(*l).inner, Layout::new::<T>(), alloc_id, ptr as *u8, capacity);

lem RawVec_share__inv<T, A>()
    req [_]RawVec_share_::<T, A>(?k, ?t, ?l, ?alloc_id, ?ptr, ?capacity);
    ens ptr != 0 &*& Layout::new::<T>().repeat(capacity) != none &*& capacity <= usize::MAX;
{
    open RawVec_share_(k, t, l, alloc_id, ptr, capacity);
    RawVecInner_share__inv();
}

lem RawVec_share__mono<T, A>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *RawVec<T, A>)
    req type_interp::<T>() &*& type_interp::<A>() &*& lifetime_inclusion(k1, k) == true &*& [_]RawVec_share_::<T, A>(k, t, l, ?alloc_id, ?ptr, ?capacity);
    ens type_interp::<T>() &*& type_interp::<A>() &*& [_]RawVec_share_::<T, A>(k1, t, l, alloc_id, ptr, capacity);
{
    open RawVec_share_(k, t, l, alloc_id, ptr, capacity);
    RawVecInner_share__mono(k, k1, t, &(*l).inner);
    close RawVec_share_(k1, t, l, alloc_id, ptr, capacity);
    leak RawVec_share_(k1, t, l, alloc_id, ptr, capacity);
}

lem RawVec_sync_<T, A>(t1: thread_id_t)
    req type_interp::<A>() &*& [_]RawVec_share_::<T, A>(?k, ?t0, ?l, ?alloc_id, ?ptr, ?capacity) &*& is_Sync(typeid(RawVec<T, A>)) == true;
    ens type_interp::<A>() &*& [_]RawVec_share_::<T, A>(k, t1, l, alloc_id, ptr, capacity);
{
    open RawVec_share_::<T, A>(k, t0, l, alloc_id, ptr, capacity);
    RawVecInner_sync_::<A>(t1);
    close RawVec_share_::<T, A>(k, t1, l, alloc_id, ptr, capacity);
    leak RawVec_share_::<T, A>(k, t1, l, alloc_id, ptr, capacity);
}

pred RawVec_share_end_token<T, A>(k: lifetime_t, t: thread_id_t, l: *RawVec<T, A>, alloc_id: alloc_id_t, ptr: *T, capacity: usize) =
    RawVecInner_share_end_token(k, t, &(*l).inner, Layout::new::<T>(), alloc_id, ptr as *u8, capacity);

lem RawVec_share_full_<T, A>(k: lifetime_t, l: *RawVec<T, A>)
    req type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(MaskTop) &*& [?q]lifetime_token(k) &*&
        RawVec_full_borrow(k, ?t, l, ?alloc_id, ?ptr, ?capacity);
    ens type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(MaskTop) &*& [q]lifetime_token(k) &*&
        [_]RawVec_share_(k, t, l, alloc_id, ptr, capacity);
{
    open RawVec_full_borrow(k, t, l, alloc_id, ptr, capacity);
    RawVecInner_share_full_(k, &(*l).inner);
    close RawVec_share_(k, t, l, alloc_id, ptr, capacity);
    leak RawVec_share_(k, t, l, alloc_id, ptr, capacity);
}

lem share_RawVec<T, A>(k: lifetime_t, l: *RawVec<T, A>)
    nonghost_callers_only
    req [?q]lifetime_token(k) &*& *l |-> ?self_ &*& RawVec(?t, self_, ?alloc_id, ?ptr, ?capacity);
    ens [q]lifetime_token(k) &*& [_]RawVec_share_(k, t, l, alloc_id, ptr, capacity) &*& RawVec_share_end_token(k, t, l, alloc_id, ptr, capacity);
{
    open RawVec(t, self_, alloc_id, ptr, capacity);
    open_points_to(l);
    share_RawVecInner(k, &(*l).inner);
    close RawVec_share_(k, t, l, alloc_id, ptr, capacity);
    leak RawVec_share_(k, t, l, alloc_id, ptr, capacity);
    close RawVec_share_end_token(k, t, l, alloc_id, ptr, capacity);
}

lem end_share_RawVec<T, A>(l: *RawVec<T, A>)
    nonghost_callers_only
    req RawVec_share_end_token(?k, ?t, l, ?alloc_id, ?ptr, ?capacity) &*& [_]lifetime_dead_token(k);
    ens *l |-> ?self_ &*& RawVec(t, self_, alloc_id, ptr, capacity);
{
    open RawVec_share_end_token(k, t, l, alloc_id, ptr, capacity);
    end_share_RawVecInner(&(*l).inner);
    close_points_to(l);
    close RawVec(t, *l, alloc_id, ptr, capacity);
}

lem init_ref_RawVec_<T, A>(l: *RawVec<T, A>)
    nonghost_callers_only
    req ref_init_perm(l, ?l0) &*& [_]RawVec_share_(?k, ?t, l0, ?alloc_id, ?ptr, ?capacity) &*& [?q]lifetime_token(k);
    ens [q]lifetime_token(k) &*& [_]RawVec_share_(k, t, l, alloc_id, ptr, capacity) &*& [_]frac_borrow(k, ref_initialized_(l));
{
    open RawVec_share_(k, t, l0, alloc_id, ptr, capacity);
    open_ref_init_perm_RawVec(l);
    init_ref_RawVecInner_(&(*l).inner);
    close RawVec_share_(k, t, l, alloc_id, ptr, capacity);
    leak RawVec_share_(k, t, l, alloc_id, ptr, capacity);
    
    let klong = open_frac_borrow_strong(k, ref_initialized_(&(*l).inner), q);
    open [?f]ref_initialized_::<RawVecInner<A>>(&(*l).inner)();
    close_ref_initialized_RawVec(l, f);
    close [f]ref_initialized_::<RawVec<T, A>>(l)();
    {
        pred Ctx() = true;
        produce_lem_ptr_chunk frac_borrow_convert_strong(Ctx, scaledp(f, ref_initialized_(l)), klong, f, ref_initialized_(&(*l).inner))() {
            open Ctx();
            open scaledp(f, ref_initialized_(l))();
            open ref_initialized_::<RawVec<T, A>>(l)();
            open_ref_initialized_RawVec(l);
            close [f]ref_initialized_::<RawVecInner<A>>(&(*l).inner)();
        } {
            close Ctx();
            close scaledp(f, ref_initialized_(l))();
            close_frac_borrow_strong(klong, ref_initialized_(&(*l).inner), scaledp(f, ref_initialized_(l)));
            full_borrow_mono(klong, k, scaledp(f, ref_initialized_(l)));
            full_borrow_into_frac(k, scaledp(f, ref_initialized_(l)));
            frac_borrow_implies_scaled(k, f, ref_initialized_(l));
        }
    }
}

lem init_ref_RawVec_m<T, A>(l: *RawVec<T, A>)
    req type_interp::<A>() &*& atomic_mask(Nlft) &*& ref_init_perm(l, ?l0) &*& [_]RawVec_share_(?k, ?t, l0, ?alloc_id, ?ptr, ?capacity) &*& [?q]lifetime_token(k);
    ens type_interp::<A>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]RawVec_share_(k, t, l, alloc_id, ptr, capacity) &*& [_]frac_borrow(k, ref_initialized_(l));
{
    open RawVec_share_(k, t, l0, alloc_id, ptr, capacity);
    open_ref_init_perm_RawVec(l);
    init_ref_RawVecInner_m(&(*l).inner);
    close RawVec_share_(k, t, l, alloc_id, ptr, capacity);
    leak RawVec_share_(k, t, l, alloc_id, ptr, capacity);
    
    let klong = open_frac_borrow_strong_m(k, ref_initialized_(&(*l).inner), q);
    open [?f]ref_initialized_::<RawVecInner<A>>(&(*l).inner)();
    close_ref_initialized_RawVec(l, f);
    close [f]ref_initialized_::<RawVec<T, A>>(l)();
    {
        pred Ctx() = true;
        produce_lem_ptr_chunk frac_borrow_convert_strong(Ctx, scaledp(f, ref_initialized_(l)), klong, f, ref_initialized_(&(*l).inner))() {
            open Ctx();
            open scaledp(f, ref_initialized_(l))();
            open ref_initialized_::<RawVec<T, A>>(l)();
            open_ref_initialized_RawVec(l);
            close [f]ref_initialized_::<RawVecInner<A>>(&(*l).inner)();
        } {
            close Ctx();
            close scaledp(f, ref_initialized_(l))();
            close_frac_borrow_strong_m();
            full_borrow_mono(klong, k, scaledp(f, ref_initialized_(l)));
            full_borrow_into_frac_m(k, scaledp(f, ref_initialized_(l)));
            frac_borrow_implies_scaled(k, f, ref_initialized_(l));
        }
    }
}

pred<T, A> <RawVec<T, A>>.share(k, t, l) = [_]RawVec_share_(k, t, l, ?alloc_id, ?ptr, ?capacity);

lem RawVec_share_mono<T, A>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *RawVec<T, A>)
    req type_interp::<T>() &*& type_interp::<A>() &*& lifetime_inclusion(k1, k) == true &*& [_]RawVec_share::<T, A>(k, t, l);
    ens type_interp::<T>() &*& type_interp::<A>() &*& [_]RawVec_share::<T, A>(k1, t, l);
{
    open RawVec_share::<T, A>(k, t, l);
    RawVec_share__mono(k, k1, t, l);
    close RawVec_share::<T, A>(k1, t, l);
    leak RawVec_share::<T, A>(k1, t, l);
}

lem RawVec_share_full<T, A>(k: lifetime_t, t: thread_id_t, l: *RawVec<T, A>)
    req type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(MaskTop) &*& full_borrow(k, RawVec_full_borrow_content::<T, A>(t, l)) &*& [?q]lifetime_token(k) &*& ref_origin(l) == l;
    ens type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(MaskTop) &*& [_]RawVec_share::<T, A>(k, t, l) &*& [q]lifetime_token(k);
{
    let klong = open_full_borrow_strong_m(k, RawVec_full_borrow_content::<T, A>(t, l), q);
    open RawVec_full_borrow_content::<T, A>(t, l)();
    let self_ = *l;
    points_to_limits(&(*l).inner.alloc);
    open <RawVec<T, A>>.own(t, self_);
    open RawVec(t, self_, ?alloc_id, ?ptr, ?capacity);
    open RawVecInner(t, self_.inner, Layout::new::<T>(), alloc_id, ptr as *u8, capacity);
    {
        pred Ctx() =
            if capacity * std::mem::size_of::<T>() == 0 {
                true
            } else {
                Layout::new::<T>().repeat(capacity) == some(pair(?allocLayout, ?stride)) &*&
                alloc_block_in(alloc_id, ptr as *u8, allocLayout)
            } &*&
            array_at_lft_(alloc_id.lft, ptr, capacity, _);
        produce_lem_ptr_chunk full_borrow_convert_strong(Ctx, sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).inner.alloc, alloc_id), RawVecInner_frac_borrow_content(&(*l).inner, Layout::new::<T>(), ptr as *u8, capacity)), klong, RawVec_full_borrow_content(t, l))() {
            open Ctx();
            open sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).inner.alloc, alloc_id), RawVecInner_frac_borrow_content(&(*l).inner, Layout::new::<T>(), ptr as *u8, capacity))();
            std::alloc::open_Allocator_full_borrow_content_(t, &(*l).inner.alloc, alloc_id);
            open RawVecInner_frac_borrow_content::<A>(&(*l).inner, Layout::new::<T>(), ptr as *u8, capacity)();
            close RawVecInner(t, (*l).inner, Layout::new::<T>(), alloc_id, ptr as *u8, capacity);
            close RawVec(t, *l, alloc_id, ptr, capacity);
            close <RawVec<T, A>>.own(t, *l);
            close RawVec_full_borrow_content::<T, A>(t, l)();
        } {
            close Ctx();
            std::alloc::close_Allocator_full_borrow_content_(t, &(*l).inner.alloc);
            close RawVecInner_frac_borrow_content::<A>(&(*l).inner, Layout::new::<T>(), ptr as *u8, capacity)();
            close sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).inner.alloc, alloc_id), RawVecInner_frac_borrow_content(&(*l).inner, Layout::new::<T>(), ptr as *u8, capacity))();
            close_full_borrow_strong_m(klong, RawVec_full_borrow_content(t, l), sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).inner.alloc, alloc_id), RawVecInner_frac_borrow_content(&(*l).inner, Layout::new::<T>(), ptr as *u8, capacity)));
            full_borrow_mono(klong, k, sep(std::alloc::Allocator_full_borrow_content_(t, &(*l).inner.alloc, alloc_id), RawVecInner_frac_borrow_content(&(*l).inner, Layout::new::<T>(), ptr as *u8, capacity)));
            full_borrow_split_m(k, std::alloc::Allocator_full_borrow_content_(t, &(*l).inner.alloc, alloc_id), RawVecInner_frac_borrow_content(&(*l).inner, Layout::new::<T>(), ptr as *u8, capacity));
        }
    }
    std::alloc::share_Allocator_full_borrow_content_m(k, t, &(*l).inner.alloc, alloc_id);
    full_borrow_into_frac_m(k, RawVecInner_frac_borrow_content(&(*l).inner, Layout::new::<T>(), ptr as *u8, capacity));
    close RawVecInner_share_::<A>(k, t, &(*l).inner, Layout::new::<T>(), alloc_id, ptr as *u8, capacity);
    leak RawVecInner_share_::<A>(k, t, &(*l).inner, Layout::new::<T>(), alloc_id, ptr as *u8, capacity);
    close RawVec_share_::<T, A>(k, t, l, alloc_id, ptr, capacity);
    leak RawVec_share_::<T, A>(k, t, l, alloc_id, ptr, capacity);
    close RawVec_share::<T, A>(k, t, l);
    leak RawVec_share::<T, A>(k, t, l);
}

lem RawVec_sync<T, A>(t1: thread_id_t)
    req type_interp::<T>() &*& type_interp::<A>() &*& is_Sync(typeid(RawVec<T, A>)) == true &*& [_]RawVec_share::<T, A>(?k, ?t0, ?l);
    ens type_interp::<T>() &*& type_interp::<A>() &*& [_]RawVec_share::<T, A>(k, t1, l);
{
    open RawVec_share::<T, A>(k, t0, l);
    RawVec_sync_::<T, A>(t1);
    close RawVec_share::<T, A>(k, t1, l);
    leak RawVec_share::<T, A>(k, t1, l);
}

lem init_ref_RawVec<T, A>(l: *RawVec<T, A>)
    req type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(Nlft) &*& ref_init_perm(l, ?l0) &*& [_]RawVec_share::<T, A>(?k, ?t, l0) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& type_interp::<A>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]RawVec_share::<T, A>(k, t, l) &*& [_]frac_borrow(k, ref_initialized_(l));
{
    open RawVec_share::<T, A>(k, t, l0);
    open RawVec_share_(k, t, l0, ?alloc_id, ?ptr, ?capacity);
    open_ref_init_perm_RawVec(l);
    init_ref_RawVecInner_m(&(*l).inner);
    close RawVec_share_(k, t, l, alloc_id, ptr, capacity);
    leak RawVec_share_(k, t, l, alloc_id, ptr, capacity);
    close RawVec_share::<T, A>(k, t, l);
    leak RawVec_share::<T, A>(k, t, l);
    
    let klong = open_frac_borrow_strong_m(k, ref_initialized_(&(*l).inner), q);
    open [?f]ref_initialized_::<RawVecInner<A>>(&(*l).inner)();
    close_ref_initialized_RawVec(l, f);
    close [f]ref_initialized_::<RawVec<T, A>>(l)();
    {
        pred Ctx() = true;
        produce_lem_ptr_chunk frac_borrow_convert_strong(Ctx, scaledp(f, ref_initialized_(l)), klong, f, ref_initialized_(&(*l).inner))() {
            open Ctx();
            open scaledp(f, ref_initialized_(l))();
            open ref_initialized_::<RawVec<T, A>>(l)();
            open_ref_initialized_RawVec(l);
            close [f]ref_initialized_::<RawVecInner<A>>(&(*l).inner)();
        } {
            close Ctx();
            close scaledp(f, ref_initialized_(l))();
            close_frac_borrow_strong_m();
            full_borrow_mono(klong, k, scaledp(f, ref_initialized_(l)));
            full_borrow_into_frac_m(k, scaledp(f, ref_initialized_(l)));
            frac_borrow_implies_scaled(k, f, ref_initialized_(l));
        }
    }
}

fix RawVec::alloc<T, A>(self_: RawVec<T, A>) -> A { self_.inner.alloc() }

lem RawVec_into_raw_parts<T, A>(self_: RawVec<T, A>)
    req RawVec(?t, self_, ?alloc_id, ?ptr, ?capacity);
    ens Allocator(t, self_.alloc(), alloc_id) &*&
        if capacity * std::mem::size_of::<T>() == 0 {
            true
        } else {
            Layout::new::<T>().repeat(capacity) == some(pair(?allocLayout, ?stride)) &*&
            alloc_block_in(alloc_id, ptr as *u8, allocLayout)
        };
{
    open RawVec(t, self_, alloc_id, ptr, capacity);
    RawVecInner_into_raw_parts(self_.inner);
}

@*/

impl<T> RawVec<T, Global> {
    /// Creates the biggest possible `RawVec` (on the system heap)
    /// without allocating. If `T` has positive size, then this makes a
    /// `RawVec` with capacity `0`. If `T` is zero-sized, then it makes a
    /// `RawVec` with capacity `usize::MAX`. Useful for implementing
    /// delayed allocation.
    #[must_use]
    pub(crate) const fn new() -> Self {
        Self::new_in(Global)
    }

    /// Creates a `RawVec` (on the system heap) with exactly the
    /// capacity and alignment requirements for a `[T; capacity]`. This is
    /// equivalent to calling `RawVec::new` when `capacity` is `0` or `T` is
    /// zero-sized. Note that if `T` is zero-sized this means you will
    /// *not* get a `RawVec` with the requested capacity.
    ///
    /// Non-fallible version of `try_with_capacity`
    ///
    /// # Panics
    ///
    /// Panics if the requested capacity exceeds `isize::MAX` bytes.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    #[cfg(not(any(no_global_oom_handling, test)))]
    #[must_use]
    #[inline]
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self { inner: RawVecInner::with_capacity(capacity, T::LAYOUT), _marker: PhantomData }
    }

    /// Like `with_capacity`, but guarantees the buffer is zeroed.
    #[cfg(not(any(no_global_oom_handling, test)))]
    #[must_use]
    #[inline]
    pub(crate) fn with_capacity_zeroed(capacity: usize) -> Self {
        Self {
            inner: RawVecInner::with_capacity_zeroed_in(capacity, Global, T::LAYOUT),
            _marker: PhantomData,
        }
    }
}

impl RawVecInner<Global> {
    #[cfg(not(any(no_global_oom_handling, test)))]
    #[must_use]
    #[inline]
    fn with_capacity(capacity: usize, elem_layout: Layout) -> Self {
        match Self::try_allocate_in(capacity, AllocInit::Uninitialized, Global, elem_layout) {
            Ok(res) => res,
            Err(err) => handle_error(err),
        }
    }
}

// Tiny Vecs are dumb. Skip to:
// - 8 if the element size is 1, because any heap allocator is likely
//   to round up a request of less than 8 bytes to at least 8 bytes.
// - 4 if elements are moderate-sized (<= 1 KiB).
// - 1 otherwise, to avoid wasting too much space for very short Vecs.
const fn min_non_zero_cap(size: usize) -> usize
//@ req true;
//@ ens true;
//@ on_unwind_ens false;
{
    if size == 1 {
        8
    } else if size <= 1024 {
        4
    } else {
        1
    }
}

impl<T, A: Allocator> RawVec<T, A> {
    #[cfg(not(no_global_oom_handling))]
    pub(crate) const MIN_NON_ZERO_CAP: usize = min_non_zero_cap(size_of::<T>());

    /// Like `new`, but parameterized over the choice of allocator for
    /// the returned `RawVec`.
    #[inline]
    pub(crate) const fn new_in(alloc: A) -> Self
    //@ req thread_token(?t) &*& Allocator(t, alloc, ?alloc_id);
    //@ ens thread_token(t) &*& RawVec::<T, A>(t, result, alloc_id, ?ptr, ?capacity) &*& array_at_lft_(alloc_id.lft, ptr, capacity, _);
    /*@
    safety_proof {
        std::alloc::open_Allocator_own(alloc);
        let result = call();
        close <RawVec<T, A>>.own(_t, result);
    }
    @*/
    {
        // Check assumption made in `current_memory`
        const { assert!(T::LAYOUT.size() % T::LAYOUT.align() == 0) };
        //@ close exists(std::mem::size_of::<T>());
        //@ std::alloc::Layout_inv(Layout::new::<T>());
        //@ std::alloc::is_valid_layout_size_of_align_of::<T>();
        //@ std::ptr::Alignment_as_nonzero_new(std::mem::align_of::<T>());
        let r = Self { inner: RawVecInner::new_in(alloc, Alignment::of::<T>()), _marker: PhantomData };
        //@ close RawVec::<T, A>(t, r, alloc_id, ?ptr, ?capacity);
        //@ u8s_at_lft__to_array_at_lft_(ptr, capacity);
        r
    }

    /// Like `with_capacity`, but parameterized over the choice of
    /// allocator for the returned `RawVec`.
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub(crate) fn with_capacity_in(capacity: usize, alloc: A) -> Self
    //@ req thread_token(?t) &*& Allocator(t, alloc, ?alloc_id) &*& t == currentThread;
    /*@
    ens thread_token(t) &*&
        RawVec(t, result, alloc_id, ?ptr, ?capacity_) &*&
        array_at_lft_(alloc_id.lft, ptr, capacity_, _) &*&
        capacity <= capacity_;
    @*/
    /*@
    safety_proof {
        std::alloc::open_Allocator_own(alloc);
        let result = call();
        close <RawVec<T, A>>.own(_t, result);
    }
    @*/
    {
        //@ size_align::<T>();
        let r = Self {
            inner: RawVecInner::with_capacity_in(capacity, alloc, T::LAYOUT),
            _marker: PhantomData,
        };
        //@ close RawVec(t, r, alloc_id, ?ptr, ?capacity_);
        //@ u8s_at_lft__to_array_at_lft_(ptr, capacity_);
        r
    }

    /// Like `try_with_capacity`, but parameterized over the choice of
    /// allocator for the returned `RawVec`.
    #[inline]
    pub(crate) fn try_with_capacity_in(capacity: usize, alloc: A) -> Result<Self, TryReserveError> {
        match RawVecInner::try_with_capacity_in(capacity, alloc, T::LAYOUT) {
            Ok(inner) => Ok(Self { inner, _marker: PhantomData }),
            Err(e) => Err(e),
        }
    }

    /// Like `with_capacity_zeroed`, but parameterized over the choice
    /// of allocator for the returned `RawVec`.
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub(crate) fn with_capacity_zeroed_in(capacity: usize, alloc: A) -> Self {
        Self {
            inner: RawVecInner::with_capacity_zeroed_in(capacity, alloc, T::LAYOUT),
            _marker: PhantomData,
        }
    }

    /// Converts the entire buffer into `Box<[MaybeUninit<T>]>` with the specified `len`.
    ///
    /// Note that this will correctly reconstitute any `cap` changes
    /// that may have been performed. (See description of type for details.)
    ///
    /// # Safety
    ///
    /// * `len` must be greater than or equal to the most recently requested capacity, and
    /// * `len` must be less than or equal to `self.capacity()`.
    ///
    /// Note, that the requested capacity and `self.capacity()` could differ, as
    /// an allocator could overallocate and return a greater memory block than requested.
    pub(crate) unsafe fn into_box(mut self, len: usize) -> Box<[MaybeUninit<T>], A>
    //@ req thread_token(?t) &*& RawVec(t, self, ?alloc_id, ?ptr, ?capacity_) &*& array_at_lft_(alloc_id.lft, ptr as *T, len, ?vs) &*& if std::mem::size_of::<T>() == 0 { true } else { len == capacity_ };
    //@ ens thread_token(t) &*& std::boxed::Box_in::<[std::mem::MaybeUninit<T>], A>(t, result, alloc_id, slice_of_elems(map(std::mem::MaybeUninit::new_maybe_uninit, vs)));
    //@ on_unwind_ens thread_token(t);
    {
        //@ RawVec_inv2();
        
        // Sanity-check one half of the safety requirement (we cannot check the other half).
        if cfg!(debug_assertions) { //~allow_dead_code
            //@ let k = begin_lifetime();
            //@ share_RawVec(k, &self);
            //@ let self_ref = precreate_ref(&self);
            //@ init_ref_RawVec_(self_ref);
            //@ open_frac_borrow(k, ref_initialized_(self_ref), 1/2);
            //@ open [?f]ref_initialized_::<RawVec<T, A>>(self_ref)();
            let capacity = self.capacity();
            //@ close [f]ref_initialized_::<RawVec<T, A>>(self_ref)();
            //@ close_frac_borrow(f, ref_initialized_(self_ref));
            //@ end_lifetime(k);
            //@ end_share_RawVec(&self);
            //@ open_points_to(&self);
            
            if !(len <= capacity) {
                unsafe { core::hint::unreachable_unchecked(); }
            }
        }

        let mut me = ManuallyDrop::new(self);
        //@ close_points_to(&self);
        unsafe {
            //@ let k0 = begin_lifetime();
            //@ close_points_to(&me);
            //@ share_RawVec(k0, &me);
            //@ let me_ref0 = precreate_ref(&me);
            //@ init_ref_RawVec_(me_ref0);
            //@ open_frac_borrow(k0, ref_initialized_(me_ref0), 1/2);
            //@ open [?f0]ref_initialized_::<RawVec<T, A>>(me_ref0)();
            let me_ref = <ManuallyDrop<RawVec<T, A>> as core::ops::Deref>::deref(&me);
            let ptr_ = me_ref.ptr();
            let slice = ptr::slice_from_raw_parts_mut(ptr_ as *mut MaybeUninit<T>, len);
            //@ close [f0]ref_initialized_::<RawVec<T, A>>(me_ref0)();
            //@ close_frac_borrow(f0, ref_initialized_(me_ref0));
            //@ end_lifetime(k0);
            //@ end_share_RawVec(&me);
            
            //@ let me_ref1 = precreate_ref(&me);
            //@ init_ref_readonly(me_ref1, 1/2);
            //@ open_points_to(me_ref1);
            //@ let alloc_ref = precreate_ref(&(*me_ref1).inner.alloc);
            //@ init_ref_readonly(alloc_ref, 1/2);
            let alloc = ptr::read(&me.inner.alloc);
            //@ end_ref_readonly(alloc_ref);
            //@ close_points_to(me_ref1, 1/2);
            //@ end_ref_readonly(me_ref1);
            //@ open_points_to(&me);
            //@ std::mem::array_at_lft__to_array_at_lft_MaybeUninit(slice as *T);
            //@ open RawVec(_, _, _, _, _);
            //@ open RawVecInner(_, _, _, _, _, _);
            //@ size_align::<T>();
            //@ if len * std::mem::size_of::<T>() != 0 { std::alloc::Layout_repeat_some_size_aligned(Layout::new::<T>(), len); }
            //@ close_points_to_slice_at_lft(slice);
            Box::from_raw_in(slice, alloc)
        }
    }

    /// Reconstitutes a `RawVec` from a pointer, capacity, and allocator.
    ///
    /// # Safety
    ///
    /// The `ptr` must be allocated (via the given allocator `alloc`), and with the given
    /// `capacity`.
    /// The `capacity` cannot exceed `isize::MAX` for sized types. (only a concern on 32-bit
    /// systems). For ZSTs capacity is ignored.
    /// If the `ptr` and `capacity` come from a `RawVec` created via `alloc`, then this is
    /// guaranteed.
    #[inline]
    pub(crate) unsafe fn from_raw_parts_in(ptr: *mut T, capacity: usize, alloc: A) -> Self
    /*@
    req Allocator(?t, alloc, ?alloc_id) &*&
        ptr != 0 &*&
        ptr as usize % std::mem::align_of::<T>() == 0 &*&
        if capacity * std::mem::size_of::<T>() == 0 {
            true
        } else {
            Layout::new::<T>().repeat(capacity) == some(pair(?allocLayout, ?stride)) &*&
            alloc_block_in(alloc_id, ptr as *u8, allocLayout)
        };
    @*/
    //@ ens RawVec(t, result, alloc_id, ptr, ?capacity_) &*& capacity <= capacity_;
    {
        // SAFETY: Precondition passed to the caller
        unsafe {
            let ptr = ptr.cast();
            //@ std::alloc::Layout_inv(Layout::new::<T>());
            /*@
            if 1 <= std::mem::size_of::<T>() {
                if capacity != 0 {
                    mul_zero(capacity, std::mem::size_of::<T>());
                    assert Layout::new::<T>().repeat(capacity) == some(pair(?allocLayout, ?stride));
                    std::alloc::Layout_repeat_some(Layout::new::<T>(), capacity);
                    div_rem_nonneg(isize::MAX, std::mem::align_of::<T>());
                    mul_mono_l(1, std::mem::size_of::<T>(), capacity);
                    mul_mono_l(std::mem::size_of::<T>(), stride, capacity);
                    std::alloc::Layout_inv(allocLayout);
                }
            }
            @*/
            let capacity = new_cap::<T>(capacity);
            //@ close exists(Layout::new::<T>());
            let r = Self {
                inner: RawVecInner::from_raw_parts_in(ptr, capacity, alloc),
                _marker: PhantomData,
            };
            //@ close RawVec(t, r, alloc_id, ptr, _);
            r
        }
    }

    /// A convenience method for hoisting the non-null precondition out of [`RawVec::from_raw_parts_in`].
    ///
    /// # Safety
    ///
    /// See [`RawVec::from_raw_parts_in`].
    #[inline]
    pub(crate) unsafe fn from_nonnull_in(ptr: NonNull<T>, capacity: usize, alloc: A) -> Self
    /*@
    req Allocator(?t, alloc, ?alloc_id) &*&
        ptr.as_ptr() as usize % std::mem::align_of::<T>() == 0 &*&
        pointer_within_limits(ptr.as_ptr()) == true &*&
        if capacity * std::mem::size_of::<T>() == 0 {
            true
        } else {
            Layout::new::<T>().repeat(capacity) == some(pair(?allocLayout, ?stride)) &*&
            alloc_block_in(alloc_id, ptr.as_ptr() as *u8, allocLayout)
        };
    @*/
    //@ ens RawVec(t, result, alloc_id, ptr.as_ptr(), ?capacity_) &*& capacity <= capacity_;
    {
        // SAFETY: Precondition passed to the caller
        unsafe {
            let ptr = ptr.cast();
            //@ std::ptr::NonNull_Sized_as_ptr(ptr);
            //@ std::alloc::Layout_inv(Layout::new::<T>());
            /*@
            if 1 <= std::mem::size_of::<T>() && capacity != 0 {
                mul_zero(capacity, std::mem::size_of::<T>());
                assert Layout::new::<T>().repeat(capacity) == some(pair(?allocLayout, ?stride));
                std::alloc::Layout_repeat_some(Layout::new::<T>(), capacity);
                std::alloc::Layout_inv(allocLayout);
                div_rem_nonneg(isize::MAX, std::mem::align_of::<T>());
                mul_mono_l(1, std::mem::size_of::<T>(), capacity);
                mul_mono_l(std::mem::size_of::<T>(), stride, capacity);
            }
            @*/
            let capacity = new_cap::<T>(capacity);
            //@ close exists(Layout::new::<T>());
            let r = Self { inner: RawVecInner::from_nonnull_in(ptr, capacity, alloc), _marker: PhantomData };
            //@ close RawVec(t, r, alloc_id, _, _);
            r
        }
    }

    /// Gets a raw pointer to the start of the allocation. Note that this is
    /// `Unique::dangling()` if `capacity == 0` or `T` is zero-sized. In the former case, you must
    /// be careful.
    #[inline]
    pub(crate) const fn ptr(&self) -> *mut T
    //@ req [_]RawVec_share_(?k, ?t, self, ?alloc_id, ?ptr, ?capacity) &*& [?q]lifetime_token(k);
    //@ ens [q]lifetime_token(k) &*& result == ptr;
    /*@
    safety_proof {
        open <RawVec<T, A>>.share(?k, _t, self);
        call();
    }
    @*/
    {
        //@ open RawVec_share_(k, t, self, alloc_id, ptr, capacity);
        //@ let inner_ref = precreate_ref(&(*self).inner);
        //@ init_ref_RawVecInner_(inner_ref);
        //@ open_frac_borrow(k, ref_initialized_(inner_ref), q/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(inner_ref)();
        let r = self.inner.ptr();
        //@ close [f]ref_initialized_::<RawVecInner<A>>(inner_ref)();
        //@ close_frac_borrow(f, ref_initialized_(inner_ref));
        r
    }

    #[inline]
    pub(crate) const fn non_null(&self) -> NonNull<T> {
        self.inner.non_null()
    }

    /// Gets the capacity of the allocation.
    ///
    /// This will always be `usize::MAX` if `T` is zero-sized.
    #[inline]
    pub(crate) const fn capacity(&self) -> usize
    //@ req [_]RawVec_share_(?k, ?t, self, ?alloc_id, ?ptr, ?capacity) &*& [?q]lifetime_token(k);
    //@ ens [q]lifetime_token(k) &*& result == capacity;
    /*@
    safety_proof {
        open <RawVec<T, A>>.share(?k, _t, self);
        call();
    }
    @*/
    {
        //@ open RawVec_share_(k, t, self, alloc_id, ptr, capacity);
        //@ let inner_ref = precreate_ref(&(*self).inner);
        //@ init_ref_RawVecInner_(inner_ref);
        //@ open_frac_borrow(k, ref_initialized_(inner_ref), q/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(inner_ref)();
        let r = self.inner.capacity(size_of::<T>());
        //@ close [f]ref_initialized_::<RawVecInner<A>>(inner_ref)();
        //@ close_frac_borrow(f, ref_initialized_(inner_ref));
        r
    }

    /// Returns a shared reference to the allocator backing this `RawVec`.
    #[inline]
    pub(crate) fn allocator(&self) -> &A
    /*@
    req
        [?q]lifetime_token(?k) &*&
        exists(?readOnly) &*&
        if readOnly {
            [_]points_to_shared(k, self, ?self_) &*&
            ens [q]lifetime_token(k) &*&
                [_]points_to_shared(k, result, self_.alloc()) &*&
                [_]frac_borrow(k, ref_initialized_(result))
        } else {
            [_]RawVec_share_(k, ?t, self, ?alloc_id, ?ptr, ?capacity) &*&
            ens [q]lifetime_token(k) &*&
                [_]std::alloc::Allocator_share(k, t, result, alloc_id) &*&
                [_]frac_borrow(k, ref_initialized_(result))
        };
    @*/
    //@ ens true;
    /*@
    safety_proof {
        open <RawVec<T, A>>.share(?k, _t, self);
        close exists(false);
        let result = call();
        std::alloc::close_Allocator_share(k, _t, result);
    }
    @*/
    {
        //@ let inner_ref = precreate_ref(&(*self).inner);
        /*@
        if readOnly {
            open points_to_shared(k, self, ?self_);
            open_frac_borrow_strong_(k, mk_points_to(self, self_), q);
            open [?f]mk_points_to::<RawVec<T, A>>(self, self_)();
            open_points_to(self);
            close [f]mk_points_to::<RawVecInner<A>>(&(*self).inner, self_.inner)();
            close scaledp(f, mk_points_to(&(*self).inner, self_.inner))();
            produce_lem_ptr_chunk restore_frac_borrow(True, scaledp(f, mk_points_to(&(*self).inner, self_.inner)), f, mk_points_to(self, self_))() {
                open scaledp(f, mk_points_to(&(*self).inner, self_.inner))();
                open mk_points_to::<RawVecInner<A>>(&(*self).inner, self_.inner)();
                open_points_to(&(*self).inner);
                close_points_to(self, f);
                close [f]mk_points_to::<RawVec<T, A>>(self, self_)();
            } {
                close_frac_borrow_strong_();
            }
            full_borrow_into_frac(k, scaledp(f, mk_points_to(&(*self).inner, self_.inner)));
            frac_borrow_implies_scaled(k, f, mk_points_to(&(*self).inner, self_.inner));
            close points_to_shared(k, &(*self).inner, self_.inner);
            leak points_to_shared(k, &(*self).inner, self_.inner);
            init_ref_readonly_points_to_shared(inner_ref);
        } else {
            open RawVec_share_(k, ?t, self, ?alloc_id, ?ptr, ?capacity);
            init_ref_RawVecInner_(inner_ref);
        }
        @*/
        //@ open_frac_borrow(k, ref_initialized_(inner_ref), q/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(inner_ref)();
        let r = self.inner.allocator();
        //@ assert [f]ref_initialized::<RawVecInner<A>>(inner_ref);
        //@ close [f]ref_initialized_::<RawVecInner<A>>(inner_ref)();
        //@ close_frac_borrow(f, ref_initialized_(inner_ref));
        r
    }

    /// Ensures that the buffer contains at least enough space to hold `len +
    /// additional` elements. If it doesn't already have enough capacity, will
    /// reallocate enough space plus comfortable slack space to get amortized
    /// *O*(1) behavior. Will limit this behavior if it would needlessly cause
    /// itself to panic.
    ///
    /// If `len` exceeds `self.capacity()`, this may fail to actually allocate
    /// the requested space. This is not really unsafe, but the unsafe
    /// code *you* write that relies on the behavior of this function may break.
    ///
    /// This is ideal for implementing a bulk-push operation like `extend`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub(crate) fn reserve(&mut self, len: usize, additional: usize) {
        // SAFETY: All calls on self.inner pass T::LAYOUT as the elem_layout
        unsafe { self.inner.reserve(len, additional, T::LAYOUT) }
    }

    /// A specialized version of `self.reserve(len, 1)` which requires the
    /// caller to ensure `len == self.capacity()`.
    #[cfg(not(no_global_oom_handling))]
    #[inline(never)]
    pub(crate) fn grow_one(&mut self) {
        // SAFETY: All calls on self.inner pass T::LAYOUT as the elem_layout
        unsafe { self.inner.grow_one(T::LAYOUT) }
    }

    /// The same as `reserve`, but returns on errors instead of panicking or aborting.
    pub(crate) fn try_reserve(
        &mut self,
        len: usize,
        additional: usize,
    ) -> Result<(), TryReserveError>
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        *self |-> ?self0 &*&
        RawVec(t, self0, ?alloc_id, ?ptr0, ?capacity0) &*& array_at_lft_(alloc_id.lft, ptr0, capacity0, _);
    @*/
    /*@
    ens thread_token(t) &*&
        *self |-> ?self1 &*&
        match result {
            Result::Ok(u) =>
                RawVec(t, self1, alloc_id, ?ptr1, ?capacity1) &*& array_at_lft_(alloc_id.lft, ptr1, capacity1, _) &*&
                len > capacity0 || len + additional <= capacity1,
            Result::Err(e) =>
                RawVec(t, self1, alloc_id, ptr0, capacity0) &*& array_at_lft_(alloc_id.lft, ptr0, capacity0, _) &*&
                <TryReserveError>.own(t, e)
        };
    @*/
    /*@
    safety_proof {
        open <RawVec<T, A>>.own(_t, *self);
        let result = call();
        close <RawVec<T, A>>.own(_t, *self);
        match result {
            Result::Ok(u) => {
                tuple_0_eq(u);
                close_tuple_0_own(_t);
            }
            Result::Err(e) => {
            }
        }
        close <std::result::Result<(), TryReserveError>>.own(_t, result);
    }
    @*/
    {
        //@ size_align::<T>();
        //@ open_points_to(self);
        //@ close_points_to(&(*self).inner);
        //@ open RawVec(t, self0, alloc_id, ptr0, capacity0);
        //@ array_at_lft__to_u8s_at_lft_(ptr0, capacity0);
        // SAFETY: All calls on self.inner pass T::LAYOUT as the elem_layout
        let r = unsafe { self.inner.try_reserve(len, additional, T::LAYOUT) };
        //@ open_points_to(&(*self).inner);
        //@ close_points_to(self);
        //@ assert *self |-> ?self1;
        /*@
        match r {
            Result::Ok(u) => {
                close RawVec(t, self1, alloc_id, ?ptr1, ?capacity1);
                u8s_at_lft__to_array_at_lft_(ptr1, capacity1);
            }
            Result::Err(e) => {
                close RawVec(t, self1, alloc_id, ptr0, capacity0);
                u8s_at_lft__to_array_at_lft_(ptr0, capacity0);
            }
        }
        @*/
        r
    }

    /// Ensures that the buffer contains at least enough space to hold `len +
    /// additional` elements. If it doesn't already, will reallocate the
    /// minimum possible amount of memory necessary. Generally this will be
    /// exactly the amount of memory necessary, but in principle the allocator
    /// is free to give back more than we asked for.
    ///
    /// If `len` exceeds `self.capacity()`, this may fail to actually allocate
    /// the requested space. This is not really unsafe, but the unsafe code
    /// *you* write that relies on the behavior of this function may break.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` _bytes_.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    #[cfg(not(no_global_oom_handling))]
    pub(crate) fn reserve_exact(&mut self, len: usize, additional: usize) {
        // SAFETY: All calls on self.inner pass T::LAYOUT as the elem_layout
        unsafe { self.inner.reserve_exact(len, additional, T::LAYOUT) }
    }

    /// The same as `reserve_exact`, but returns on errors instead of panicking or aborting.
    pub(crate) fn try_reserve_exact(
        &mut self,
        len: usize,
        additional: usize,
    ) -> Result<(), TryReserveError>
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        *self |-> ?self0 &*&
        RawVec(t, self0, ?alloc_id, ?ptr0, ?capacity0) &*& array_at_lft_(alloc_id.lft, ptr0, capacity0, _);
    @*/
    /*@
    ens thread_token(t) &*&
        *self |-> ?self1 &*&
        match result {
            Result::Ok(u) =>
                RawVec(t, self1, alloc_id, ?ptr1, ?capacity1) &*& array_at_lft_(alloc_id.lft, ptr1, capacity1, _) &*&
                len > capacity0 || len + additional <= capacity1,
            Result::Err(e) =>
                RawVec(t, self1, alloc_id, ptr0, capacity0) &*& array_at_lft_(alloc_id.lft, ptr0, capacity0, _) &*&
                <TryReserveError>.own(t, e)
        };
    @*/
    /*@
    safety_proof {
        open <RawVec<T, A>>.own(_t, *self);
        let result = call();
        close <RawVec<T, A>>.own(_t, *self);
        match result {
            Result::Ok(u) => {
                tuple_0_eq(u);
                close_tuple_0_own(_t);
            }
            Result::Err(e) => {
            }
        }
        close <std::result::Result<(), TryReserveError>>.own(_t, result);
    }
    @*/
    {
        //@ size_align::<T>();
        //@ open_points_to(self);
        //@ close_points_to(&(*self).inner);
        //@ open RawVec(t, self0, alloc_id, ptr0, capacity0);
        //@ array_at_lft__to_u8s_at_lft_(ptr0, capacity0);
        // SAFETY: All calls on self.inner pass T::LAYOUT as the elem_layout
        let r = unsafe { self.inner.try_reserve_exact(len, additional, T::LAYOUT) };
        //@ open_points_to(&(*self).inner);
        //@ close_points_to(self);
        //@ assert *self |-> ?self1;
        /*@
        match r {
            Result::Ok(u) => {
                close RawVec(t, self1, alloc_id, ?ptr1, ?capacity1);
                u8s_at_lft__to_array_at_lft_(ptr1, capacity1);
            }
            Result::Err(e) => {
                close RawVec(t, self1, alloc_id, ptr0, capacity0);
                u8s_at_lft__to_array_at_lft_(ptr0, capacity0);
            }
        }
        @*/
        r
    }

    /// Shrinks the buffer down to the specified capacity. If the given amount
    /// is 0, actually completely deallocates.
    ///
    /// # Panics
    ///
    /// Panics if the given amount is *larger* than the current capacity.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    pub(crate) fn shrink_to_fit(&mut self, cap: usize)
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        *self |-> ?self0 &*&
        RawVec(t, self0, ?alloc_id, ?ptr0, ?capacity0) &*&
        array_at_lft_(alloc_id.lft, ptr0, capacity0, ?vs0);
    @*/
    /*@
    ens thread_token(t) &*&
        *self |-> ?self1 &*&
        RawVec(t, self1, alloc_id, ?ptr1, ?capacity1) &*&
        array_at_lft_(alloc_id.lft, ptr1, capacity1, take(capacity1, vs0)) &*&
        cap <= capacity0 &*&
        cap <= capacity1 &*&
        capacity1 == if std::mem::size_of::<T>() == 0 { usize::MAX } else { cap };
    @*/
    /*@
    safety_proof {
        open <RawVec<T, A>>.own(_t, ?self0);
        call();
        assert RawVec(_, ?self1, _, _, _);
        close <RawVec<T, A>>.own(_t, self1);
    }
    @*/
    {
        //@ size_align::<T>();
        //@ open_points_to(self);
        //@ open RawVec(t, self0, alloc_id, ptr0, capacity0);
        //@ RawVecInner_inv2();
        //@ array_at_lft__to_u8s_at_lft_(ptr0, capacity0);
        //@ assert array_at_lft_::<u8>(_, _, _, ?bs);
        //@ array_at_lft__inv();
        // SAFETY: All calls on self.inner pass T::LAYOUT as the elem_layout
        let r = unsafe { self.inner.shrink_to_fit(cap, T::LAYOUT) };
        //@ close_points_to(self);
        //@ close RawVec(t, *self, alloc_id, ?ptr1, ?capacity1);
        //@ u8s_at_lft__to_array_at_lft_(ptr1, capacity1);
        //@ vals__of_u8s__take::<T>(capacity1, bs, capacity0);
        r
    }
}

unsafe impl<#[may_dangle] T, A: Allocator> Drop for RawVec<T, A> {
    /// Frees the memory owned by the `RawVec` *without* trying to drop its contents.
    fn drop(&mut self)
    //@ req thread_token(?t) &*& t == currentThread &*& <RawVec<T, A>>.full_borrow_content(t, self)();
    //@ ens thread_token(t) &*& (*self).inner |-> ?inner &*& <RawVecInner<A>>.own(t, inner);
    {
        //@ open <RawVec<T, A>>.full_borrow_content(t, self)();
        //@ open <RawVec<T, A>>.own(t, *self);
        //@ open RawVec(t, *self, ?alloc_id, ?ptr, ?capacity);
        //@ array_at_lft__to_u8s_at_lft_(ptr, capacity);
        //@ size_align::<T>();
        // SAFETY: We are in a Drop impl, self.inner will not be used again.
        unsafe { self.inner.deallocate(T::LAYOUT) }
    }
}

impl<A: Allocator> RawVecInner<A> {
    #[inline]
    const fn new_in(alloc: A, align: Alignment) -> Self
    /*@
    req exists::<usize>(?elemSize) &*&
        thread_token(?t) &*&
        Allocator(t, alloc, ?alloc_id) &*&
        std::alloc::is_valid_layout(elemSize, align.as_nonzero().get()) == true;
    @*/
    /*@
    ens thread_token(t) &*&
        RawVecInner(t, result, Layout::from_size_align(elemSize, align.as_nonzero().get()), alloc_id, ?ptr, ?capacity) &*&
        array_at_lft_(alloc_id.lft, ptr, capacity * elemSize, []) &*&
        capacity * elemSize == 0;
    @*/
    //@ on_unwind_ens false;
    /*@
    safety_proof {
        leak <Alignment>.own(_t, align);
        close exists::<usize>(0);
        std::alloc::open_Allocator_own(alloc);
        std::ptr::Alignment_is_power_of_2(align);
        if align.as_nonzero().get() <= isize::MAX {
            div_rem_nonneg(isize::MAX, align.as_nonzero().get());
        } else {
            div_rem_nonneg_unique(isize::MAX, align.as_nonzero().get(), 0, isize::MAX);
        }
        let result = call();
        open RawVecInner(_t, result, ?elemLayout, ?alloc_id, ?ptr, ?capacity);
        std::num::niche_types::UsizeNoHighBit_inv(result.cap);
        std::alloc::Layout_inv(elemLayout);
        mul_zero(capacity, elemLayout.size());
        assert elemLayout == Layout::from_size_align(0, align.as_nonzero().get());
        std::alloc::Layout_size_Layout_from_size_align(0, align.as_nonzero().get());
        assert elemLayout.size() == 0;
        assert capacity * elemLayout.size() == 0;
        std::alloc::Allocator_to_own(result.alloc);
        close RawVecInner0(result, elemLayout, ptr, capacity);
        close <RawVecInner<A>>.own(_t, result);
        leak array_at_lft_(_, _, _, _);
    }
    @*/
    {
        let ptr = Unique::from_non_null(NonNull::without_provenance(align.as_nonzero()));
        // `cap: 0` means "unallocated". zero-sized types are ignored.
        let cap = ZERO_CAP;
        let r = Self { ptr, cap, alloc };
        //@ div_rem_nonneg_unique(align.as_nonzero().get(), align.as_nonzero().get(), 1, 0);
        //@ let layout = Layout::from_size_align(elemSize, align.as_nonzero().get());
        /*@
        if layout.size() == 0 {
            div_rem_nonneg_unique(layout.size(), layout.align(), 0, 0);
            std::alloc::Layout_repeat_size_aligned_intro(layout, logical_capacity(cap, layout.size()));
        } else {
            std::alloc::Layout_repeat_0_intro(layout);
        }
        @*/
        //@ close RawVecInner(t, r, layout, alloc_id, _, _);
        r
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    fn with_capacity_in(capacity: usize, alloc: A, elem_layout: Layout) -> Self
    /*@
    req thread_token(?t) &*&
        Allocator(t, alloc, ?alloc_id) &*&
        t == currentThread;
    @*/
    /*@
    ens thread_token(t) &*&
        RawVecInner(t, result, elem_layout, alloc_id, ?ptr, ?capacity_) &*&
        array_at_lft_(alloc_id.lft, ptr, ?n, _) &*&
        elem_layout.size() % elem_layout.align() != 0 || n == elem_layout.size() * capacity_ &*&
        capacity <= capacity_;
    @*/
    /*@
    safety_proof {
        leak <Layout>.own(_t, elem_layout);
        std::alloc::open_Allocator_own(alloc);
        let result = call();
        open RawVecInner(_t, result, elem_layout, ?alloc_id, ?ptr, ?capacity_);
        std::alloc::Allocator_to_own(result.alloc);
        close RawVecInner0(result, elem_layout, ptr, capacity_);
        close <RawVecInner<A>>.own(_t, result);
        if capacity_ * elem_layout.size() != 0 {
            leak alloc_block_in(_, _, _);
        }
        leak array_at_lft_(_, _, _, _);
    }
    @*/
    {
        match Self::try_allocate_in(capacity, AllocInit::Uninitialized, alloc, elem_layout) {
            Ok(mut this) => {
                unsafe {
                    // Make it more obvious that a subsequent Vec::reserve(capacity) will not allocate.
                    //@ let k = begin_lifetime();
                    //@ share_RawVecInner(k, &this);
                    //@ let this_ref = precreate_ref(&this);
                    //@ init_ref_RawVecInner_(this_ref);
                    //@ open_frac_borrow(k, ref_initialized_(this_ref), 1/2);
                    //@ open [?f]ref_initialized_::<RawVecInner<A>>(this_ref)();
                    let needs_to_grow = this.needs_to_grow(0, capacity, elem_layout);
                    //@ close [f]ref_initialized_::<RawVecInner<A>>(this_ref)();
                    //@ close_frac_borrow(f, ref_initialized_(this_ref));
                    //@ end_lifetime(k);
                    //@ end_share_RawVecInner(&this);
                    //@ open_points_to(&this);
                    
                    hint::assert_unchecked(!needs_to_grow);
                }
                this
            }
            Err(err) => handle_error(err),
        }
    }

    #[inline]
    fn try_with_capacity_in(
        capacity: usize,
        alloc: A,
        elem_layout: Layout,
    ) -> Result<Self, TryReserveError> {
        Self::try_allocate_in(capacity, AllocInit::Uninitialized, alloc, elem_layout)
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    fn with_capacity_zeroed_in(capacity: usize, alloc: A, elem_layout: Layout) -> Self {
        match Self::try_allocate_in(capacity, AllocInit::Zeroed, alloc, elem_layout) {
            Ok(res) => res,
            Err(err) => handle_error(err),
        }
    }

    fn try_allocate_in(
        capacity: usize,
        init: AllocInit,
        mut alloc: A,
        elem_layout: Layout,
    ) -> Result<Self, TryReserveError>
    /*@
    req thread_token(?t) &*&
        Allocator(t, alloc, ?alloc_id) &*&
        t == currentThread;
    @*/
    /*@
    ens thread_token(t) &*&
        match result {
            Result::Ok(v) =>
                RawVecInner(t, v, elem_layout, alloc_id, ?ptr, ?capacity_) &*&
                capacity <= capacity_ &*&
                match init {
                    AllocInit::Uninitialized =>
                        array_at_lft_(alloc_id.lft, ptr, ?n, _) &*&
                        elem_layout.size() % elem_layout.align() != 0 || n == capacity_ * elem_layout.size(),
                    AllocInit::Zeroed =>
                        array_at_lft(alloc_id.lft, ptr, ?n, ?bs) &*&
                        elem_layout.size() % elem_layout.align() != 0 || n == capacity_ * elem_layout.size() &*&
                        forall(bs, (eq)(0)) == true
                },
            Result::Err(e) => <TryReserveError>.own(t, e)
        };
    @*/
    /*@
    safety_proof {
        leak <AllocInit>.own(_t, init) &*& <Layout>.own(_t, elem_layout);
        std::alloc::open_Allocator_own(alloc);
        let result = call();
        match result {
            Result::Ok(r) => {
                open RawVecInner(_t, r, elem_layout, ?alloc_id, ?ptr, ?capacity_);
                if capacity_ * elem_layout.size() != 0 {
                    leak alloc_block_in(_, _, _);
                }
                std::alloc::Allocator_to_own(r.alloc);
                close RawVecInner0(r, elem_layout, ptr, capacity_);
                close <RawVecInner<A>>.own(_t, r);
                match init {
                    AllocInit::Uninitialized => { leak array_at_lft_(_, _, _, _); }
                    AllocInit::Zeroed => { leak array_at_lft(_, _, _, _); }
                }
            }
            Result::Err(e) => { }
        }
        close <std::result::Result<RawVecInner<A>, TryReserveError>>.own(_t, result);
    }
    @*/
    {
        //@ std::alloc::Layout_inv(elem_layout);
        
        // We avoid `unwrap_or_else` here because it bloats the amount of
        // LLVM IR generated.
        let layout = match layout_array(capacity, elem_layout) {
            Ok(layout) => layout,
            Err(_) => {
                //@ leak <TryReserveError>.own(_, _);
                //@ std::alloc::Allocator_to_own(alloc);
                //@ close <std::collections::TryReserveErrorKind>.own(currentThread, TryReserveErrorKind::CapacityOverflow);
                return Err(CapacityOverflow.into())
            },
        };

        //@ let elemLayout = elem_layout;
        //@ let layout_ = layout;
        //@ assert elemLayout.repeat(capacity) == some(pair(layout_, ?stride));
        //@ std::alloc::Layout_repeat_some(elemLayout, capacity);
        //@ mul_mono_l(elemLayout.size(), stride, capacity);
        // Don't allocate here because `Drop` will not deallocate when `capacity` is 0.
        if layout.size() == 0 {
            let elem_layout_alignment = elem_layout.alignment();
            //@ close exists(elem_layout.size());
            let r = Self::new_in(alloc, elem_layout_alignment);
            //@ RawVecInner_inv2::<A>();
            //@ assert RawVecInner(_, _, _, _, ?ptr_, ?capacity_);
            //@ mul_mono_l(0, capacity, elem_layout.size());
            //@ mul_zero(capacity, elem_layout.size());
            /*@
            match init {
                AllocInit::Uninitialized => { close array_at_lft_(alloc_id.lft, ptr_, 0, []); }
                AllocInit::Zeroed => { close array_at_lft(alloc_id.lft, ptr_, 0, []); }
            }
            @*/
            return Ok(r);
        }

        let result = match init {
            AllocInit::Uninitialized => {
                let r;
                //@ let alloc_ref = precreate_ref(&alloc);
                //@ let k = begin_lifetime();
                unsafe {
                    //@ let_lft 'a = k;
                    //@ std::alloc::init_ref_Allocator_at_lifetime::<'a, A>(alloc_ref);
                    r = alloc.allocate/*@::<A, 'a>@*/(layout);
                    //@ leak Allocator(_, _, _);
                }
                //@ end_lifetime(k);
                //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
                r
            }
            #[cfg(not(no_global_oom_handling))]
            AllocInit::Zeroed => {
                let r;
                //@ let alloc_ref = precreate_ref(&alloc);
                //@ let k = begin_lifetime();
                {
                    //@ let_lft 'a = k;
                    //@ std::alloc::init_ref_Allocator_at_lifetime::<'a, A>(alloc_ref);
                    r = alloc.allocate_zeroed/*@::<A, 'a>@*/(layout);
                    //@ leak Allocator(_, _, _);
                }
                //@ end_lifetime(k);
                //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
                r
            }
        };
        let ptr = match result {
            Ok(ptr) => ptr,
            Err(_) => {
                //@ std::alloc::Allocator_to_own(alloc);
                let err1 = AllocError { layout, non_exhaustive: () };
                //@ std::alloc::close_Layout_own(currentThread, layout);
                //@ close_tuple_0_own(currentThread);
                //@ close <std::collections::TryReserveErrorKind>.own(currentThread, err1);
                return Err(err1.into())
            }
        };

        // Allocators currently return a `NonNull<[u8]>` whose length
        // matches the size requested. If that ever changes, the capacity
        // here should change to `ptr.len() / size_of::<T>()`.
        /*@
        if elem_layout.size() % elem_layout.align() == 0 {
            div_rem_nonneg(elem_layout.size(), elem_layout.align());
            div_rem_nonneg(stride, elem_layout.align());
            if elem_layout.size() / elem_layout.align() < stride / elem_layout.align() {
                mul_mono_l(elem_layout.size() / elem_layout.align() + 1, stride / elem_layout.align(), elem_layout.align());
            } else {
                if elem_layout.size() / elem_layout.align() > stride / elem_layout.align() {
                    mul_mono_l(stride / elem_layout.align() + 1, elem_layout.size() / elem_layout.align(), elem_layout.align());
                    assert false;
                }
            }
            assert stride == elem_layout.size();
        }
        @*/
        /*@
        if elem_layout.size() == 0 {
            div_rem_nonneg_unique(elem_layout.size(), elem_layout.align(), 0, 0);
            assert false;
        }
        @*/
        //@ mul_mono_l(1, elem_layout.size(), capacity);
        let res = Self {
            ptr: Unique::from(ptr.cast()),
            cap: unsafe { Cap::new_unchecked(capacity) },
            alloc,
        };
        //@ std::alloc::alloc_block_in_aligned(ptr.as_ptr() as *u8);
        //@ close RawVecInner(t, res, elem_layout, alloc_id, ptr.as_ptr() as *u8, _);
        Ok(res)
    }

    #[inline]
    unsafe fn from_raw_parts_in(ptr: *mut u8, cap: Cap, alloc: A) -> Self
    /*@
    req exists::<Layout>(?elem_layout) &*&
        Allocator(?t, alloc, ?alloc_id) &*&
        ptr != 0 &*&
        ptr as usize % elem_layout.align() == 0 &*&
        if cap.as_inner() * elem_layout.size() == 0 {
            true
        } else {
            elem_layout.repeat(cap.as_inner()) == some(pair(?allocLayout, ?stride)) &*&
            alloc_block_in(alloc_id, ptr, allocLayout)
        };
    @*/
    //@ ens RawVecInner(t, result, elem_layout, alloc_id, ptr, logical_capacity(cap, elem_layout.size()));
    {
        let r = Self { ptr: unsafe { Unique::new_unchecked(ptr) }, cap, alloc };
        //@ std::alloc::Layout_inv(elem_layout);
        /*@
        if cap.as_inner() * elem_layout.size() == 0 {
            std::num::niche_types::UsizeNoHighBit_inv(cap);
            mul_zero(cap.as_inner(), elem_layout.size());
            if elem_layout.size() == 0 {
                div_rem_nonneg_unique(elem_layout.size(), elem_layout.align(), 0, 0);
                std::alloc::Layout_repeat_size_aligned_intro(elem_layout, logical_capacity(cap, elem_layout.size()));
            } else {
                std::alloc::Layout_repeat_0_intro(elem_layout);
            }
        }
        @*/
        //@ close RawVecInner(t, r, elem_layout, alloc_id, ptr, logical_capacity(cap, elem_layout.size()));
        r
    }

    #[inline]
    unsafe fn from_nonnull_in(ptr: NonNull<u8>, cap: Cap, alloc: A) -> Self
    /*@
    req exists::<Layout>(?elem_layout) &*&
        Allocator(?t, alloc, ?alloc_id) &*&
        ptr.as_ptr() as usize % elem_layout.align() == 0 &*&
        pointer_within_limits(ptr.as_ptr()) == true &*&
        if cap.as_inner() * elem_layout.size() == 0 {
            true
        } else {
            elem_layout.repeat(cap.as_inner()) == some(pair(?allocLayout, ?stride)) &*&
            alloc_block_in(alloc_id, ptr.as_ptr(), allocLayout)
        };
    @*/
    //@ ens RawVecInner(t, result, elem_layout, alloc_id, ptr.as_ptr(), logical_capacity(cap, elem_layout.size()));
    {
        let r = Self { ptr: Unique::from(ptr), cap, alloc };
        /*@
        if cap.as_inner() * elem_layout.size() == 0 {
            std::num::niche_types::UsizeNoHighBit_inv(cap);
            std::alloc::Layout_inv(elem_layout);
            mul_zero(cap.as_inner(), elem_layout.size());
            if elem_layout.size() == 0 {
                div_rem_nonneg_unique(elem_layout.size(), elem_layout.align(), 0, 0);
                std::alloc::Layout_repeat_size_aligned_intro(elem_layout, usize::MAX);
            } else {
                std::alloc::Layout_repeat_0_intro(elem_layout);
            }
        }
        @*/
        //@ close RawVecInner(t, r, elem_layout, alloc_id, _, _);
        r
    }

    #[inline]
    const fn ptr<T>(&self) -> *mut T
    /*@
    req [_]RawVecInner_share_(?k, ?t, self, ?elem_layout, ?alloc_id, ?ptr, ?capacity) &*&
        [?q]lifetime_token(k);
    @*/
    //@ ens [q]lifetime_token(k) &*& result == ptr as *T;
    /*@
    safety_proof {
        open <RawVecInner<A>>.share(?k, _t, self);
        call();
    }
    @*/
    {
        //@ RawVecInner_share__inv::<A>();
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_RawVecInner_(self_ref);
        //@ open_frac_borrow(k, ref_initialized_(self_ref), q/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        let r = unsafe { &*(self as *const RawVecInner<A>) }.non_null::<T>();
        //@ close [f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        //@ close_frac_borrow(f, ref_initialized_(self_ref));
        r.as_ptr()
    }

    #[inline]
    const fn non_null<T>(&self) -> NonNull<T>
    //@ req [_]RawVecInner_share_(?k, ?t, self, ?elem_layout, ?alloc_id, ?ptr, ?capacity) &*& [?q]lifetime_token(k);
    //@ ens [q]lifetime_token(k) &*& result.as_ptr() == ptr as *T;
    /*@
    safety_proof {
        open <RawVecInner<A>>.share(?k, _t, self);
        let result = call();
        std::ptr::close_NonNull_own::<T>(_t, result);
    }
    @*/
    {
        //@ open RawVecInner_share_(k, t, self, elem_layout, alloc_id, ptr, capacity);
        //@ open_frac_borrow(k, RawVecInner_frac_borrow_content(self, elem_layout, ptr, capacity), q);
        //@ open [?f]RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr, capacity)();
        let r = self.ptr.cast().as_non_null_ptr();
        //@ close [f]RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr, capacity)();
        //@ close_frac_borrow(f, RawVecInner_frac_borrow_content(self, elem_layout, ptr, capacity));
        r
    }

    #[inline]
    const fn capacity(&self, elem_size: usize) -> usize
    /*@
    req [_]RawVecInner_share_(?k, ?t, self, ?elem_layout, ?alloc_id, ?ptr, ?capacity) &*&
        [?q]lifetime_token(k);
    @*/
    //@ ens [q]lifetime_token(k) &*& elem_size != elem_layout.size() || result == capacity;
    /*@
    safety_proof {
        open <RawVecInner<A>>.share(?k, _t, self);
        call();
    }
    @*/
    {
        //@ open RawVecInner_share_(k, t, self, elem_layout, alloc_id, ptr, capacity);
        //@ open_frac_borrow(k, RawVecInner_frac_borrow_content(self, elem_layout, ptr, capacity), q);
        //@ open [?f]RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr, capacity)();
        let r =
            if elem_size == 0 { usize::MAX } else { self.cap.as_inner() };
        //@ close [f]RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr, capacity)();
        //@ close_frac_borrow(f, RawVecInner_frac_borrow_content(self, elem_layout, ptr, capacity));
        r
    }

    #[inline]
    fn allocator(&self) -> &A
    /*@
    req [?q]lifetime_token(?k) &*&
        exists(?readOnly) &*&
        if readOnly {
            [_]points_to_shared(k, self, ?self_) &*&
            ens [q]lifetime_token(k) &*&
                [_]points_to_shared(k, result, self_.alloc()) &*&
                [_]frac_borrow(k, ref_initialized_(result))
        } else {
            [_]RawVecInner_share_(k, ?t, self, ?elem_layout, ?alloc_id, ?ptr, ?capacity) &*&
            ens [q]lifetime_token(k) &*&
                [_]std::alloc::Allocator_share(k, t, result, alloc_id) &*&
                [_]frac_borrow(k, ref_initialized_(result))
        };
    @*/
    //@ ens true;
    /*@
    safety_proof {
        open <RawVecInner<A>>.share(?k, _t, self);
        close exists(false);
        let result = call();
        std::alloc::close_Allocator_share(k, _t, result);
    }
    @*/
    {
        //@ let alloc_ref = precreate_ref(&(*self).alloc);
        /*@
        if readOnly {
            open points_to_shared(k, self, ?self_);
            open_frac_borrow_strong_(k, mk_points_to(self, self_), q);
            open [?f]mk_points_to::<RawVecInner<A>>(self, self_)();
            open_points_to(self);
            close [f]mk_points_to::<A>(&(*self).alloc, self_.alloc)();
            close scaledp(f, mk_points_to(&(*self).alloc, self_.alloc))();
            {
                pred Ctx() = [f](*self).ptr |-> self_.ptr &*& [f](*self).cap |-> self_.cap &*& [f]struct_RawVecInner_padding(self);
                close Ctx();
                produce_lem_ptr_chunk restore_frac_borrow(Ctx, scaledp(f, mk_points_to(&(*self).alloc, self_.alloc)), f, mk_points_to(self, self_))() {
                    open Ctx();
                    open scaledp(f, mk_points_to(&(*self).alloc, self_.alloc))();
                    open [f]mk_points_to::<A>(&(*self).alloc, self_.alloc)();
                    close [f]mk_points_to::<RawVecInner<A>>(self, self_)();
                } {
                    close_frac_borrow_strong_();
                    full_borrow_into_frac(k, scaledp(f, mk_points_to(&(*self).alloc, self_.alloc)));
                }
            }
            frac_borrow_implies_scaled(k, f, mk_points_to(&(*self).alloc, self_.alloc));
            close points_to_shared(k, &(*self).alloc, self_.alloc);
            leak points_to_shared(k, &(*self).alloc, self_.alloc);
            init_ref_readonly_points_to_shared(alloc_ref);
        } else {
            open RawVecInner_share_(k, ?t, self, ?elem_layout, ?alloc_id, ?ptr, ?capacity);
            std::alloc::init_ref_Allocator_share(k, t, alloc_ref);
        }
        @*/
        //@ open_frac_borrow(k, ref_initialized_::<A>(alloc_ref), q);
        //@ open [?f]ref_initialized_::<A>(alloc_ref)();
        let r = &self.alloc;
        //@ close [f]ref_initialized_::<A>(alloc_ref)();
        //@ close_frac_borrow(f, ref_initialized_::<A>(alloc_ref));
        r
    }

    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    #[inline]
    unsafe fn current_memory(&self, elem_layout: Layout) -> Option<(NonNull<u8>, Layout)>
    /*@
    req [_]RawVecInner_share_(?k, ?t, self, elem_layout, ?alloc_id, ?ptr, ?capacity) &*&
        [?q]lifetime_token(k) &*& elem_layout.size() % elem_layout.align() == 0;
    @*/
    /*@
    ens [q]lifetime_token(k) &*&
        if capacity * elem_layout.size() == 0 {
            result == Option::None
        } else {
            result == Option::Some(?r) &*&
            r.0.as_ptr() == ptr &*&
            r.1 == Layout::from_size_align(capacity * elem_layout.size(), elem_layout.align())
        };
    @*/
    //@ on_unwind_ens false;
    {
        //@ open RawVecInner_share_(k, t, self, elem_layout, alloc_id, ptr, capacity);
        //@ open_frac_borrow(k, RawVecInner_frac_borrow_content(self, elem_layout, ptr, capacity), q);
        //@ open [?f]RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr, capacity)();
        //@ std::num::niche_types::UsizeNoHighBit_inv((*self).cap);
        //@ std::alloc::Layout_inv(elem_layout);
        //@ mul_zero(capacity, elem_layout.size());
        if elem_layout.size() == 0 || self.cap.as_inner() == 0 {
            //@ close [f]RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr, capacity)();
            //@ close_frac_borrow(f, RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr, capacity));
            None
        } else {
            // We could use Layout::array here which ensures the absence of isize and usize overflows
            // and could hypothetically handle differences between stride and size, but this memory
            // has already been allocated so we know it can't overflow and currently Rust does not
            // support such types. So we can do better by skipping some checks and avoid an unwrap.
            unsafe {
                //@ let elemLayout = elem_layout;
                //@ assert elemLayout.repeat(capacity) == some(pair(?allocLayout, ?stride));
                //@ std::alloc::Layout_repeat_some_size_aligned(elem_layout, capacity);
                //@ std::alloc::Layout_inv(allocLayout);
                //@ is_power_of_2_pos(elem_layout.align());
                //@ div_rem_nonneg(isize::MAX, elem_layout.align());
                let alloc_size = elem_layout.size().unchecked_mul(self.cap.as_inner());
                let layout = Layout::from_size_align_unchecked(alloc_size, elem_layout.align());
                let ptr_ = self.ptr.into();
                //@ std::ptr::NonNull_new_as_ptr((*self).ptr.as_non_null_ptr());
                //@ close [f]RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr, capacity)();
                //@ close_frac_borrow(f, RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr, capacity));
                Some((ptr_, layout))
            }
        }
    }

    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    unsafe fn reserve(&mut self, len: usize, additional: usize, elem_layout: Layout) {
        // Callers expect this function to be very cheap when there is already sufficient capacity.
        // Therefore, we move all the resizing and error-handling logic from grow_amortized and
        // handle_reserve behind a call, while making sure that this function is likely to be
        // inlined as just a comparison and a call if the comparison fails.
        #[cold]
        unsafe fn do_reserve_and_handle<A: Allocator>(
            slf: &mut RawVecInner<A>,
            len: usize,
            additional: usize,
            elem_layout: Layout,
        ) {
            // SAFETY: Precondition passed to caller
            if let Err(err) = unsafe { slf.grow_amortized(len, additional, elem_layout) } {
                handle_error(err);
            }
        }

        if self.needs_to_grow(len, additional, elem_layout) {
            unsafe {
                do_reserve_and_handle(self, len, additional, elem_layout);
            }
        }
    }

    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    unsafe fn grow_one(&mut self, elem_layout: Layout) {
        // SAFETY: Precondition passed to caller
        if let Err(err) = unsafe { self.grow_amortized(self.cap.as_inner(), 1, elem_layout) } {
            handle_error(err);
        }
    }

    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    unsafe fn try_reserve(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveError>
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        elem_layout.size() % elem_layout.align() == 0 &*&
        *self |-> ?self0 &*&
        RawVecInner(t, self0, elem_layout, ?alloc_id, ?ptr0, ?capacity0) &*&
        array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), _);
    @*/
    /*@
    ens thread_token(t) &*&
        *self |-> ?self1 &*&
        match result {
            Result::Ok(u) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ?ptr1, ?capacity1) &*&
                array_at_lft_(alloc_id.lft, ptr1, capacity1 * elem_layout.size(), _) &*&
                len > capacity0 || len + additional <= capacity1,
            Result::Err(e) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ptr0, capacity0) &*&
                array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), _) &*&
                <TryReserveError>.own(t, e)
        };
    @*/
    {
        //@ let k = begin_lifetime();
        //@ share_RawVecInner(k, self);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_RawVecInner_(self_ref);
        //@ open_frac_borrow(k, ref_initialized_(self_ref), 1/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        let needs_to_grow = self.needs_to_grow(len, additional, elem_layout);
        //@ close [f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        //@ close_frac_borrow(f, ref_initialized_(self_ref));
        //@ end_lifetime(k);
        //@ end_share_RawVecInner(self);
        
        if needs_to_grow {
            // SAFETY: Precondition passed to caller
            unsafe {
                self.grow_amortized(len, additional, elem_layout)?;
            }
        }
        unsafe {
            //@ let k2 = begin_lifetime();
            //@ share_RawVecInner(k2, self);
            //@ let self_ref2 = precreate_ref(self);
            //@ init_ref_RawVecInner_(self_ref2);
            //@ open_frac_borrow(k2, ref_initialized_(self_ref2), 1/2);
            //@ open [?f2]ref_initialized_::<RawVecInner<A>>(self_ref2)();
            let needs_to_grow2 = self.needs_to_grow(len, additional, elem_layout);
            //@ close [f2]ref_initialized_::<RawVecInner<A>>(self_ref2)();
            //@ close_frac_borrow(f2, ref_initialized_(self_ref2));
            //@ end_lifetime(k2);
            //@ end_share_RawVecInner(self);
            
            // Inform the optimizer that the reservation has succeeded or wasn't needed
            hint::assert_unchecked(!needs_to_grow2);
            
        }
        Ok(())
    }

    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    #[cfg(not(no_global_oom_handling))]
    unsafe fn reserve_exact(&mut self, len: usize, additional: usize, elem_layout: Layout) {
        // SAFETY: Precondition passed to caller
        if let Err(err) = unsafe { self.try_reserve_exact(len, additional, elem_layout) } {
            handle_error(err);
        }
    }

    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    unsafe fn try_reserve_exact(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveError>
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        elem_layout.size() % elem_layout.align() == 0 &*&
        *self |-> ?self0 &*&
        RawVecInner(t, self0, elem_layout, ?alloc_id, ?ptr0, ?capacity0) &*&
        array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), _);
    @*/
    /*@
    ens thread_token(t) &*&
        *self |-> ?self1 &*&
        match result {
            Result::Ok(u) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ?ptr1, ?capacity1) &*&
                array_at_lft_(alloc_id.lft, ptr1, capacity1 * elem_layout.size(), _) &*&
                len > capacity0 || len + additional <= capacity1,
            Result::Err(e) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ptr0, capacity0) &*&
                array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), _) &*&
                <TryReserveError>.own(t, e)
        };
    @*/
    {
        //@ let k = begin_lifetime();
        //@ share_RawVecInner(k, self);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_RawVecInner_(self_ref);
        //@ open_frac_borrow(k, ref_initialized_(self_ref), 1/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        let needs_to_grow = self.needs_to_grow(len, additional, elem_layout);
        //@ close [f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        //@ close_frac_borrow(f, ref_initialized_(self_ref));
        //@ end_lifetime(k);
        //@ end_share_RawVecInner(self);
        
        if needs_to_grow {
            // SAFETY: Precondition passed to caller
            unsafe {
                self.grow_exact(len, additional, elem_layout)?;
            }
        }
        unsafe {
            //@ let k2 = begin_lifetime();
            //@ share_RawVecInner(k2, self);
            //@ let self_ref2 = precreate_ref(self);
            //@ init_ref_RawVecInner_(self_ref2);
            //@ open_frac_borrow(k2, ref_initialized_(self_ref2), 1/2);
            //@ open [?f2]ref_initialized_::<RawVecInner<A>>(self_ref2)();
            let needs_to_grow2 = self.needs_to_grow(len, additional, elem_layout);
            //@ close [f2]ref_initialized_::<RawVecInner<A>>(self_ref2)();
            //@ close_frac_borrow(f2, ref_initialized_(self_ref2));
            //@ end_lifetime(k2);
            //@ end_share_RawVecInner(self);
            
            // Inform the optimizer that the reservation has succeeded or wasn't needed
            hint::assert_unchecked(!needs_to_grow2);
            
        }
        Ok(())
    }

    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    /// - `cap` must be less than or equal to `self.capacity(elem_layout.size())`
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    unsafe fn shrink_to_fit(&mut self, cap: usize, elem_layout: Layout)
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        elem_layout.size() % elem_layout.align() == 0 &*&
        *self |-> ?self0 &*&
        RawVecInner(t, self0, elem_layout, ?alloc_id, ?ptr0, ?capacity0) &*&
        array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), ?bs0);
    @*/
    /*@
    ens thread_token(t) &*&
        *self |-> ?self1 &*&
        RawVecInner(t, self1, elem_layout, alloc_id, ?ptr1, ?capacity1) &*&
        array_at_lft_(alloc_id.lft, ptr1, capacity1 * elem_layout.size(), take(capacity1 * elem_layout.size(), bs0)) &*&
        cap <= capacity0 &*&
        cap <= capacity1 &*&
        capacity1 == if elem_layout.size() == 0 { usize::MAX } else { cap };
    @*/
    {
        if let Err(err) = unsafe { self.shrink(cap, elem_layout) } {
            handle_error(err);
        }
    }

    #[inline]
    fn needs_to_grow(&self, len: usize, additional: usize, elem_layout: Layout) -> bool
    /*@
    req [_]RawVecInner_share_(?k, ?t, self, ?elemLayout, ?alloc_id, ?ptr, ?capacity) &*&
        [?qa]lifetime_token(k);
    @*/
    //@ ens [qa]lifetime_token(k) &*& elem_layout != elemLayout || result == (additional > std::num::wrapping_sub_usize(capacity, len));
    /*@
    safety_proof {
        leak <Layout>.own(_t, elem_layout);
        open <RawVecInner<A>>.share(?k, _t, self);
        call();
    }
    @*/
    {
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_RawVecInner_(self_ref);
        //@ open_frac_borrow(k, ref_initialized_(self_ref), qa/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        let r = additional > unsafe { &*(self as *const RawVecInner<A>) }.capacity(elem_layout.size()).wrapping_sub(len);
        //@ close [f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        //@ close_frac_borrow(f, ref_initialized_(self_ref));
        r
    }

    #[inline]
    unsafe fn set_ptr_and_cap(&mut self, ptr: NonNull<[u8]>, cap: usize)
    //@ req (*self).ptr |-> _ &*& (*self).cap |-> _ &*& cap <= isize::MAX;
    //@ ens (*self).ptr |-> Unique::from_non_null::<u8>(ptr.as_non_null_ptr()) &*& (*self).cap |-> UsizeNoHighBit::new(cap);
    {
        //@ std::ptr::NonNull_new_as_ptr(ptr.as_non_null_ptr());
        // Allocators currently return a `NonNull<[u8]>` whose length matches
        // the size requested. If that ever changes, the capacity here should
        // change to `ptr.len() / size_of::<T>()`.
        self.ptr = Unique::from(ptr.cast());
        self.cap = unsafe { Cap::new_unchecked(cap) };
    }

    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    /// - The sum of `len` and `additional` must be greater than the current capacity
    unsafe fn grow_amortized(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveError>
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        elem_layout.size() % elem_layout.align() == 0 &*&
        *self |-> ?self0 &*&
        RawVecInner(t, self0, elem_layout, ?alloc_id, ?ptr0, ?capacity0) &*&
        array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), _) &*&
        capacity0 < len + additional;
    @*/
    /*@
    ens thread_token(t) &*&
        *self |-> ?self1 &*&
        match result {
            Result::Ok(u) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ?ptr1, ?capacity1) &*&
                array_at_lft_(alloc_id.lft, ptr1, capacity1 * elem_layout.size(), _) &*&
                len + additional <= capacity1,
            Result::Err(e) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ptr0, capacity0) &*&
                array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), _) &*&
                <TryReserveError>.own(t, e)
        };
    @*/
    {
        // This is ensured by the calling contexts.
        if cfg!(debug_assertions) { //~allow_dead_code // FIXME: The source location associated with a dead `else` branch is the entire `if` statement :-(
            assert!(additional > 0);
        }

        if elem_layout.size() == 0 {
            // Since we return a capacity of `usize::MAX` when `elem_size` is
            // 0, getting to here necessarily means the `RawVec` is overfull.
            //@ close <std::collections::TryReserveErrorKind>.own(t, TryReserveErrorKind::CapacityOverflow);
            return Err(CapacityOverflow.into());
        }

        // Nothing we can really do about these checks, sadly.
        //@ close <std::collections::TryReserveErrorKind>.own(t, TryReserveErrorKind::CapacityOverflow);
        let required_cap = len.checked_add(additional).ok_or(CapacityOverflow)?;
        //@ leak <std::collections::TryReserveErrorKind>.own(t, TryReserveErrorKind::CapacityOverflow);

        //@ open_points_to(self);
        //@ std::num::niche_types::UsizeNoHighBit_inv(self0.cap);
        // This guarantees exponential growth. The doubling cannot overflow
        // because `cap <= isize::MAX` and the type of `cap` is `usize`.
        let cap0 = cmp::max(self.cap.as_inner() * 2, required_cap);
        let cap = cmp::max(min_non_zero_cap(elem_layout.size()), cap0);

        //@ let k = begin_lifetime();
        //@ open RawVecInner(t, self0, elem_layout, alloc_id, ptr0, capacity0);
        //@ share_RawVecInner0(k, self, elem_layout, ptr0, capacity0);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_RawVecInner_(self_ref);
        //@ open_frac_borrow(k, ref_initialized_(self_ref), 1/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        let finish_grow_result;
        {
            //@ let_lft 'a = k;
            finish_grow_result = unsafe { self.finish_grow/*@::<A, 'a>@*/(cap, elem_layout) };
        }
        //@ close [f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        //@ close_frac_borrow(f, ref_initialized_(self_ref));
        //@ end_lifetime(k);
        //@ end_share_RawVecInner0(self);
        
        //@ open_points_to(self);
        
        //@ mul_mono_l(1, elem_layout.size(), cap);

        // SAFETY: Precondition passed to caller + `current_memory` does the right thing
        match core::ops::Try::branch(finish_grow_result) {
            core::ops::ControlFlow::Break(residual) => {
                //@ let self1 = *self;
                //@ close RawVecInner(t, self1, elem_layout, alloc_id, ptr0, capacity0);
                core::ops::FromResidual::from_residual(residual)
            }
            core::ops::ControlFlow::Continue(ptr) => {
                unsafe {
                    // SAFETY: layout_array would have resulted in a capacity overflow if we tried to allocate more than `isize::MAX` items
                    self.set_ptr_and_cap(ptr, cap);
                    //@ let self1 = *self;
                    //@ std::alloc::alloc_block_in_aligned(ptr.as_ptr() as *u8);
                    //@ std::num::niche_types::UsizeNoHighBit_as_inner_new(cap);
                    //@ mul_zero(elem_layout.size(), cap);
                    //@ assert 0 <= self0.cap.as_inner();
                    //@ assert 0 <= logical_capacity(self0.cap, elem_layout.size());
                    //@ assert cap != 0;
                    //@ std::alloc::Layout_inv(elem_layout);
                    //@ assert 0 <= cap * elem_layout.size();
                    //@ assert cap * elem_layout.size() <= isize::MAX - isize::MAX % elem_layout.align();
                    //@ std::alloc::Layout_repeat_some_size_aligned(elem_layout, cap);
                    //@ assert ptr.as_ptr() as usize % Layout::from_size_align(cap * elem_layout.size(), elem_layout.align()).align() == 0;
                    //@ std::alloc::Layout_align_Layout_from_size_align(cap * elem_layout.size(), elem_layout.align());
                    //@ close RawVecInner::<A>(t, self1, elem_layout, alloc_id, ptr.as_ptr() as *u8, cap);
                }
                Ok(())
            }
        }
    }

    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    /// - The sum of `len` and `additional` must be greater than the current capacity
    unsafe fn grow_exact(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveError>
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        elem_layout.size() % elem_layout.align() == 0 &*&
        *self |-> ?self0 &*&
        RawVecInner(t, self0, elem_layout, ?alloc_id, ?ptr0, ?capacity0) &*&
        array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), _) &*&
        capacity0 < len + additional;
    @*/
    /*@
    ens thread_token(t) &*&
        *self |-> ?self1 &*&
        match result {
            Result::Ok(u) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ?ptr1, ?capacity1) &*&
                array_at_lft_(alloc_id.lft, ptr1, capacity1 * elem_layout.size(), _) &*&
                len + additional <= capacity1,
            Result::Err(e) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ptr0, capacity0) &*&
                array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), _) &*&
                <TryReserveError>.own(t, e)
        };
    @*/
    {
        if elem_layout.size() == 0 {
            // Since we return a capacity of `usize::MAX` when the type size is
            // 0, getting to here necessarily means the `RawVec` is overfull.
            let e = CapacityOverflow;
            //@ close <std::collections::TryReserveErrorKind>.own(t, e);
            return Err(e.into());
        }

        //@ close <std::collections::TryReserveErrorKind>.own(t, TryReserveErrorKind::CapacityOverflow);
        let cap = len.checked_add(additional).ok_or(CapacityOverflow)?;
        //@ leak <std::collections::TryReserveErrorKind>.own(t, TryReserveErrorKind::CapacityOverflow);

        //@ let k = begin_lifetime();
        //@ open RawVecInner(t, self0, elem_layout, alloc_id, ptr0, capacity0);
        //@ share_RawVecInner0(k, self, elem_layout, ptr0, capacity0);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_RawVecInner_(self_ref);
        //@ open_frac_borrow(k, ref_initialized_(self_ref), 1/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        let finish_grow_result;
        {
            //@ let_lft 'a = k;
            finish_grow_result = unsafe { self.finish_grow/*@::<A, 'a>@*/(cap, elem_layout) };
        }
        //@ close [f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        //@ close_frac_borrow(f, ref_initialized_(self_ref));
        //@ end_lifetime(k);
        //@ end_share_RawVecInner0(self);
        
        //@ open_points_to(self);
        
        //@ mul_mono_l(1, elem_layout.size(), cap);

        // SAFETY: Precondition passed to caller + `current_memory` does the right thing
        match core::ops::Try::branch(finish_grow_result) {
            core::ops::ControlFlow::Break(residual) => {
                //@ let self1 = *self;
                //@ close RawVecInner(t, self1, elem_layout, alloc_id, ptr0, capacity0);
                core::ops::FromResidual::from_residual(residual)
            }
            core::ops::ControlFlow::Continue(ptr) => {
                // SAFETY: layout_array would have resulted in a capacity overflow if we tried to allocate more than `isize::MAX` items
                unsafe {
                    //@ let elemLayout = elem_layout;
                    //@ assert elemLayout.repeat(cap) == some(pair(?new_layout, ?stride));
                    //@ std::alloc::Layout_repeat_some_size_aligned(elemLayout, cap);
                    //@ assert new_layout.size() == elem_layout.size() * cap;
                    //@ mul_mono_l(1, elem_layout.size(), cap);
                    self.set_ptr_and_cap(ptr, cap);
                    //@ let self1 = *self;
                    //@ std::alloc::alloc_block_in_aligned(ptr.as_ptr() as *u8);
                    //@ std::num::niche_types::UsizeNoHighBit_as_inner_new(cap);
                    //@ mul_zero(elem_layout.size(), cap);
                    //@ assert 0 <= self0.cap.as_inner();
                    //@ assert 0 <= logical_capacity(self0.cap, elem_layout.size());
                    //@ assert cap != 0;
                    //@ std::alloc::Layout_inv(new_layout);
                    //@ close RawVecInner::<A>(t, self1, elem_layout, alloc_id, _, _);
                }
                Ok(())
            }
        }
    }

    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    /// - `cap` must be greater than the current capacity
    // not marked inline(never) since we want optimizers to be able to observe the specifics of this
    // function, see tests/codegen-llvm/vec-reserve-extend.rs.
    #[cold]
    unsafe fn finish_grow<'a>(
        &'a self,
        cap: usize,
        elem_layout: Layout,
    ) -> Result<NonNull<[u8]>, TryReserveError>
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        1 <= elem_layout.size() &*&
        elem_layout.size() % elem_layout.align() == 0 &*&
        [_]RawVecInner_share_('a, t, self, elem_layout, ?alloc_id, ?ptr0, ?capacity0) &*& [?q]lifetime_token('a) &*&
        if capacity0 * elem_layout.size() == 0 {
            true
        } else {
            elem_layout.repeat(capacity0) == some(pair(?allocLayout, ?stride)) &*&
            std::alloc::alloc_block_in(alloc_id, ptr0, allocLayout)
        } &*&
        array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), _) &*&
        capacity0 <= cap;
    @*/
    /*@
    ens thread_token(t) &*& [q]lifetime_token('a) &*&
        match result {
            Result::Ok(new_ptr) =>
                elem_layout.repeat(cap) == some(pair(?allocLayout, ?stride)) &*&
                alloc_block_in(alloc_id, new_ptr.as_ptr() as *u8, allocLayout) &*&
                array_at_lft_(alloc_id.lft, new_ptr.as_ptr() as *u8, cap * elem_layout.size(), _) &*&
                cap * elem_layout.size() <= isize::MAX &*&
                std::alloc::is_valid_layout(cap * elem_layout.size(), elem_layout.align()) == true,
            Result::Err(e) =>
                if capacity0 * elem_layout.size() == 0 {
                    true
                } else {
                    elem_layout.repeat(capacity0) == some(pair(?allocLayout, ?stride)) &*&
                    std::alloc::alloc_block_in(alloc_id, ptr0, allocLayout)
                } &*&
                array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), _) &*&
                <TryReserveError>.own(currentThread, e)
        };
    @*/
    {
        //@ std::alloc::Layout_inv(elem_layout);
        
        let new_layout = layout_array(cap, elem_layout)?;
        //@ std::alloc::Layout_repeat_some_size_aligned(elem_layout, cap);
        
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_RawVecInner_(self_ref);
        //@ open_frac_borrow('a, ref_initialized_(self_ref), q/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        // SAFETY: Precondition passed to caller
        let current_memory = unsafe { (&*(self as *const RawVecInner<A>)).current_memory(elem_layout) };
        //@ close [f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        //@ close_frac_borrow(f, ref_initialized_(self_ref));
        
        //@ open RawVecInner_share_('a, t, self, elem_layout, alloc_id, ptr0, capacity0);
        //@ std::alloc::Layout_inv(elem_layout);
        /*@
        if capacity0 * elem_layout.size() != 0 {
            let elemLayout = elem_layout;
            assert elemLayout.repeat(capacity0) == some(pair(?allocLayout, ?stride));
            std::alloc::Layout_repeat_some_size_aligned(elemLayout, capacity0);
            std::alloc::Layout_inv(allocLayout);
        }
        @*/
        //@ std::alloc::Layout_size_Layout_from_size_align(capacity0 * elem_layout.size(), elem_layout.align());
        //@ std::alloc::Layout_align_Layout_from_size_align(capacity0 * elem_layout.size(), elem_layout.align());
        
        //@ open_frac_borrow('a, RawVecInner_frac_borrow_content(self, elem_layout, ptr0, capacity0), q/2);
        //@ open [?f1]RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr0, capacity0)();
        //@ let cap0 = (*self).cap;
        //@ std::num::niche_types::UsizeNoHighBit_inv(cap0);
        //@ close [f1]RawVecInner_frac_borrow_content::<A>(self, elem_layout, ptr0, capacity0)();
        //@ close_frac_borrow(f1, RawVecInner_frac_borrow_content(self, elem_layout, ptr0, capacity0));
        //@ mul_mono_l(1, elem_layout.size(), cap0.as_inner());
        //@ mul_mono_l(1, elem_layout.size(), cap);
        //@ mul_mono_l(capacity0, cap, elem_layout.size());
        
        let memory = if let Some((ptr, old_layout)) = current_memory {
            // debug_assert_eq!(old_layout.align(), new_layout.align());
            if cfg!(debug_assertions) { //~allow_dead_code // FIXME: The source location associated
                                        //with a dead `else` branch is the entire `if` statement :-(
                match (&old_layout.align(), &new_layout.align()) {
                    (left_val, right_val) =>
                    if !(*left_val == *right_val) {
                        let kind = core::panicking::AssertKind::Eq; //~allow_dead_code
                        core::panicking::assert_failed(kind, &*left_val, &*right_val, None); //~allow_dead_code
                    }
                }
            }
            unsafe {
                // The allocator checks for alignment equality
                hint::assert_unchecked(old_layout.align() == new_layout.align());
                //@ std::alloc::Layout_repeat_some_size_aligned(elem_layout, capacity0);
                //@ assert elem_layout.repeat(capacity0) == some(pair(?allocLayout, ?stride));
                //@ assert allocLayout == old_layout;
                //@ assert ptr.as_ptr() as *u8 == ptr0;
                //@ assert std::alloc::alloc_block_in(alloc_id, ptr0, allocLayout);
                //@ let alloc_ref = precreate_ref(&(*self).alloc);
                //@ std::alloc::init_ref_Allocator_share::<A>('a, t, alloc_ref);
                //@ open_frac_borrow('a, ref_initialized_::<A>(alloc_ref), q/2);
                //@ open [?f2]ref_initialized_::<A>(alloc_ref)();
                //@ std::alloc::close_Allocator_ref::<'a, A>(t, alloc_ref);
                let r = self.alloc.grow/*@::<A, 'a>@*/(ptr, old_layout, new_layout);
                //@ close [f2]ref_initialized_::<A>(alloc_ref)();
                //@ close_frac_borrow(f2, ref_initialized_::<A>(alloc_ref));
                //@ leak Allocator(_, _, _);
                r
            }
        } else {
            //@ let alloc_ref = precreate_ref(&(*self).alloc);
            //@ std::alloc::init_ref_Allocator_share::<A>('a, t, alloc_ref);
            //@ open_frac_borrow('a, ref_initialized_::<A>(alloc_ref), q/2);
            //@ open [?f2]ref_initialized_::<A>(alloc_ref)();
            //@ std::alloc::close_Allocator_ref::<'a, A>(t, alloc_ref);
            let r = self.alloc.allocate/*@::<A, 'a>@*/(new_layout);
            //@ close [f2]ref_initialized_::<A>(alloc_ref)();
            //@ close_frac_borrow(f2, ref_initialized_::<A>(alloc_ref));
            //@ leak Allocator(_, _, _);
            r
        };

        let new_layout_ref = &new_layout;
        match memory {
            Ok(ptr) => Ok(ptr),
            Err(err) => {
                let e = AllocError { layout: *new_layout_ref, non_exhaustive: () };
                //@ std::alloc::close_Layout_own(t, new_layout);
                //@ close_tuple_0_own(t);
                //@ close <std::collections::TryReserveErrorKind>.own(t, e);
                Err(e.into())
            }
        }
    }


    /// # Safety
    /// - `elem_layout` must be valid for `self`, i.e. it must be the same `elem_layout` used to
    ///   initially construct `self`
    /// - `elem_layout`'s size must be a multiple of its alignment
    /// - `cap` must be less than or equal to `self.capacity(elem_layout.size())`
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    unsafe fn shrink(&mut self, cap: usize, elem_layout: Layout) -> Result<(), TryReserveError>
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        elem_layout.size() % elem_layout.align() == 0 &*&
        *self |-> ?self0 &*&
        RawVecInner(t, self0, elem_layout, ?alloc_id, ?ptr0, ?capacity0) &*&
        array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), ?bs0);
    @*/
    /*@
    ens thread_token(t) &*&
        *self |-> ?self1 &*&
        match result {
            Result::Ok(u) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ?ptr1, ?capacity1) &*&
                array_at_lft_(alloc_id.lft, ptr1, capacity1 * elem_layout.size(), take(capacity1 * elem_layout.size(), bs0)) &*&
                cap <= capacity0 &*&
                cap <= capacity1 &*&
                capacity1 == if elem_layout.size() == 0 { usize::MAX } else { cap },
            Result::Err(e) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ptr0, capacity0) &*&
                array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), bs0) &*&
                <TryReserveError>.own(t, e)
        };
    @*/
    {
        //@ let k = begin_lifetime();
        //@ share_RawVecInner(k, self);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_RawVecInner_(self_ref);
        //@ open_frac_borrow(k, ref_initialized_(self_ref), 1/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        let capacity = self.capacity(elem_layout.size());
        //@ close [f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        //@ close_frac_borrow(f, ref_initialized_(self_ref));
        //@ end_lifetime(k);
        //@ end_share_RawVecInner(self);
        assert!(cap <= capacity, "Tried to shrink to a larger capacity");
        // SAFETY: Just checked this isn't trying to grow
        unsafe { self.shrink_unchecked(cap, elem_layout) }
    }

    /// `shrink`, but without the capacity check.
    ///
    /// This is split out so that `shrink` can inline the check, since it
    /// optimizes out in things like `shrink_to_fit`, without needing to
    /// also inline all this code, as doing that ends up failing the
    /// `vec-shrink-panic` codegen test when `shrink_to_fit` ends up being too
    /// big for LLVM to be willing to inline.
    ///
    /// # Safety
    /// `cap <= self.capacity()`
    #[cfg(not(no_global_oom_handling))]
    unsafe fn shrink_unchecked(
        &mut self,
        cap: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveError>
    /*@
    req thread_token(?t) &*& t == currentThread &*&
        elem_layout.size() % elem_layout.align() == 0 &*&
        *self |-> ?self0 &*&
        RawVecInner(t, self0, elem_layout, ?alloc_id, ?ptr0, ?capacity0) &*&
        array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), ?bs0) &*&
        cap <= capacity0;
    @*/
    /*@
    ens thread_token(t) &*&
        *self |-> ?self1 &*&
        match result {
            Result::Ok(u) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ?ptr1, ?capacity1) &*&
                array_at_lft_(alloc_id.lft, ptr1, capacity1 * elem_layout.size(), take(capacity1 * elem_layout.size(), bs0)) &*&
                cap <= capacity1 &*&
                capacity1 == if elem_layout.size() == 0 { usize::MAX } else { cap },
            Result::Err(e) =>
                RawVecInner(t, self1, elem_layout, alloc_id, ptr0, capacity0) &*&
                array_at_lft_(alloc_id.lft, ptr0, capacity0 * elem_layout.size(), bs0) &*&
                <TryReserveError>.own(t, e)
        };
    @*/
    {
        //@ let k = begin_lifetime();
        //@ share_RawVecInner(k, self);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_RawVecInner_(self_ref);
        //@ open_frac_borrow(k, ref_initialized_(self_ref), 1/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        // SAFETY: Precondition passed to caller
        let current_memory = unsafe { self.current_memory(elem_layout) };
        //@ close [f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        //@ close_frac_borrow(f, ref_initialized_(self_ref));
        //@ end_lifetime(k);
        //@ end_share_RawVecInner(self);
        
        let (ptr, layout) =
            if let Some(mem) = current_memory { mem } else {
                //@ std::alloc::Layout_inv(elem_layout);
                //@ mul_zero(capacity0, elem_layout.size());
                //@ RawVecInner_inv2();
                return Ok(())
            };
            
        //@ open_points_to(self);

        //@ open RawVecInner(t, ?self01, elem_layout, alloc_id, ptr0, capacity0);
        //@ assert self01.ptr.as_non_null_ptr().as_ptr() == ptr0;
        //@ std::alloc::Layout_inv(elem_layout);
        /*@
        if capacity0 * elem_layout.size() != 0 {
            let elemLayout = elem_layout;
            assert elemLayout.repeat(capacity0) == some(pair(?allocLayout, ?stride));
            std::alloc::Layout_repeat_some_size_aligned(elemLayout, capacity0);
            std::alloc::Layout_inv(allocLayout);
        }
        @*/
        //@ std::alloc::Layout_size_Layout_from_size_align(capacity0 * elem_layout.size(), elem_layout.align());
        //@ std::alloc::Layout_align_Layout_from_size_align(capacity0 * elem_layout.size(), elem_layout.align());
        
        // If shrinking to 0, deallocate the buffer. We don't reach this point
        // for the T::IS_ZST case since current_memory() will have returned
        // None.
        if cap == 0 {
            //@ let alloc_ref = precreate_ref(&(*self).alloc);
            //@ let k1 = begin_lifetime();
            unsafe {
                //@ let_lft 'a = k1;
                //@ std::alloc::init_ref_Allocator_at_lifetime::<'a, A>(alloc_ref);
                self.alloc.deallocate/*@::<A, 'a>@*/(ptr, layout);
                //@ leak Allocator(_, _, _);
            };
            //@ end_lifetime(k1);
            //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
            self.ptr =
                unsafe { Unique::new_unchecked(ptr::without_provenance_mut(elem_layout.align())) };
            self.cap = ZERO_CAP;
            //@ let ptr1_ = (*self).ptr;
            //@ assert ptr1_.as_non_null_ptr().as_ptr() as usize == elem_layout.align();
            //@ div_rem_nonneg_unique(elem_layout.align(), elem_layout.align(), 1, 0);
            //@ std::alloc::Layout_repeat_0_intro(elem_layout);
            //@ close RawVecInner(t, *self, elem_layout, alloc_id, _, _);
        } else {
            let ptr = unsafe {
                // Layout cannot overflow here because it would have
                // overflowed earlier when capacity was larger.
                //@ mul_mono_l(cap, capacity0, elem_layout.size());
                let new_size = elem_layout.size().unchecked_mul(cap);
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                //@ let alloc_ref = precreate_ref(&(*self).alloc);
                //@ let k1 = begin_lifetime();
                let r;
                {
                    //@ let_lft 'a = k1;
                    //@ std::alloc::init_ref_Allocator_at_lifetime::<'a, A>(alloc_ref);
                    r = self.alloc.shrink/*@::<A, 'a>@*/(ptr, layout, new_layout);
                    //@ leak Allocator(_, _, _);
                };
                //@ end_lifetime(k1);
                //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
                let new_layout_ref = &new_layout;
                match r {
                    Ok(ptr1) => Ok(ptr1),
                    Err(err) => {
                        //@ close RawVecInner(t, *self, elem_layout, alloc_id, ptr0, capacity0);
                        let e = AllocError { layout: *new_layout_ref, non_exhaustive: () };
                        //@ std::alloc::close_Layout_own(t, new_layout);
                        //@ close_tuple_0_own(t);
                        //@ close <std::collections::TryReserveErrorKind>.own(t, e);
                        Err(e)
                    }
                }?
            };
            // SAFETY: if the allocation is valid, then the capacity is too
            unsafe {
                //@ std::num::niche_types::UsizeNoHighBit_inv(self01.cap);
                self.set_ptr_and_cap(ptr, cap);
                //@ std::alloc::alloc_block_in_aligned(ptr_1.as_ptr() as *u8);
                //@ mul_zero(cap, elem_layout.size());
                //@ std::alloc::Layout_repeat_size_aligned_intro(elem_layout, cap);
                //@ close RawVecInner(t, *self, elem_layout, alloc_id, _, _);
            }
        }
        Ok(())
    }

    /// # Safety
    ///
    /// This function deallocates the owned allocation, but does not update `ptr` or `cap` to
    /// prevent double-free or use-after-free. Essentially, do not do anything with the caller
    /// after this function returns.
    /// Ideally this function would take `self` by move, but it cannot because it exists to be
    /// called from a `Drop` impl.
    unsafe fn deallocate(&mut self, elem_layout: Layout)
    /*@
    req thread_token(?t) &*&
        *self |-> ?self0 &*&
        RawVecInner(t, self0, elem_layout, ?alloc_id, ?ptr_, ?capacity) &*&
        elem_layout.size() % elem_layout.align() == 0 &*&
        array_at_lft_(alloc_id.lft, ptr_, capacity * elem_layout.size(), _);
    @*/
    //@ ens thread_token(t) &*& *self |-> ?self1 &*& <RawVecInner<A>>.own(t, self1);
    //@ on_unwind_ens thread_token(t) &*& *self |-> ?self1 &*& <RawVecInner<A>>.own(t, self1);
    {
        //@ let k = begin_lifetime();
        //@ share_RawVecInner(k, self);
        //@ let self_ref = precreate_ref(self);
        //@ init_ref_RawVecInner_(self_ref);
        //@ open_frac_borrow(k, ref_initialized_(self_ref), 1/2);
        //@ open [?f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        // SAFETY: Precondition passed to caller
        let current_memory = unsafe { self.current_memory(elem_layout) };
        //@ close [f]ref_initialized_::<RawVecInner<A>>(self_ref)();
        //@ close_frac_borrow(f, ref_initialized_(self_ref));
        //@ end_lifetime(k);
        //@ end_share_RawVecInner(self);
        
        //@ open_points_to(self);
        //@ open RawVecInner(t, _, elem_layout, alloc_id, ptr_, capacity);
        if let Some((ptr, layout)) = current_memory {
            //@ let alloc_ref = precreate_ref(&(*self).alloc);
            //@ let k1 = begin_lifetime();
            unsafe {
                //@ let_lft 'a = k1;
                //@ std::alloc::init_ref_Allocator_at_lifetime::<'a, A>(alloc_ref);
                //@ std::alloc::Layout_repeat_some_size_aligned(elem_layout, capacity);
                //@ assert capacity * elem_layout.size() == layout.size();
                self.alloc.deallocate/*@::<A, 'a>@*/(ptr, layout);
            }
            //@ end_lifetime(k1);
            //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
        }
        //@ std::alloc::Allocator_to_own((*self).alloc);
        //@ close RawVecInner0(*self, elem_layout, ptr_, capacity);
        //@ close <RawVecInner<A>>.own(t, *self);
    }
}

// Central function for reserve error handling.
#[cfg(not(no_global_oom_handling))]
#[cold]
#[optimize(size)]
fn handle_error(e: TryReserveError) -> !
//@ req thread_token(?t);
//@ ens false;
{
    match e.kind() {
        CapacityOverflow => capacity_overflow(),
        AllocError { layout, .. } => handle_alloc_error(layout),
    }
}

#[inline]
fn layout_array(cap: usize, elem_layout: Layout) -> Result<Layout, TryReserveError>
//@ req thread_token(currentThread);
/*@
ens thread_token(currentThread) &*&
    match result {
        Result::Ok(layout) => elem_layout.repeat(cap) == some(pair(layout, ?stride)),
        Result::Err(err) => <TryReserveError>.own(currentThread, err)
    };
@*/
/*@
safety_proof {
    leak <Layout>.own(_t, elem_layout);
    let result = call();
    match result {
        Result::Ok(layout) => { std::alloc::close_Layout_own(_t, layout); }
        Result::Err(e) => {}
    }
    close <std::result::Result<Layout, TryReserveError>>.own(_t, result);
}
@*/
{
    let r = match elem_layout.repeat(cap) {
        Ok(info) => Ok(info.0),
        Err(err) => Err(err)
    };
    let r2 = match r {
        Ok(l) => Ok(l),
        Err(err) => {
            let e = CapacityOverflow;
            //@ close <std::collections::TryReserveErrorKind>.own(currentThread, e);
            Err(e.into())
        }
    };
    r2
}
