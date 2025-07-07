#![unstable(feature = "raw_vec_internals", reason = "unstable const warnings", issue = "none")]
#![cfg_attr(test, allow(dead_code))]

//@ use std::num::{niche_types::UsizeNoHighBit, NonZero};
//@ use std::ptr::{NonNull, NonNull_ptr, Unique, Alignment};
//@ use std::alloc::{Layout, Allocator, alloc_block_in};
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

#[cfg(test)]
mod tests;

// One central function responsible for reporting capacity overflows. This'll
// ensure that the code generation related to these panics is minimal as there's
// only one location which panics rather than a bunch throughout the module.
#[cfg(not(no_global_oom_handling))]
#[cfg_attr(not(feature = "panic_immediate_abort"), inline(never))]
#[track_caller]
fn capacity_overflow() -> ! {
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

//@ fix Cap_new_(n: usize) -> UsizeNoHighBit { UsizeNoHighBit::new_(n) }
//@ fix Cap_as_inner_(cap: UsizeNoHighBit) -> usize { UsizeNoHighBit::as_inner_(cap) }

const ZERO_CAP: Cap = unsafe { Cap::new_unchecked(0) };

/// `Cap(cap)`, except if `T` is a ZST then `Cap::ZERO`.
///
/// # Safety: cap must be <= `isize::MAX`.
unsafe fn new_cap<T>(cap: usize) -> Cap {
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

pred RawVecInner0(alloc_id: any, u: Unique<u8>, cap: UsizeNoHighBit, elemLayout: Layout; ptr: *u8, allocSize: usize) =
    allocSize == Layout::size_(elemLayout) * Cap_as_inner_(cap) &*&
    ptr == NonNull_ptr(Unique::non_null_(u)) &*&
    ptr != 0 &*&
    ptr as usize % Layout::align_(elemLayout) == 0 &*&
    if allocSize == 0 {
        true
    } else {
        allocSize <= isize::MAX - isize::MAX % Layout::align_(elemLayout) &*&
        alloc_block_in(alloc_id, ptr, Layout::from_size_align_(allocSize, Layout::align_(elemLayout)))
    };

pred RawVecInner<A>(t: thread_id_t, self: RawVecInner<A>, elemLayout: Layout, ptr: *u8, allocSize: usize) =
    Allocator(t, self.alloc, ?alloc_id) &*&
    RawVecInner0(alloc_id, self.ptr, self.cap, elemLayout, ptr, allocSize);

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
    #[track_caller]
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self { inner: RawVecInner::with_capacity(capacity, T::LAYOUT), _marker: PhantomData }
    }

    /// Like `with_capacity`, but guarantees the buffer is zeroed.
    #[cfg(not(any(no_global_oom_handling, test)))]
    #[must_use]
    #[inline]
    #[track_caller]
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
    #[track_caller]
    fn with_capacity(capacity: usize, elem_layout: Layout) -> Self {
        match Self::try_allocate_in(capacity, AllocInit::Uninitialized, Global, elem_layout) {
            Ok(res) => res,
            Err(err) => handle_error(err),
        }
    }
}

// Tiny Vecs are dumb. Skip to:
// - 8 if the element size is 1, because any heap allocators is likely
//   to round up a request of less than 8 bytes to at least 8 bytes.
// - 4 if elements are moderate-sized (<= 1 KiB).
// - 1 otherwise, to avoid wasting too much space for very short Vecs.
const fn min_non_zero_cap(size: usize) -> usize {
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
    pub(crate) const fn new_in(alloc: A) -> Self {
        Self { inner: RawVecInner::new_in(alloc, Alignment::of::<T>()), _marker: PhantomData }
    }

    /// Like `with_capacity`, but parameterized over the choice of
    /// allocator for the returned `RawVec`.
    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[track_caller]
    pub(crate) fn with_capacity_in(capacity: usize, alloc: A) -> Self {
        Self {
            inner: RawVecInner::with_capacity_in(capacity, alloc, T::LAYOUT),
            _marker: PhantomData,
        }
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
    #[track_caller]
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
    pub(crate) unsafe fn into_box(self, len: usize) -> Box<[MaybeUninit<T>], A> {
        // Sanity-check one half of the safety requirement (we cannot check the other half).
        debug_assert!(
            len <= self.capacity(),
            "`len` must be smaller than or equal to `self.capacity()`"
        );

        let me = ManuallyDrop::new(self);
        unsafe {
            let slice = ptr::slice_from_raw_parts_mut(me.ptr() as *mut MaybeUninit<T>, len);
            Box::from_raw_in(slice, ptr::read(&me.inner.alloc))
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
    pub(crate) unsafe fn from_raw_parts_in(ptr: *mut T, capacity: usize, alloc: A) -> Self {
        // SAFETY: Precondition passed to the caller
        unsafe {
            let ptr = ptr.cast();
            let capacity = new_cap::<T>(capacity);
            Self {
                inner: RawVecInner::from_raw_parts_in(ptr, capacity, alloc),
                _marker: PhantomData,
            }
        }
    }

    /// A convenience method for hoisting the non-null precondition out of [`RawVec::from_raw_parts_in`].
    ///
    /// # Safety
    ///
    /// See [`RawVec::from_raw_parts_in`].
    #[inline]
    pub(crate) unsafe fn from_nonnull_in(ptr: NonNull<T>, capacity: usize, alloc: A) -> Self {
        // SAFETY: Precondition passed to the caller
        unsafe {
            let ptr = ptr.cast();
            let capacity = new_cap::<T>(capacity);
            Self { inner: RawVecInner::from_nonnull_in(ptr, capacity, alloc), _marker: PhantomData }
        }
    }

    /// Gets a raw pointer to the start of the allocation. Note that this is
    /// `Unique::dangling()` if `capacity == 0` or `T` is zero-sized. In the former case, you must
    /// be careful.
    #[inline]
    pub(crate) const fn ptr(&self) -> *mut T {
        self.inner.ptr()
    }

    #[inline]
    pub(crate) const fn non_null(&self) -> NonNull<T> {
        self.inner.non_null()
    }

    /// Gets the capacity of the allocation.
    ///
    /// This will always be `usize::MAX` if `T` is zero-sized.
    #[inline]
    pub(crate) const fn capacity(&self) -> usize {
        self.inner.capacity(size_of::<T>())
    }

    /// Returns a shared reference to the allocator backing this `RawVec`.
    #[inline]
    pub(crate) fn allocator(&self) -> &A {
        self.inner.allocator()
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
    #[track_caller]
    pub(crate) fn reserve(&mut self, len: usize, additional: usize) {
        self.inner.reserve(len, additional, T::LAYOUT)
    }

    /// A specialized version of `self.reserve(len, 1)` which requires the
    /// caller to ensure `len == self.capacity()`.
    #[cfg(not(no_global_oom_handling))]
    #[inline(never)]
    #[track_caller]
    pub(crate) fn grow_one(&mut self) {
        self.inner.grow_one(T::LAYOUT)
    }

    /// The same as `reserve`, but returns on errors instead of panicking or aborting.
    pub(crate) fn try_reserve(
        &mut self,
        len: usize,
        additional: usize,
    ) -> Result<(), TryReserveError> {
        self.inner.try_reserve(len, additional, T::LAYOUT)
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
    #[track_caller]
    pub(crate) fn reserve_exact(&mut self, len: usize, additional: usize) {
        self.inner.reserve_exact(len, additional, T::LAYOUT)
    }

    /// The same as `reserve_exact`, but returns on errors instead of panicking or aborting.
    pub(crate) fn try_reserve_exact(
        &mut self,
        len: usize,
        additional: usize,
    ) -> Result<(), TryReserveError> {
        self.inner.try_reserve_exact(len, additional, T::LAYOUT)
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
    #[track_caller]
    #[inline]
    pub(crate) fn shrink_to_fit(&mut self, cap: usize) {
        self.inner.shrink_to_fit(cap, T::LAYOUT)
    }
}

unsafe impl<#[may_dangle] T, A: Allocator> Drop for RawVec<T, A> {
    /// Frees the memory owned by the `RawVec` *without* trying to drop its contents.
    fn drop(&mut self) {
        // SAFETY: We are in a Drop impl, self.inner will not be used again.
        unsafe { self.inner.deallocate(T::LAYOUT) }
    }
}

impl<A: Allocator> RawVecInner<A> {
    #[inline]
    const fn new_in(alloc: A, align: Alignment) -> Self
    //@ req exists::<usize>(?elemSize) &*& thread_token(?t) &*& Allocator(t, alloc, ?alloc_id) &*& std::alloc::is_valid_layout(elemSize, NonZero::get_(Alignment::as_nonzero_(align))) == true;
    //@ ens thread_token(t) &*& RawVecInner(t, result, Layout::from_size_align_(elemSize, NonZero::get_(Alignment::as_nonzero_(align))), ?ptr, 0) &*& ptr[..0] |-> _;
    //@ on_unwind_ens false;
    //@ safety_proof { assume(false); }
    {
        let ptr = Unique::from_non_null(NonNull::without_provenance(align.as_nonzero()));
        // `cap: 0` means "unallocated". zero-sized types are ignored.
        let cap = ZERO_CAP;
        //@ let layout = Layout::from_size_align_(elemSize, NonZero::get_(Alignment::as_nonzero_(align)));
        let r = Self { ptr, cap, alloc };
        //@ div_rem_nonneg_unique(NonZero::get_(Alignment::as_nonzero_(align)), NonZero::get_(Alignment::as_nonzero_(align)), 1, 0);
        //@ close RawVecInner0(alloc_id, ptr, cap, layout, _, 0);
        //@ close RawVecInner(t, r, layout, _, 0);
        //@ std::num::NonZero_usize_limits(Alignment::as_nonzero_(align));
        //@ close array::<u8>(NonNull_ptr(Unique::non_null_(ptr)), 0, nil);
        r
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[track_caller]
    fn with_capacity_in(capacity: usize, alloc: A, elem_layout: Layout) -> Self {
        match Self::try_allocate_in(capacity, AllocInit::Uninitialized, alloc, elem_layout) {
            Ok(this) => {
                unsafe {
                    // Make it more obvious that a subsequent Vec::reserve(capacity) will not allocate.
                    hint::assert_unchecked(!this.needs_to_grow(0, capacity, elem_layout));
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
    #[track_caller]
    fn with_capacity_zeroed_in(capacity: usize, alloc: A, elem_layout: Layout) -> Self {
        match Self::try_allocate_in(capacity, AllocInit::Zeroed, alloc, elem_layout) {
            Ok(res) => res,
            Err(err) => handle_error(err),
        }
    }

    fn try_allocate_in(
        capacity: usize,
        init: AllocInit,
        alloc: A,
        elem_layout: Layout,
    ) -> Result<Self, TryReserveError>
    //@ req thread_token(?t) &*& Allocator(t, alloc, ?alloc_id) &*& t == currentThread &*& Layout::size_(elem_layout) % Layout::align_(elem_layout) == 0;
    /*@
    ens thread_token(t) &*&
        match result {
            Result::Ok(v) =>
                RawVecInner(t, v, elem_layout, ?ptr, ?allocSize) &*&
                match init {
                    raw_vec::AllocInit::Uninitialized => ptr[..allocSize] |-> _,
                    raw_vec::AllocInit::Zeroed => ptr[..allocSize] |-> ?bs &*& forall(bs, (eq)(0)) == true
                },
            Result::Err(e) => <std::collections::TryReserveError>.own(t, e)
        };
    @*/
    //@ safety_proof { assume(false); }
    {
        //@ std::alloc::Layout_inv(elem_layout);
        
        // We avoid `unwrap_or_else` here because it bloats the amount of
        // LLVM IR generated.
        let layout = match layout_array(capacity, elem_layout) {
            Ok(layout) => layout,
            Err(_) => {
                //@ std::alloc::Allocator_to_own(alloc);
                //@ close <std::collections::TryReserveErrorKind>.own(currentThread, std::collections::TryReserveErrorKind::CapacityOverflow);
                return Err(CapacityOverflow.into())
            },
        };

        // Don't allocate here because `Drop` will not deallocate when `capacity` is 0.
        {
            //@ let layout_ref = precreate_ref(&layout);
            //@ std::alloc::init_ref_Layout(layout_ref, 1/2);
            let layout_size = layout.size();
            //@ std::alloc::end_ref_Layout(layout_ref);
            if layout_size == 0 {
                //@ let elem_layout_ref = precreate_ref(&elem_layout);
                //@ std::alloc::init_ref_Layout(elem_layout_ref, 1/2);
                let elem_layout_alignment = elem_layout.alignment();
                //@ std::alloc::end_ref_Layout(elem_layout_ref);
                //@ close exists(Layout::size_(elem_layout));
                return Ok(Self::new_in(alloc, elem_layout_alignment));
            }
        }
        
        {
            //@ let layout_ref2 = precreate_ref(&layout);
            //@ std::alloc::init_ref_Layout(layout_ref2, 1/2);
            let layout_size = layout.size();
            //@ std::alloc::end_ref_Layout(layout_ref2);
            if let Err(err) = alloc_guard(layout_size) {
                //@ std::alloc::Allocator_to_own(alloc);
                return Err(err);
            }
        }

        let result = match init {
            AllocInit::Uninitialized => {
                let r;
                //@ let alloc_ref = precreate_ref(&alloc);
                //@ let k = begin_lifetime();
                unsafe {
                    //@ let_lft 'a = k;
                    //@ std::alloc::init_ref_Allocator_at_lifetime::<'a, A>(alloc_ref);
                    r = alloc.allocate(layout);
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
                    r = alloc.allocate_zeroed(layout);
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
        //@ std::alloc::Layout_inv(elem_layout);
        //@ assert 0 <= Layout::size_(elem_layout);
        //@ assert Layout::size_(elem_layout) != 0;
        //@ mul_mono_l(1, Layout::size_(elem_layout), capacity);
        //@ assert capacity * Layout::size_(elem_layout) <= isize::MAX;
        let res = Self {
            ptr: Unique::from(ptr.cast()),
            cap: unsafe { Cap::new_unchecked(capacity) },
            alloc,
        };
        //@ assert res.ptr == Unique::from_non_null_(NonNull::new_(NonNull_ptr(ptr.ptr)));
        //@ std::ptr::NonNull_ptr_nonnull(ptr.ptr);
        //@ std::ptr::Unique_non_null__from_non_null_(ptr.ptr);
        //@ std::ptr::NonNull_new_ptr(ptr.ptr);
        //@ assert Unique::non_null_(res.ptr) == ptr.ptr;
        //@ assert Layout::align_(layout) == Layout::align_(elem_layout);
        //@ std::alloc::alloc_block_in_aligned(NonNull_ptr(ptr.ptr));
        //@ close RawVecInner0(alloc_id, res.ptr, res.cap, elem_layout, _, _);
        //@ close RawVecInner(t, res, elem_layout, NonNull_ptr(ptr.ptr), _);
        Ok(res)
    }

    #[inline]
    unsafe fn from_raw_parts_in(ptr: *mut u8, cap: Cap, alloc: A) -> Self {
        Self { ptr: unsafe { Unique::new_unchecked(ptr) }, cap, alloc }
    }

    #[inline]
    unsafe fn from_nonnull_in(ptr: NonNull<u8>, cap: Cap, alloc: A) -> Self {
        Self { ptr: Unique::from(ptr), cap, alloc }
    }

    #[inline]
    const fn ptr<T>(&self) -> *mut T {
        self.non_null::<T>().as_ptr()
    }

    #[inline]
    const fn non_null<T>(&self) -> NonNull<T> {
        self.ptr.cast().as_non_null_ptr()
    }

    #[inline]
    const fn capacity(&self, elem_size: usize) -> usize {
        if elem_size == 0 { usize::MAX } else { self.cap.as_inner() }
    }

    #[inline]
    fn allocator(&self) -> &A {
        &self.alloc
    }

    #[inline]
    fn current_memory(&self, elem_layout: Layout) -> Option<(NonNull<u8>, Layout)>
    //@ req [?fu]((*self).ptr |-> ?u) &*& [?fc]((*self).cap |-> ?cap) &*& [?fv]RawVecInner0(?alloc_id, u, cap, elem_layout, ?ptr, ?allocSize);
    /*@
    ens [fu]((*self).ptr |-> u) &*& [fc]((*self).cap |-> cap) &*& [fv]RawVecInner0(alloc_id, u, cap, elem_layout, ptr, allocSize) &*&
        if allocSize == 0 {
            result == Option::None
        } else {
            result == Option::Some(std_tuple_2_::<NonNull<u8>, Layout> {0: Unique::non_null_(u), 1: Layout::from_size_align_(allocSize, Layout::align_(elem_layout))})
        };
    @*/
    //@ on_unwind_ens false;
    //@ safety_proof { assume(false); }
    {
        //@ open RawVecInner0(alloc_id, u, cap, elem_layout, ptr, allocSize);
        //@ let elem_layout_ref = precreate_ref(&elem_layout);
        //@ std::alloc::init_ref_Layout(elem_layout_ref, 1/2);
        if elem_layout.size() == 0 || self.cap.as_inner() == 0 {
            //@ std::alloc::end_ref_Layout(elem_layout_ref);
            //@ close [fv]RawVecInner0(alloc_id, u, cap, elem_layout, ptr, allocSize);
            None
        } else {
            //@ std::alloc::end_ref_Layout(elem_layout_ref);
            // We could use Layout::array here which ensures the absence of isize and usize overflows
            // and could hypothetically handle differences between stride and size, but this memory
            // has already been allocated so we know it can't overflow and currently Rust does not
            // support such types. So we can do better by skipping some checks and avoid an unwrap.
            unsafe {
                //@ let elem_layout_ref1 = precreate_ref(&elem_layout);
                //@ std::alloc::init_ref_Layout(elem_layout_ref1, 1/2);
                //@ std::alloc::Layout_inv(elem_layout);
                //@ is_power_of_2_pos(Layout::align_(elem_layout));
                //@ div_rem_nonneg(isize::MAX, Layout::align_(elem_layout));
                let alloc_size = elem_layout.size().unchecked_mul(self.cap.as_inner());
                //@ if allocSize == 0 { mul_zero(Layout::size_(elem_layout), Cap_as_inner_(cap)); assert false; }
                //@ std::alloc::end_ref_Layout(elem_layout_ref1);
                //@ let elem_layout_ref2 = precreate_ref(&elem_layout);
                //@ std::alloc::init_ref_Layout(elem_layout_ref2, 1/2);
                let layout = Layout::from_size_align_unchecked(alloc_size, elem_layout.align());
                //@ std::alloc::end_ref_Layout(elem_layout_ref2);
                //@ close [fv]RawVecInner0(alloc_id, u, cap, elem_layout, ptr, alloc_size);
                Some((self.ptr.into(), layout))
            }
        }
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[track_caller]
    fn reserve(&mut self, len: usize, additional: usize, elem_layout: Layout) {
        // Callers expect this function to be very cheap when there is already sufficient capacity.
        // Therefore, we move all the resizing and error-handling logic from grow_amortized and
        // handle_reserve behind a call, while making sure that this function is likely to be
        // inlined as just a comparison and a call if the comparison fails.
        #[cold]
        fn do_reserve_and_handle<A: Allocator>(
            slf: &mut RawVecInner<A>,
            len: usize,
            additional: usize,
            elem_layout: Layout,
        ) {
            if let Err(err) = slf.grow_amortized(len, additional, elem_layout) {
                handle_error(err);
            }
        }

        if self.needs_to_grow(len, additional, elem_layout) {
            do_reserve_and_handle(self, len, additional, elem_layout);
        }
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[track_caller]
    fn grow_one(&mut self, elem_layout: Layout) {
        if let Err(err) = self.grow_amortized(self.cap.as_inner(), 1, elem_layout) {
            handle_error(err);
        }
    }

    fn try_reserve(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveError> {
        if self.needs_to_grow(len, additional, elem_layout) {
            self.grow_amortized(len, additional, elem_layout)?;
        }
        unsafe {
            // Inform the optimizer that the reservation has succeeded or wasn't needed
            hint::assert_unchecked(!self.needs_to_grow(len, additional, elem_layout));
        }
        Ok(())
    }

    #[cfg(not(no_global_oom_handling))]
    #[track_caller]
    fn reserve_exact(&mut self, len: usize, additional: usize, elem_layout: Layout) {
        if let Err(err) = self.try_reserve_exact(len, additional, elem_layout) {
            handle_error(err);
        }
    }

    fn try_reserve_exact(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveError> {
        if self.needs_to_grow(len, additional, elem_layout) {
            self.grow_exact(len, additional, elem_layout)?;
        }
        unsafe {
            // Inform the optimizer that the reservation has succeeded or wasn't needed
            hint::assert_unchecked(!self.needs_to_grow(len, additional, elem_layout));
        }
        Ok(())
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    #[track_caller]
    fn shrink_to_fit(&mut self, cap: usize, elem_layout: Layout) {
        if let Err(err) = self.shrink(cap, elem_layout) {
            handle_error(err);
        }
    }

    #[inline]
    fn needs_to_grow(&self, len: usize, additional: usize, elem_layout: Layout) -> bool {
        additional > self.capacity(elem_layout.size()).wrapping_sub(len)
    }

    #[inline]
    unsafe fn set_ptr_and_cap(&mut self, ptr: NonNull<[u8]>, cap: usize) {
        // Allocators currently return a `NonNull<[u8]>` whose length matches
        // the size requested. If that ever changes, the capacity here should
        // change to `ptr.len() / size_of::<T>()`.
        self.ptr = Unique::from(ptr.cast());
        self.cap = unsafe { Cap::new_unchecked(cap) };
    }

    fn grow_amortized(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveError> {
        // This is ensured by the calling contexts.
        debug_assert!(additional > 0);

        if elem_layout.size() == 0 {
            // Since we return a capacity of `usize::MAX` when `elem_size` is
            // 0, getting to here necessarily means the `RawVec` is overfull.
            return Err(CapacityOverflow.into());
        }

        // Nothing we can really do about these checks, sadly.
        let required_cap = len.checked_add(additional).ok_or(CapacityOverflow)?;

        // This guarantees exponential growth. The doubling cannot overflow
        // because `cap <= isize::MAX` and the type of `cap` is `usize`.
        let cap = cmp::max(self.cap.as_inner() * 2, required_cap);
        let cap = cmp::max(min_non_zero_cap(elem_layout.size()), cap);

        let new_layout = layout_array(cap, elem_layout)?;

        let ptr = finish_grow(new_layout, self.current_memory(elem_layout), &mut self.alloc)?;
        // SAFETY: finish_grow would have resulted in a capacity overflow if we tried to allocate more than `isize::MAX` items

        unsafe { self.set_ptr_and_cap(ptr, cap) };
        Ok(())
    }

    fn grow_exact(
        &mut self,
        len: usize,
        additional: usize,
        elem_layout: Layout,
    ) -> Result<(), TryReserveError> {
        if elem_layout.size() == 0 {
            // Since we return a capacity of `usize::MAX` when the type size is
            // 0, getting to here necessarily means the `RawVec` is overfull.
            return Err(CapacityOverflow.into());
        }

        let cap = len.checked_add(additional).ok_or(CapacityOverflow)?;
        let new_layout = layout_array(cap, elem_layout)?;

        let ptr = finish_grow(new_layout, self.current_memory(elem_layout), &mut self.alloc)?;
        // SAFETY: finish_grow would have resulted in a capacity overflow if we tried to allocate more than `isize::MAX` items
        unsafe {
            self.set_ptr_and_cap(ptr, cap);
        }
        Ok(())
    }

    #[cfg(not(no_global_oom_handling))]
    #[inline]
    fn shrink(&mut self, cap: usize, elem_layout: Layout) -> Result<(), TryReserveError> {
        assert!(cap <= self.capacity(elem_layout.size()), "Tried to shrink to a larger capacity");
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
    ) -> Result<(), TryReserveError> {
        let (ptr, layout) =
            if let Some(mem) = self.current_memory(elem_layout) { mem } else { return Ok(()) };

        // If shrinking to 0, deallocate the buffer. We don't reach this point
        // for the T::IS_ZST case since current_memory() will have returned
        // None.
        if cap == 0 {
            unsafe { self.alloc.deallocate(ptr, layout) };
            self.ptr =
                unsafe { Unique::new_unchecked(ptr::without_provenance_mut(elem_layout.align())) };
            self.cap = ZERO_CAP;
        } else {
            let ptr = unsafe {
                // Layout cannot overflow here because it would have
                // overflowed earlier when capacity was larger.
                let new_size = elem_layout.size().unchecked_mul(cap);
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                self.alloc
                    .shrink(ptr, layout, new_layout)
                    .map_err(|_| AllocError { layout: new_layout, non_exhaustive: () })?
            };
            // SAFETY: if the allocation is valid, then the capacity is too
            unsafe {
                self.set_ptr_and_cap(ptr, cap);
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
    //@ req thread_token(?t) &*& *self |-> ?self0 &*& RawVecInner(t, self0, elem_layout, ?ptr_, ?allocSize) &*& ptr_[..allocSize] |-> _;
    //@ ens thread_token(t) &*& (*self).ptr |-> _ &*& (*self).cap |-> _ &*& (*self).alloc |-> ?alloc &*& <A>.own(t, alloc) &*& struct_RawVecInner_padding(self);
    //@ on_unwind_ens thread_token(t) &*& (*self).ptr |-> _ &*& (*self).cap |-> _ &*& (*self).alloc |-> ?alloc &*& <A>.own(t, alloc) &*& struct_RawVecInner_padding(self);
    {
        //@ let self_ref = precreate_ref(self);
        //@ open_ref_init_perm_RawVecInner(self_ref);
        //@ open_points_to(self);
        //@ open RawVecInner(t, self0, elem_layout, ptr_, allocSize);
        //@ init_ref_padding_RawVecInner(self_ref, 1/2);
        //@ std::ptr::init_ref_Unique(&(*self_ref).ptr, 1/2);
        //@ std::num::niche_types::init_ref_UsizeNoHighBit(&(*self_ref).cap, 1/2);
        //@ let k = begin_lifetime();
        let r;
        {
            //@ let_lft 'a = k;
            //@ std::alloc::init_ref_Allocator_at_lifetime::<'a, A>(&(*self_ref).alloc);
            //@ close_ref_initialized_RawVecInner(self_ref);
            r = self.current_memory/*@::<A, 'a>@*/(elem_layout);
        }
        //@ end_lifetime(k);
        //@ open_ref_initialized_RawVecInner(self_ref);
        //@ std::ptr::end_ref_Unique(&(*self_ref).ptr);
        //@ std::num::niche_types::end_ref_UsizeNoHighBit(&(*self_ref).cap);
        //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
        //@ end_ref_padding_RawVecInner(self_ref);
        //@ open RawVecInner0(?alloc_id, ?u, ?cap, elem_layout, _, _);
        if let Some((ptr, layout)) = r {
            //@ let alloc_ref = precreate_ref(&(*self).alloc);
            //@ let k1 = begin_lifetime();
            unsafe {
                //@ let_lft 'a = k1;
                //@ std::alloc::init_ref_Allocator_at_lifetime::<'a, A>(alloc_ref);
                //@ assert ptr_ == std::ptr::NonNull_ptr(ptr);
                //@ std::alloc::Layout_inv(elem_layout);
                //@ std::alloc::Layout_size__Layout_from_size_align_(allocSize, Layout::align_(elem_layout));
                //@ assert allocSize == Layout::size_(layout);
                //@ assert std::ptr::NonNull_ptr(ptr)[..Layout::size_(layout)] |-> _;
                self.alloc.deallocate(ptr, layout);
                //@ leak Allocator(_, _, _);
            }
            //@ end_lifetime(k1);
            //@ std::alloc::end_ref_Allocator_at_lifetime::<A>();
        }
        //@ if r == Option::None { leak ptr_[..allocSize] |-> _; }
        //@ std::alloc::Allocator_to_own((*self).alloc);
    }
}

// not marked inline(never) since we want optimizers to be able to observe the specifics of this
// function, see tests/codegen/vec-reserve-extend.rs.
#[cold]
fn finish_grow<A>(
    new_layout: Layout,
    current_memory: Option<(NonNull<u8>, Layout)>,
    alloc: &mut A,
) -> Result<NonNull<[u8]>, TryReserveError>
where
    A: Allocator,
{
    alloc_guard(new_layout.size())?;

    let memory = if let Some((ptr, old_layout)) = current_memory {
        debug_assert_eq!(old_layout.align(), new_layout.align());
        unsafe {
            // The allocator checks for alignment equality
            hint::assert_unchecked(old_layout.align() == new_layout.align());
            alloc.grow(ptr, old_layout, new_layout)
        }
    } else {
        alloc.allocate(new_layout)
    };

    memory.map_err(|_| AllocError { layout: new_layout, non_exhaustive: () }.into())
}

// Central function for reserve error handling.
#[cfg(not(no_global_oom_handling))]
#[cold]
#[optimize(size)]
#[track_caller]
fn handle_error(e: TryReserveError) -> ! {
    match e.kind() {
        CapacityOverflow => capacity_overflow(),
        AllocError { layout, .. } => handle_alloc_error(layout),
    }
}

// We need to guarantee the following:
// * We don't ever allocate `> isize::MAX` byte-size objects.
// * We don't overflow `usize::MAX` and actually allocate too little.
//
// On 64-bit we just need to check for overflow since trying to allocate
// `> isize::MAX` bytes will surely fail. On 32-bit and 16-bit we need to add
// an extra guard for this in case we're running on a platform which can use
// all 4GB in user-space, e.g., PAE or x32.
#[inline]
fn alloc_guard(alloc_size: usize) -> Result<(), TryReserveError>
//@ req thread_token(currentThread);
/*@
ens thread_token(currentThread) &*&
    match result {
        Result::Ok(dummy) => true,
        Result::Err(err) => <std::collections::TryReserveError>.own(currentThread, err)
    };
@*/
//@ safety_proof { assume(false); }
{
    if usize::BITS < 64 && alloc_size > isize::MAX as usize { //~allow_dead_code
        Err(CapacityOverflow.into()) //~allow_dead_code
    } else {
        Ok(())
    }
}

#[inline]
fn layout_array(cap: usize, elem_layout: Layout) -> Result<Layout, TryReserveError>
//@ req Layout::size_(elem_layout) % Layout::align_(elem_layout) == 0;
/*@
ens match result {
        Result::Ok(layout) =>
            Layout::size_(layout) == cap * Layout::size_(elem_layout) &*&
            Layout::align_(layout) == Layout::align_(elem_layout),
        Result::Err(err) => true
    };
@*/
//@ safety_proof { assume(false); }
//@ assume_correct // TODO
{
    elem_layout.repeat(cap).map(|(layout, _pad)| layout).map_err(|_| CapacityOverflow.into())
}
