/* TODO: To spec-out `AtomicUsize` we need its methods to have an `Ordering` parameter. That leads to appearance of Aggregates of `Ordering`
constructors to MIR of this file. This means we might need to include the definitions of external ADTs to our data generated from the exporter.
For now the exporter only encodes localy defined ADTs. */

use std::process::abort;
use std::ptr::NonNull;

pub mod sync {
    pub mod atomic {
        use abort;
        pub struct AtomicUsize {
            v: usize,
        }
        /*@
        pred AtomicUsize(p: *AtomicUsize; v: usize);
        pred AtomicUsize_own(t: thread_id_t, v: usize);
        pred AtomicUsize_share(k: lifetime_t, t: thread_id_t, l: *AtomicUsize);
        @*/
        impl AtomicUsize {
            pub fn new(v: usize) -> AtomicUsize
            //@ req thread_token(?t);
            //@ ens thread_token(t) &*& AtomicUsize_own(t, result.v) &*& result.v == v;
            {
                abort();
            }

            /*@
            lem_type AUs_load_seq_cst(self: *AtomicUsize, Pre_op_token: pred(), Post_op_token: pred(usize)) = lem();
                req AtomicUsize(self, ?v) &*& Pre_op_token();
                ens AtomicUsize(self, v) &*& Post_op_token(v);
            lem_type AUs_load_seq_cst_ghost(self: *AtomicUsize, Pre: pred(), Post: pred(usize)) = lem();
                req atomic_mask(MaskTop) &*& is_AUs_load_seq_cst(?op, self, ?Pre_op_token, ?Post_op_token) &*& Pre_op_token() &*& Pre() &*& AtomicUsize(self, ?v);
                ens atomic_mask(MaskTop) &*& is_AUs_load_seq_cst(op, self, Pre_op_token, Post_op_token) &*& Post_op_token(?res) &*& Post(res) &*& AtomicUsize(self, v);
            @*/
            // TODO: The `unsafe` keyword should be removed from following methods
            pub unsafe fn load_seq_cst<'a>(&'a self) -> usize
            //@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& [_]AtomicUsize_share(a, t, self) &*& is_AUs_load_seq_cst_ghost(?ghop, self, ?Pre, ?Post) &*& Pre();
            //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& Post(result);
            {
                abort();
            }

            /*@
            // TODO: What about OVF
            lem_type AUs_fetch_add_seq_cst(self: *AtomicUsize, Pre_op_token: pred(), Post_op_token: pred(usize)) = lem();
                req AtomicUsize(self, ?old) &*& Pre_op_token();
                ens AtomicUsize(self, old + 1) &*& Post_op_token(old);
            lem_type AUs_fetch_add_seq_cst_ghost(self: *AtomicUsize, Pre: pred(), Post: pred(usize)) = lem();
                req atomic_mask(MaskTop) &*& is_AUs_fetch_add_seq_cst(?op, self, ?Pre_op_token, ?Post_op_token) &*& Pre_op_token() &*& Pre() &*& AtomicUsize(self, ?old);
                ens atomic_mask(MaskTop) &*& is_AUs_fetch_add_seq_cst(op, self, Pre_op_token, Post_op_token) &*& Post_op_token(old) &*& Post(old) &*& AtomicUsize(self, old + 1);
            @*/
            pub unsafe fn fetch_add_seq_cst<'a>(&'a self, val: usize) -> usize
            //@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& [_]AtomicUsize_share(a, t, self) &*& is_AUs_fetch_add_seq_cst_ghost(?ghop, self, ?Pre, ?Post) &*& Pre();
            //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& Post(result);
            {
                abort();
            }

            /*@
            // TODO: What about UNF
            lem_type AUs_fetch_sub_seq_cst(self: *AtomicUsize, Pre_op_token: pred(), Post_op_token: pred(usize)) = lem();
                req AtomicUsize(self, ?old) &*& Pre_op_token();
                ens AtomicUsize(self, old - 1) &*& Post_op_token(old);
            lem_type AUs_fetch_sub_seq_cst_ghost(self: *AtomicUsize, Pre: pred(), Post: pred(usize)) = lem();
                req atomic_mask(MaskTop) &*& is_AUs_fetch_sub_seq_cst(?op, self, ?Pre_op_token, ?Post_op_token) &*& Pre_op_token() &*& Pre() &*& AtomicUsize(self, ?old);
                ens atomic_mask(MaskTop) &*& is_AUs_fetch_sub_seq_cst(op, self, Pre_op_token, Post_op_token) &*& Post_op_token(old) &*& Post(old) &*& AtomicUsize(self, old - 1);
            @*/
            pub unsafe fn fetch_sub_seq_cst<'a>(&'a self, val: usize) -> usize
            //@ req thread_token(?t) &*& [?qa]lifetime_token(?a) &*& [_]AtomicUsize_share(a, t, self) &*& is_AUs_fetch_sub_seq_cst_ghost(?ghop, self, ?Pre, ?Post) &*& Pre();
            //@ ens thread_token(t) &*& [qa]lifetime_token(a) &*& Post(result);
            {
                abort();
            }
        }
    }
}

use sync::atomic::AtomicUsize;

// TODO: This will not be necessary in an approximation which ignores counter ovf
const MAX_REFCOUNT: usize = (isize::MAX) as usize;

pub struct ArcU32 {
    ptr: NonNull<ArcInnerU32>,
}

/*@
pred_ctor dlft_pred(dk: lifetime_t)(gid: isize; destroyed: bool) = ghost_cell(gid, destroyed) &*& if destroyed { true } else { lifetime_token(dk) };
pred_ctor Arc_inv()() = true;
pred ArcU32_own(t: thread_id_t, nnp: std::ptr::NonNull<ArcInnerU32>) = exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*&
    exists(?dk) &*& [_]sync::atomic::AtomicUsize_share(dk, ?t1, &(*ptr).strong);

pred_ctor Arc_frac_bc(l: *ArcU32, nnp: std::ptr::NonNull<ArcInnerU32>)(;) = (*l).ptr |-> nnp;
pred ArcU32_share(k: lifetime_t, t: thread_id_t, l: *ArcU32) = [_]exists(?nnp) &*& [_]frac_borrow(k, Arc_frac_bc(l, nnp)) &*&
    exists(?ptr) &*& std::ptr::NonNull_ptr::<ArcInnerU32>(nnp) == ptr &*&
    exists(?dk) &*& [_]sync::atomic::AtomicUsize_share(dk, ?t1, &(*ptr).strong);

lem ArcU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *ArcU32)
    req lifetime_inclusion(k1, k) == true &*& [_]ArcU32_share(k, t, l);
    ens [_]ArcU32_share(k1, t, l);
{
    assume(false);
}
lem ArcU32_share_full(k: lifetime_t, t: thread_id_t, l: *ArcU32)
    req atomic_mask(Nlft) &*& [?q]lifetime_token(k) &*& full_borrow(k, ArcU32_full_borrow_content(t, l));
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]ArcU32_share(k, t, l);
{
    assume(false);
}
@*/

// TODO: check if `unsafe` is indeed necessary for `Send` and `Sync` marker traits
unsafe impl Send for ArcU32 {}
unsafe impl Sync for ArcU32 {}

struct ArcInnerU32 {
    strong: AtomicUsize,
    // weak: AtomicUsize,
    data: u32,
}

// TODO: Make sure we do need these markers
unsafe impl Send for ArcInnerU32 {}
unsafe impl Sync for ArcInnerU32 {}

impl ArcU32 {
    pub fn new(data: u32) -> ArcU32 {
        unsafe {
            let l = std::alloc::Layout::new::<ArcInnerU32>();
            let p = std::alloc::alloc(l) as *mut ArcInnerU32;
            if p.is_null() {
                std::alloc::handle_alloc_error(l);
            }

            *p = ArcInnerU32 {
                strong: AtomicUsize::new(1),
                data,
            };
            Self {
                ptr: NonNull::new_unchecked(p),
            }
        }
    }

    pub fn strong_count<'a>(this: &'a Self) -> usize {
        unsafe { this.ptr.as_ref().strong.load_seq_cst() }
    }
}

impl std::ops::Deref for ArcU32 {
    type Target = u32;

    fn deref<'a>(&'a self) -> &u32 {
        unsafe { &self.ptr.as_ref().data }
    }
}

impl Clone for ArcU32 {
    fn clone<'a>(&'a self) -> ArcU32 {
        let old_size = unsafe { self.ptr.as_ref().strong.fetch_add_seq_cst(1) };
        if old_size > MAX_REFCOUNT {
            //TODO: Why does not std library check for `old_size >= MAX_REFCOUNT`
            abort();
        }
        Self { ptr: self.ptr }
    }
}

impl Drop for ArcU32 {
    fn drop<'a>(&'a mut self) {
        unsafe {
            if self.ptr.as_ref().strong.fetch_sub_seq_cst(1) != 1 {
                return;
            }
            // acquire!(self.inner().strong);

            std::ptr::drop_in_place(&mut (*self.ptr.as_ptr()).data)
        }
    }
}