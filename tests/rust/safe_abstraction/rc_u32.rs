// verifast_options{ignore_unwind_paths ignore_ref_creation}

#![feature(negative_impls)]
use std::{cell::UnsafeCell, process::abort, ptr::NonNull};
/*@
// TODO: Move to general.h
//pred_ctor points_to__<T>(p: *T)(;) = *p |-> ?v;
//pred u32_share(k: lifetime_t, t: thread_id_t, l: *u32) = [_]frac_borrow(k, points_to__(l));

// dk: dynamic lifetime
// gh: ghost location
pred_ctor dlft_pred(dk: lifetime_t)(gid: usize; destroyed: bool) = ghost_cell(gid, destroyed) &*& if destroyed { true } else { lifetime_token(dk) };

pred_ctor rc_na_inv(dk: lifetime_t, gid: usize, ptr: *RcBoxU32, t: thread_id_t)() =
    counting(dlft_pred(dk), gid, ?sn, ?destroyed) &*& if destroyed { true } else {
        (*ptr).strong |-> sn &*& sn >= 1 &*&
        std::alloc::alloc_block(ptr as *u8, std::alloc::Layout::new::<RcBoxU32>()) &*& struct_RcBoxU32_padding(ptr) &*&
        borrow_end_token(dk, u32_full_borrow_content(t, &(*ptr).value))
    };

//pred_ctor ticket_(dk: lifetime_t, gid: usize, frac: real, destroyed: bool)(;) = ticket(dlft_pred(dk), gid, frac) &*& [frac]dlft_pred(dk)(gid, destroyed);

// TODO: Add the following syntax to parser: `let ptr = std::ptr::NonNull_ptr(nnp);`
pred <RcU32>.own(t, rcU32) =
    std::ptr::NonNull_ptr(rcU32.ptr) as usize != 0 &*&
    ref_origin(std::ptr::NonNull_ptr::<RcBoxU32>(rcU32.ptr)) == std::ptr::NonNull_ptr::<RcBoxU32>(rcU32.ptr) &*&
    [_]exists(?dk) &*& [_]exists(?gid) &*& [_]na_inv(t, MaskNshrSingle(std::ptr::NonNull_ptr(rcU32.ptr)), rc_na_inv(dk, gid, std::ptr::NonNull_ptr(rcU32.ptr), t)) &*&
    ticket(dlft_pred(dk), gid, ?frac) &*& [frac]dlft_pred(dk)(gid, false) &*&
    [_]frac_borrow(dk, u32_full_borrow_content(t, &(*std::ptr::NonNull_ptr::<RcBoxU32>(rcU32.ptr)).value)) &*&
    pointer_within_limits(&(*std::ptr::NonNull_ptr::<RcBoxU32>(rcU32.ptr)).strong) == true &*&
    pointer_within_limits(&(*std::ptr::NonNull_ptr::<RcBoxU32>(rcU32.ptr)).value) == true;

pred_ctor Rc_frac_bc(l: *RcU32, nnp: std::ptr::NonNull<RcBoxU32>)(;) = (*l).ptr |-> nnp;
pred_ctor ticket_(dk: lifetime_t, gid: usize, frac: real)(;) = ticket(dlft_pred(dk), gid, frac) &*& [frac]ghost_cell(gid, false);
pred <RcU32>.share(k, t, l) =
    [_]exists(?nnp) &*& [_]frac_borrow(k, Rc_frac_bc(l, nnp)) &*& std::ptr::NonNull_ptr(nnp) as usize != 0 &*&
    ref_origin(std::ptr::NonNull_ptr::<RcBoxU32>(nnp)) == std::ptr::NonNull_ptr::<RcBoxU32>(nnp) &*&
    [_]exists(?dk) &*& [_]exists(?gid) &*& [_]na_inv(t, MaskNshrSingle(std::ptr::NonNull_ptr(nnp)), rc_na_inv(dk, gid, std::ptr::NonNull_ptr(nnp), t)) &*&
    [_]exists(?frac) &*& [_]frac_borrow(k, ticket_(dk, gid, frac)) &*& [_]frac_borrow(k, lifetime_token_(frac, dk)) &*&
    [_]frac_borrow(dk, u32_full_borrow_content(t, &(*std::ptr::NonNull_ptr::<RcBoxU32>(nnp)).value)) &*&
    pointer_within_limits(&(*std::ptr::NonNull_ptr::<RcBoxU32>(nnp)).strong) == true &*&
    pointer_within_limits(&(*std::ptr::NonNull_ptr::<RcBoxU32>(nnp)).value) == true;

lem RcU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *RcU32)
    req lifetime_inclusion(k1, k) == true &*& [_]RcU32_share(k, t, l);
    ens [_]RcU32_share(k1, t, l);
{
    open [?df]RcU32_share(k, t, l);
    assert [_]exists::<std::ptr::NonNull<RcBoxU32>>(?nnp) &*& [_]exists::<lifetime_t>(?dk) &*& [_]exists::<usize>(?gid) &*& [_]exists::<real>(?frac);
    frac_borrow_mono(k, k1, Rc_frac_bc(l, nnp));
    frac_borrow_mono(k, k1, ticket_(dk, gid, frac));
    frac_borrow_mono(k, k1, lifetime_token_(frac, dk));
    close [df]RcU32_share(k1, t, l);
}

pred_ctor rc_ctx(t: thread_id_t, l: *RcU32, nnp: std::ptr::NonNull<RcBoxU32>, dk: lifetime_t, gid: usize)() =
    struct_RcU32_padding(l) &*&
    [_]exists(dk) &*& [_]exists(gid) &*& [_]na_inv(t, MaskNshrSingle(std::ptr::NonNull_ptr(nnp)), rc_na_inv(dk, gid, std::ptr::NonNull_ptr(nnp), t)) &*&
    [_]frac_borrow(dk, u32_full_borrow_content(t, &(*std::ptr::NonNull_ptr::<RcBoxU32>(nnp)).value));

lem RcU32_fbor_split(t: thread_id_t, l: *RcU32) -> std::ptr::NonNull<RcBoxU32> //nnp
    req atomic_mask(?m) &*& mask_le(Nlft, m) == true &*&
        full_borrow(?k, RcU32_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(m) &*&
        full_borrow(k, Rc_frac_bc(l, result)) &*& std::ptr::NonNull_ptr(result) as usize != 0 &*&
        ref_origin(std::ptr::NonNull_ptr(result)) == std::ptr::NonNull_ptr(result) &*&
        [_]exists(?dk) &*& [_]exists(?gid) &*&
        [_]na_inv(t, MaskNshrSingle(std::ptr::NonNull_ptr(result)), rc_na_inv(dk, gid, std::ptr::NonNull_ptr(result), t)) &*&
        [_]exists(?frac) &*& full_borrow(k, ticket_(dk, gid, frac)) &*& full_borrow(k, lifetime_token_(frac, dk)) &*&
        [_]frac_borrow(dk, u32_full_borrow_content(t, &(*std::ptr::NonNull_ptr::<RcBoxU32>(result)).value)) &*&
        pointer_within_limits(&(*std::ptr::NonNull_ptr::<RcBoxU32>(result)).strong) == true &*&
        pointer_within_limits(&(*std::ptr::NonNull_ptr::<RcBoxU32>(result)).value) == true &*&
        [q]lifetime_token(k);
{
    let klong = open_full_borrow_strong_m(k, RcU32_full_borrow_content(t, l), q);
    open RcU32_full_borrow_content(t, l)();
    open RcU32_own(t, ?rcU32);
    let nnp = rcU32.ptr;
    assert [_]exists::<lifetime_t>(?dk) &*& [_]exists::<usize>(?gid) &*& ticket(dlft_pred(dk), gid, ?frac);
    close Rc_frac_bc(l, nnp)();
    close sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
    close sep(Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
    close rc_ctx(t, l, nnp, dk, gid)();
    produce_lem_ptr_chunk full_borrow_convert_strong(rc_ctx(t, l, nnp, dk, gid),
        sep(Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))), klong, RcU32_full_borrow_content(t, l))()
    {
        open sep(Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
        open Rc_frac_bc(l, nnp)();
        open sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
        open ticket_(dk, gid, frac)();
        open rc_ctx(t, l, nnp, dk, gid)();
        close RcU32_own(t, rcU32);
        close RcU32_full_borrow_content(t, l)();
    }{
        close_full_borrow_strong_m(klong, RcU32_full_borrow_content(t, l), sep(Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))));
    }
    full_borrow_mono(klong, k, sep(Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))));
    full_borrow_split_m(k, Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)));
    full_borrow_split_m(k, ticket_(dk, gid, frac), lifetime_token_(frac, dk));
    leak exists(frac);
    return nnp;
}

lem RcU32_share_full(k: lifetime_t, t: thread_id_t, l: *RcU32)
    req atomic_mask(MaskTop) &*& full_borrow(k, RcU32_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(MaskTop) &*& [_]RcU32_share(k, t, l) &*& [q]lifetime_token(k);
{
    let nnp = RcU32_fbor_split(t, l);
    full_borrow_into_frac_m(k, Rc_frac_bc(l, nnp));
    assert [?df]exists::<lifetime_t>(?dk) &*& [_]exists::<usize>(?gid) &*& [_]exists::<real>(?frac);
    full_borrow_into_frac_m(k, ticket_(dk, gid, frac));
    full_borrow_into_frac_m(k, lifetime_token_(frac, dk));
    leak exists(nnp);
    close [df]RcU32_share(k, t, l);
}

lem init_ref_RcU32(p: *RcU32)
    req atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]RcU32_share(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]RcU32_share(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false);
}

@*/
pub struct RcU32 {
    ptr: NonNull<RcBoxU32>,
}

impl !Send for RcU32 {}
impl !Sync for RcU32 {}

struct RcBoxU32 {
    strong: UnsafeCell<usize>,
    // weak: UnsafeCell<usize>,
    value: u32,
}

impl RcU32 {
    pub fn new(value: u32) -> RcU32 {
        unsafe {
            let layout = std::alloc::Layout::new::<RcBoxU32>();
            let p = std::alloc::alloc(layout) as *mut RcBoxU32;
            if p.is_null() {
                std::alloc::handle_alloc_error(layout);
            }
            //@ close_struct(p);
            *p = RcBoxU32 {
                strong: UnsafeCell::new(1),
                value,
            };
            let ret = RcU32 { ptr: NonNull::new_unchecked(p) };
            //@ let nnp = ret.ptr;
            //@ let dk = begin_lifetime();
            //@ leak exists(dk);
            //@ let gid = create_ghost_cell(false); //destroyed
            //@ leak exists::<usize>(gid);
            //@ close dlft_pred(dk)(gid, false);
            //@ start_counting(dlft_pred(dk), gid);
            //@ let frac = create_ticket(dlft_pred(dk), gid);
            //@ close u32_full_borrow_content(_t, &(*p).value)();
            //@ borrow(dk, u32_full_borrow_content(_t, &(*p).value));
            //@ close rc_na_inv(dk, gid, p, _t)();
            //@ na_inv_new(_t, MaskNshrSingle(p), rc_na_inv(dk, gid, p, _t));
            //@ full_borrow_into_frac(dk, u32_full_borrow_content(_t, &(*p).value));
            //@ close RcU32_own(_t, ret);
            ret
        }
    }
}

impl std::ops::Deref for RcU32 {
    type Target = u32;

    fn deref<'a>(&'a self) -> &'a u32 {
        unsafe {
            //@ open RcU32_share('a, _t, self);
            //@ assert [_]exists::<std::ptr::NonNull<RcBoxU32>>(?nnp);
            //@ open_frac_borrow('a, Rc_frac_bc(self, nnp), _q_a);
            //@ open [?qp]Rc_frac_bc(self, nnp)();
            let r = &self.ptr.as_ref().value;
            //@ close [qp]Rc_frac_bc(self, nnp)();
            //@ close_frac_borrow(qp, Rc_frac_bc(self, nnp));
            //@ assert [_]exists::<real>(?frac) &*& [_]exists::<lifetime_t>(?dk);
            //@ frac_borrow_lft_incl('a, frac, dk);
            //@ frac_borrow_mono(dk, 'a, u32_full_borrow_content(_t, r));
            r
        }
    }
}

/*@
lem close_dlft_pred_(dk: lifetime_t, gid: usize) -> real
    req [?q]lifetime_token(dk) &*& [?q1]ghost_cell(gid, false);
    ens [result]dlft_pred(dk)(gid, false) &*& [q - result]lifetime_token(dk) &*& [q1 - result]ghost_cell(gid, false) &*& result < q &*& result < q1;
{
    lifetime_token_inv(dk);
    ghost_cell_fraction_info(gid);
    if q < q1 { return q/2; } else { return q1/2; }
}
@*/

impl Clone for RcU32 {
    fn clone<'a>(&'a self) -> Self {
        unsafe {
            //@ open RcU32_share('a, _t, self);
            //@ assert [_]exists::<std::ptr::NonNull<RcBoxU32>>(?nnp);
            //@ open_frac_borrow('a, Rc_frac_bc(self, nnp), _q_a/2);
            //@ open [?qp]Rc_frac_bc(self, nnp)();
            let strong = self.ptr.as_ref().strong.get();
            //@ assert [_]exists::<lifetime_t>(?dk) &*& [_]exists::<usize>(?gid) &*& [?df]exists::<real>(?frac);
            //@ open_frac_borrow('a, ticket_(dk, gid, frac), _q_a/4);
            //@ open [?qp_t]ticket_(dk, gid, frac)();
            //@ open_frac_borrow('a, lifetime_token_(frac, dk), _q_a/4);
            //@ open [?qp_dk]lifetime_token_(frac, dk)();
            //@ close_dlft_pred_(dk, gid);
            //@ open thread_token(_t);
            //@ let ptr = std::ptr::NonNull_ptr(nnp);
            //@ open_na_inv(_t, MaskNshrSingle(ptr), rc_na_inv(dk, gid, ptr, _t));
            //@ open rc_na_inv(dk, gid, ptr, _t)();
            //@ counting_match_fraction(dlft_pred(dk), gid);
            //@ close_frac_borrow(qp_t, ticket_(dk, gid, frac));
            //@ close_frac_borrow(qp_dk, lifetime_token_(frac, dk));
            if *strong >= usize::MAX {
                abort();
            }
            *strong = *strong + 1;
            //@ let frac1 = create_ticket(dlft_pred(dk), gid);
            //@ close rc_na_inv(dk, gid, ptr, _t)();
            //@ close_na_inv(_t, MaskNshrSingle(ptr));
            //@ thread_token_merge(_t, MaskNshrSingle(ptr), mask_diff(MaskTop, MaskNshrSingle(ptr)));
            //@ close thread_token(_t);
            let r = Self { ptr: self.ptr };
            //@ close [qp]Rc_frac_bc(self, nnp)();
            //@ close_frac_borrow(qp, Rc_frac_bc(self, nnp));
            //@ close RcU32_own(_t, r);
            r
        }
    }
}

impl Drop for RcU32 {
    fn drop<'a>(&'a mut self)
    {
        unsafe {
            //@ open RcU32_full_borrow_content(_t, self)();
            //@ open RcU32_own(_t, ?rcU32);
            let strong = self.ptr.as_ref().strong.get();
            //@ let nnp = rcU32.ptr;
            //@ assert [_]exists::<lifetime_t>(?dk) &*& [_]exists::<usize>(?gid);
            //@ let ptr = std::ptr::NonNull_ptr::<RcBoxU32>(nnp);
            //@ open thread_token(_t);
            //@ open_na_inv(_t, MaskNshrSingle(ptr), rc_na_inv(dk, gid, ptr, _t));
            //@ open rc_na_inv(dk, gid, ptr, _t)();
            //@ counting_match_fraction(dlft_pred(dk), gid);
            *strong = *strong - 1;
            //@ destroy_ticket(dlft_pred(dk), gid);
            if *strong == 0 {
                //@ stop_counting(dlft_pred(dk), gid);
                //@ open dlft_pred(dk)(gid, false);
                //@ end_lifetime(dk);
                //@ borrow_end(dk, u32_full_borrow_content(_t, &(*ptr).value));
                //@ open u32_full_borrow_content(_t, &(*ptr).value)();
                //@ close RcBoxU32_strong_(ptr, _);
                //@ close RcBoxU32_value_(ptr, _);
                //@ open_struct(ptr);
                // No need to drop a u32
                //@ std::ptr::close_NonNull_own::<RcBoxU32>(_t, nnp);
                std::alloc::dealloc(
                    self.ptr.as_ptr() as *mut u8,
                    std::alloc::Layout::new::<RcBoxU32>(),
                );
                //@ ghost_cell_mutate(gid, true);
                //@ close dlft_pred(dk)(gid, true);
                //@ start_counting(dlft_pred(dk), gid);
            } else {
                //@ std::ptr::close_NonNull_own::<RcBoxU32>(_t, nnp);
            }
            //@ close rc_na_inv(dk, gid, ptr, _t)();
            //@ close_na_inv(_t, MaskNshrSingle(ptr));
            //@ thread_token_merge(_t, mask_diff(MaskTop, MaskNshrSingle(ptr)), MaskNshrSingle(ptr));
            //@ close thread_token(_t);
        }
    }
}
