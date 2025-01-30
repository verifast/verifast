// verifast_options{ignore_unwind_paths ignore_ref_creation}

#![feature(negative_impls)]

use std::{cell::UnsafeCell, process::abort, ptr::NonNull};

struct RcBox<T> {
    strong: UnsafeCell<usize>,
    // weak: UnsafeCell<usize>,
    value: T,
}

pub struct Rc<T> {
    ptr: NonNull<RcBox<T>>,
}

impl<T> !Send for Rc<T> {}
impl<T> !Sync for Rc<T> {}

/*@

// dk: dynamic lifetime
// gh: ghost location
pred_ctor dlft_pred(dk: lifetime_t)(gid: usize; destroyed: bool) = ghost_cell(gid, destroyed) &*& if destroyed { true } else { lifetime_token(dk) };

pred_ctor rc_na_inv<T>(dk: lifetime_t, gid: usize, ptr: *RcBox<T>, t: thread_id_t)() =
    counting(dlft_pred(dk), gid, ?sn, ?destroyed) &*& if destroyed { true } else {
        (*ptr).strong |-> sn &*& sn >= 1 &*&
        std::alloc::alloc_block(ptr as *u8, std::alloc::Layout::new_::<RcBox<T>>()) &*& struct_RcBox_padding::<T>(ptr) &*&
        borrow_end_token(dk, <T>.full_borrow_content(t, &(*ptr).value))
    };

pred<T> <Rc<T>>.own(t, rc) =
    wrap::<*RcBox<T>>(std::ptr::NonNull_ptr(rc.ptr)) == wrap(?ptr) &*& ref_origin(ptr) == ptr &*&
    ptr as usize != 0 &*&
    [_]exists(?dk) &*& [_]exists(?gid) &*& [_]na_inv(t, MaskNshrSingle(ptr), rc_na_inv(dk, gid, ptr, t)) &*&
    ticket(dlft_pred(dk), gid, ?frac) &*& [frac]dlft_pred(dk)(gid, false) &*&
    [_](<T>.share(dk, t, &(*ptr).value)) &*&
    pointer_within_limits(&(*ptr).strong) == true &*&
    pointer_within_limits(&(*ptr).value) == true;

lem Rc_own_mono<T0, T1>()
    req type_interp::<T0>() &*& type_interp::<T1>() &*& Rc_own::<T0>(?t, ?v) &*& is_subtype_of::<T0, T1>() == true;
    ens type_interp::<T0>() &*& type_interp::<T1>() &*& Rc_own::<T1>(t, Rc::<T1> { ptr: upcast(v.ptr) });
{
    assume(false);
}

pred_ctor Rc_frac_bc<T>(l: *Rc<T>, nnp: std::ptr::NonNull<RcBox<T>>)(;) = (*l).ptr |-> nnp;

pred_ctor ticket_(dk: lifetime_t, gid: usize, frac: real)(;) = ticket(dlft_pred(dk), gid, frac) &*& [frac]ghost_cell(gid, false);

pred<T> <Rc<T>>.share(k, t, l) =
    [_]exists(?nnp) &*& [_]frac_borrow(k, Rc_frac_bc(l, nnp)) &*&
    wrap::<*RcBox<T>>(std::ptr::NonNull_ptr(nnp)) == wrap(?ptr) &*& ptr as usize != 0 &*& ref_origin(ptr) == ptr &*&
    [_]exists(?dk) &*& [_]exists(?gid) &*& [_]na_inv(t, MaskNshrSingle(ptr), rc_na_inv(dk, gid, ptr, t)) &*&
    [_]exists(?frac) &*& [_]frac_borrow(k, ticket_(dk, gid, frac)) &*& [_]frac_borrow(k, lifetime_token_(frac, dk)) &*&
    [_](<T>.share(dk, t, &(*ptr).value)) &*&
    pointer_within_limits(&(*ptr).strong) == true &*&
    pointer_within_limits(&(*ptr).value) == true;

lem Rc_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Rc<T>)
    req lifetime_inclusion(k1, k) == true &*& [_]Rc_share::<T>(k, t, l);
    ens [_]Rc_share::<T>(k1, t, l);
{
    open [?df]Rc_share::<T>(k, t, l);
    assert [_]exists::<std::ptr::NonNull<RcBox<T>>>(?nnp) &*& [_]exists::<lifetime_t>(?dk) &*& [_]exists::<usize>(?gid) &*& [_]exists::<real>(?frac);
    frac_borrow_mono(k, k1, Rc_frac_bc(l, nnp));
    frac_borrow_mono(k, k1, ticket_(dk, gid, frac));
    frac_borrow_mono(k, k1, lifetime_token_(frac, dk));
    close [df]Rc_share::<T>(k1, t, l);
}

lem Rc_fbor_split<T>(t: thread_id_t, l: *Rc<T>) -> std::ptr::NonNull<RcBox<T>> //nnp
    req atomic_mask(?m) &*& mask_le(Nlft, m) == true &*&
        full_borrow(?k, Rc_full_borrow_content::<T>(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(m) &*&
        full_borrow(k, Rc_frac_bc(l, result)) &*& std::ptr::NonNull_ptr(result) as usize != 0 &*&
        ref_origin(std::ptr::NonNull_ptr(result)) == std::ptr::NonNull_ptr(result) &*&
        [_]exists(?dk) &*& [_]exists(?gid) &*&
        [_]na_inv(t, MaskNshrSingle(std::ptr::NonNull_ptr(result)), rc_na_inv(dk, gid, std::ptr::NonNull_ptr(result), t)) &*&
        [_]exists(?frac) &*& full_borrow(k, ticket_(dk, gid, frac)) &*& full_borrow(k, lifetime_token_(frac, dk)) &*&
        [_](<T>.share(dk, t, &(*std::ptr::NonNull_ptr::<RcBox<T>>(result)).value)) &*&
        pointer_within_limits(&(*std::ptr::NonNull_ptr::<RcBox<T>>(result)).strong) == true &*&
        pointer_within_limits(&(*std::ptr::NonNull_ptr::<RcBox<T>>(result)).value) == true &*&
        [q]lifetime_token(k);
{
    let klong = open_full_borrow_strong_m(k, Rc_full_borrow_content::<T>(t, l), q);
    open Rc_full_borrow_content::<T>(t, l)();
    open Rc_own::<T>(t, ?rc);
    let nnp = rc.ptr;
    assert [_]exists::<lifetime_t>(?dk) &*& [_]exists::<usize>(?gid) &*& ticket(dlft_pred(dk), gid, ?frac);
    close Rc_frac_bc::<T>(l, nnp)();
    close sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
    close sep(Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
    {
        pred Ctx() =
            struct_Rc_padding::<T>(l) &*&
            [_]exists(dk) &*& [_]exists(gid) &*& [_]na_inv(t, MaskNshrSingle(std::ptr::NonNull_ptr(nnp)), rc_na_inv(dk, gid, std::ptr::NonNull_ptr(nnp), t)) &*&
            [_](<T>.share(dk, t, &(*std::ptr::NonNull_ptr::<RcBox<T>>(nnp)).value));
        close Ctx();
        produce_lem_ptr_chunk full_borrow_convert_strong(Ctx,
            sep(Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))), klong, Rc_full_borrow_content::<T>(t, l))()
        {
            open sep(Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)))();
            open Rc_frac_bc::<T>(l, nnp)();
            open sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))();
            open ticket_(dk, gid, frac)();
            open Ctx();
            close Rc_own::<T>(t, rc);
            close Rc_full_borrow_content::<T>(t, l)();
        }{
            close_full_borrow_strong_m(klong, Rc_full_borrow_content::<T>(t, l), sep(Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))));
        }
    }
    full_borrow_mono(klong, k, sep(Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk))));
    full_borrow_split_m(k, Rc_frac_bc(l, nnp), sep(ticket_(dk, gid, frac), lifetime_token_(frac, dk)));
    full_borrow_split_m(k, ticket_(dk, gid, frac), lifetime_token_(frac, dk));
    leak exists(frac);
    return nnp;
}

lem Rc_share_full<T>(k: lifetime_t, t: thread_id_t, l: *Rc<T>)
    req atomic_mask(MaskTop) &*& full_borrow(k, Rc_full_borrow_content::<T>(t, l)) &*& [?q]lifetime_token(k);
    ens atomic_mask(MaskTop) &*& [_]Rc_share::<T>(k, t, l) &*& [q]lifetime_token(k);
{
    let nnp = Rc_fbor_split::<T>(t, l);
    full_borrow_into_frac_m(k, Rc_frac_bc(l, nnp));
    assert [?df]exists::<lifetime_t>(?dk) &*& [_]exists::<usize>(?gid) &*& [_]exists::<real>(?frac);
    full_borrow_into_frac_m(k, ticket_(dk, gid, frac));
    full_borrow_into_frac_m(k, lifetime_token_(frac, dk));
    leak exists(nnp);
    close [df]Rc_share::<T>(k, t, l);
}

lem init_ref_Rc<T>(p: *Rc<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]Rc_share::<T>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]Rc_share::<T>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false);
}

@*/

impl<T> Rc<T> {

    pub fn new(value: T) -> Rc<T> {
        unsafe {
            let layout = std::alloc::Layout::new::<RcBox<T>>();
            let p = std::alloc::alloc(layout) as *mut RcBox<T>;
            if p.is_null() {
                std::alloc::handle_alloc_error(layout);
            }
            //@ close_struct(p);
            std::ptr::write(p, RcBox::<T> {
                strong: UnsafeCell::new(1),
                value,
            });
            let ret = Rc::<T> { ptr: NonNull::new_unchecked(p) };
            //@ let nnp = ret.ptr;
            //@ let dk = begin_lifetime();
            //@ leak exists(dk);
            //@ let gid = create_ghost_cell(false); //destroyed
            //@ leak exists::<usize>(gid);
            //@ close dlft_pred(dk)(gid, false);
            //@ start_counting(dlft_pred(dk), gid);
            //@ let frac = create_ticket(dlft_pred(dk), gid);
            //@ open RcBox_value(_, _);
            //@ close_full_borrow_content::<T>(_t, &(*p).value);
            //@ borrow(dk, <T>.full_borrow_content(_t, &(*p).value));
            //@ close rc_na_inv::<T>(dk, gid, p, _t)();
            //@ na_inv_new(_t, MaskNshrSingle(p), rc_na_inv(dk, gid, p, _t));
            //@ share_full_borrow::<T>(dk, _t, &(*p).value);
            //@ close Rc_own::<T>(_t, ret);
            ret
        }
    }

}

impl<T> std::ops::Deref for Rc<T> {

    type Target = T;

    fn deref<'a>(&'a self) -> &'a T {
        unsafe {
            //@ open Rc_share::<T>('a, _t, self);
            //@ assert [_]exists::<std::ptr::NonNull<RcBox<T>>>(?nnp);
            //@ open_frac_borrow('a, Rc_frac_bc(self, nnp), _q_a);
            //@ open [?qp]Rc_frac_bc::<T>(self, nnp)();
            let r = &self.ptr.as_ref().value;
            //@ close [qp]Rc_frac_bc::<T>(self, nnp)();
            //@ close_frac_borrow(qp, Rc_frac_bc(self, nnp));
            //@ assert [_]exists::<real>(?frac) &*& [_]exists::<lifetime_t>(?dk);
            //@ frac_borrow_lft_incl('a, frac, dk);
            //@ produce_type_interp::<T>();
            //@ share_mono::<T>(dk, 'a, _t, r);
            //@ leak type_interp::<T>();
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

impl<T> Clone for Rc<T> {

    fn clone<'a>(&'a self) -> Self {
        unsafe {
            //@ open Rc_share::<T>('a, _t, self);
            //@ assert [_]exists::<std::ptr::NonNull<RcBox<T>>>(?nnp);
            //@ open_frac_borrow('a, Rc_frac_bc(self, nnp), _q_a/2);
            //@ open [?qp]Rc_frac_bc::<T>(self, nnp)();
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
            //@ open rc_na_inv::<T>(dk, gid, ptr, _t)();
            //@ counting_match_fraction(dlft_pred(dk), gid);
            //@ close_frac_borrow(qp_t, ticket_(dk, gid, frac));
            //@ close_frac_borrow(qp_dk, lifetime_token_(frac, dk));
            if *strong >= usize::MAX {
                abort();
            }
            *strong = *strong + 1;
            //@ let frac1 = create_ticket(dlft_pred(dk), gid);
            //@ close rc_na_inv::<T>(dk, gid, ptr, _t)();
            //@ close_na_inv(_t, MaskNshrSingle(ptr));
            //@ thread_token_merge(_t, MaskNshrSingle(ptr), mask_diff(MaskTop, MaskNshrSingle(ptr)));
            //@ close thread_token(_t);
            let r = Self { ptr: self.ptr };
            //@ close [qp]Rc_frac_bc::<T>(self, nnp)();
            //@ close_frac_borrow(qp, Rc_frac_bc(self, nnp));
            //@ close Rc_own::<T>(_t, r);
            r
        }
    }

}

impl<T> Drop for Rc<T> {

    fn drop<'a>(&'a mut self) {
        unsafe {
            //@ open Rc_full_borrow_content::<T>(_t, self)();
            //@ open Rc_own::<T>(_t, ?rc);
            let strong = (*self.ptr.as_ptr()).strong.get();
            //@ let nnp = rc.ptr;
            //@ assert [_]exists::<lifetime_t>(?dk) &*& [_]exists::<usize>(?gid);
            //@ let ptr = std::ptr::NonNull_ptr::<RcBox<T>>(nnp);
            //@ open thread_token(_t);
            //@ open_na_inv(_t, MaskNshrSingle(ptr), rc_na_inv(dk, gid, ptr, _t));
            //@ open rc_na_inv::<T>(dk, gid, ptr, _t)();
            //@ counting_match_fraction(dlft_pred(dk), gid);
            *strong = *strong - 1;
            //@ destroy_ticket(dlft_pred(dk), gid);
            if *strong == 0 {
                //@ stop_counting(dlft_pred(dk), gid);
                //@ open dlft_pred(dk)(gid, false);
                //@ end_lifetime(dk);
                //@ borrow_end(dk, <T>.full_borrow_content(_t, &(*ptr).value));
                //@ ghost_cell_mutate(gid, true);
                //@ close dlft_pred(dk)(gid, true);
                //@ start_counting(dlft_pred(dk), gid);
                //@ close rc_na_inv::<T>(dk, gid, ptr, _t)();
                //@ close_na_inv(_t, MaskNshrSingle(ptr));
                //@ thread_token_merge(_t, mask_diff(MaskTop, MaskNshrSingle(ptr)), MaskNshrSingle(ptr));
                //@ close thread_token(_t);
                //@ open_full_borrow_content::<T>(_t, &(*ptr).value);
                std::ptr::drop_in_place(&mut (*self.ptr.as_ptr()).value as *mut T);
                //@ close RcBox_strong_(ptr, _);
                //@ open_struct(ptr);
                //@ std::ptr::close_NonNull_own::<RcBox<T>>(_t, nnp);
                std::alloc::dealloc(
                    self.ptr.as_ptr() as *mut u8,
                    std::alloc::Layout::new::<RcBox<T>>(),
                );
            } else {
                //@ close rc_na_inv::<T>(dk, gid, ptr, _t)();
                //@ close_na_inv(_t, MaskNshrSingle(ptr));
                //@ thread_token_merge(_t, mask_diff(MaskTop, MaskNshrSingle(ptr)), MaskNshrSingle(ptr));
                //@ close thread_token(_t);
                //@ std::ptr::close_NonNull_own::<RcBox<T>>(_t, nnp);
            }
        }
    }

}
