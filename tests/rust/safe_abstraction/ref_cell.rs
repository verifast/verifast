// verifast_options{ignore_ref_creation}
#![feature(negative_impls)]

use std::cell::UnsafeCell;
use std::ops::{Deref, DerefMut};
use std::process;
//@ use std::option::Option;

pub struct RefCell<T> {
    value: UnsafeCell<T>, // The value being stored. Mutable even when the RefCell is immutable.
    mutably_borrowed: UnsafeCell<bool>, // Tracks whether a mutable borrow is active, using UnsafeCell for interior mutability.
    immutable_borrows: UnsafeCell<usize>, // Tracks the amount of immutable borrows, using UnsafeCell for interior mutability
}

/*@

lem init_ref_RefCell<T>(p: *RefCell<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]RefCell_share::<T>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]RefCell_share::<T>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false);
}

lem RefCell_send<T>(t1: thread_id_t)
    req type_interp::<T>() &*& is_Send(typeid(T)) == true &*& RefCell_own::<T>(?t0, ?v);
    ens type_interp::<T>() &*& RefCell_own::<T>(t1, v);
{
    open RefCell_own::<T>(t0, v);
    Send::send(t0, t1, v.value);
    close RefCell_own::<T>(t1, v);
}

pred_ctor refcell_inv_<T>(cell: *RefCell<T>)() =
    (*cell).mutably_borrowed |-> ?borrowed &*& (*cell).immutable_borrows |-> ?immutables &*& (borrowed == false || immutables == 0);

pred_ctor RefCell_padding<T>(l: *RefCell<T>)(;) = struct_RefCell_padding(l);

pred dlft_pred(gid: i32; o_dlft_max: Option<lifetime_t>) =
    ghost_cell(gid, o_dlft_max) &*& if o_dlft_max != Option::None { o_dlft_max == Option::Some(?dlft_max) &*& lifetime_token(dlft_max) } else { true };

pred<T> <RefCell<T>>.own(t, cell) = <T>.own(t, cell.value) &*& cell.mutably_borrowed == false || cell.immutable_borrows == 0;

pred<T> <RefCell<T>>.share(k, t, l) =
    exists(?klong) &*&
    exists(?gid) &*&
    lifetime_inclusion(k, klong) == true &*&
    [_]nonatomic_borrow(k, t, MaskNshrSingle(ref_origin(l)), na_borrow_content(ref_origin(l), t, klong, gid));

pred_ctor na_borrow_content<T>(ptr: *RefCell<T>, t: thread_id_t, klong: lifetime_t, gid: i32)() =
    (*ptr).mutably_borrowed |-> ?borrowed &*&
    (*ptr).immutable_borrows |-> ?immutables &*&
    pointer_within_limits(&(*ptr).immutable_borrows) == true &*&
    pointer_within_limits(&(*ptr).mutably_borrowed) == true &*&
    pointer_within_limits(&(*ptr).value) == true &*&
    borrowed == false || immutables == 0 &*&
    counting(dlft_pred, gid, immutables, ?o_dlft_max) &*&
    if !borrowed {
        if immutables > 0 {
            o_dlft_max == Option::Some(?dlft_max) &*&
            [_](<T>.share)(lifetime_intersection(klong, dlft_max), t, &(*ptr).value) &*&
            end_reborrow_token(lifetime_intersection(klong, dlft_max), klong, <T>.full_borrow_content(t, &(*ptr).value))
        } else {
            full_borrow(klong, <T>.full_borrow_content(t, &(*ptr).value))
        }
    } else {
        immutables == 0
    };

lem RefCell_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *RefCell<T>)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*& [_]RefCell_share::<T>(k, t, l);
    ens type_interp::<T>() &*& [_]RefCell_share::<T>(k1, t, l);
{
    open [?df]RefCell_share::<T>(k, t, l);
    assert [_]nonatomic_borrow(k, t, ?m, _) &*& [_]exists::<lifetime_t>(?klong) &*& [_]exists::<i32>(?gid);
    nonatomic_borrow_mono(k, k1, t, m, na_borrow_content(ref_origin(l), t, klong, gid));
    lifetime_inclusion_trans(k1, k, klong);
    close [df]RefCell_share::<T>(k1, t, l);
}

lem RefCell_share_full<T>(k: lifetime_t, t: thread_id_t, l: *RefCell<T>)
    req type_interp::<T>() &*& atomic_mask(MaskTop) &*& full_borrow(k, RefCell_full_borrow_content::<T>(t, l)) &*& [?q]lifetime_token(k) &*& l == ref_origin(l);
    ens type_interp::<T>() &*& atomic_mask(MaskTop) &*& [_]RefCell_share::<T>(k, t, l) &*& [q]lifetime_token(k);
{
    produce_lem_ptr_chunk implies(RefCell_full_borrow_content(t, l), sep(RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), refcell_inv_::<T>(l))))() {
        open RefCell_full_borrow_content::<T>(t, l)();
        assert (*l).value |-> ?value &*& (*l).mutably_borrowed |-> ?mutably_borrowed &*& (*l).immutable_borrows |-> ?immutable_borrows;
        open RefCell_own::<T>()(t, RefCell::<T> { value, mutably_borrowed, immutable_borrows});
        close_full_borrow_content::<T>(t, &(*l).value);
        close refcell_inv_::<T>(l)();
        close sep(<T>.full_borrow_content(t, &(*l).value), refcell_inv_::<T>(l))();
        close RefCell_padding::<T>(l)();
        close sep(RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), refcell_inv_::<T>(l)))();
    } {
        produce_lem_ptr_chunk implies(sep(RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), refcell_inv_::<T>(l))), RefCell_full_borrow_content(t, l))() {
            open sep(RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), refcell_inv_::<T>(l)))();
            open RefCell_padding::<T>(l)();
            open sep(<T>.full_borrow_content(t, &(*l).value), refcell_inv_::<T>(l))();
            open refcell_inv_::<T>(l)();
            open_full_borrow_content::<T>(t, &(*l).value);
            assert (*l).value |-> ?value &*& (*l).mutably_borrowed |-> ?mutably_borrowed &*& (*l).immutable_borrows |-> ?immutable_borrows;
            close RefCell_own::<T>(t, RefCell::<T> { value: value, mutably_borrowed: mutably_borrowed, immutable_borrows });
            close RefCell_full_borrow_content::<T>(t, l)();
        } {
            full_borrow_implies(k, RefCell_full_borrow_content(t, l), sep(RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), refcell_inv_::<T>(l))));
        }
    }
    full_borrow_split_m(k, RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), refcell_inv_::<T>(l)));
    full_borrow_split_m(k, <T>.full_borrow_content(t, &(*l).value), refcell_inv_::<T>(l));

    open_full_borrow_m(q, k, <T>.full_borrow_content(t, &(*l).value));
    open_full_borrow_content(t, &(*l).value);
    points_to_limits(&(*l).value);
    close_full_borrow_content(t, &(*l).value);
    close_full_borrow_m(<T>.full_borrow_content(t, &(*l).value));
    let gid = create_ghost_cell::<Option<lifetime_t>>(Option::None);
    close exists(gid);


    let kstrong = open_full_borrow_strong_m(k, refcell_inv_::<T>(l), q/2); // LFTL-BOR-ACC-STRONG
    produce_lem_ptr_chunk full_borrow_convert_strong(True, na_borrow_content(l, t, k, gid), kstrong, refcell_inv_::<T>(l))() {
        open na_borrow_content::<T>(l, t, k, gid)();
        leak counting(_, _, _, _);
        if (*l).mutably_borrowed == false && (*l).immutable_borrows == 0{
            leak full_borrow(_, <T>.full_borrow_content(t, &(*l).value));
        } else {
            if (*l).mutably_borrowed == false && (*l).immutable_borrows != 0 {
                leak [_](<T>.share)(_, _, _);
                leak end_reborrow_token(_, _, _);
            }
        }
        close refcell_inv_::<T>(l)();
    }{
        open refcell_inv_::<T>(l)();
        close exists(k);
        assert RefCell_mutably_borrowed(l, ?borrowed);
        assert RefCell_immutable_borrows(l, ?immutables);

        if borrowed == true && immutables == 0 {
            leak full_borrow(_, <T>.full_borrow_content(t, &(*l).value));
            start_counting(dlft_pred, gid);
        }
        else if borrowed == false && immutables > 0 {
            let dlft_max = begin_lifetime_m();
            let dlft = lifetime_intersection(k, dlft_max);
            reborrow_m(dlft, k, <T>.full_borrow_content(t, &(*l).value));
            ghost_cell_mutate(gid, Option::Some(dlft_max));
            start_counting(dlft_pred, gid);
            let i = 0;
            while i < immutables - 1
                inv i <= immutables - 1 &*& counting(dlft_pred, gid, i, Option::Some(dlft_max));
                decreases immutables - i;
            {
                create_ticket(dlft_pred, gid);
                leak ticket(_, _, _);
                leak [_]dlft_pred(_, _);
                i = i + 1;
            }
            let frac = create_ticket(dlft_pred, gid);
            open [frac]dlft_pred(gid, Option::Some(dlft_max));
            assert [?qk]lifetime_token(k);
            lifetime_token_inv(k);
            if qk < 1 { }
            let minimal_frac = default_value;
            if qk < frac {
                minimal_frac = qk;
            }
            if frac < qk {
                minimal_frac = frac;
            }
            if qk == frac {
                minimal_frac = frac;
            }
            close_lifetime_intersection_token(minimal_frac, k, dlft_max);
            share_full_borrow_m::<T>(dlft, t, &(*l).value);
            open_lifetime_intersection_token(minimal_frac, k, dlft_max);

            leak ticket(dlft_pred, gid, frac);
            leak [frac]ghost_cell(gid, Option::Some(dlft_max));
            leak [frac]lifetime_token(dlft_max);
        }
        else if borrowed == false && immutables == 0{
            start_counting(dlft_pred, gid);
        }
        points_to_limits(&(*l).mutably_borrowed);
        points_to_limits(&(*l).immutable_borrows);
        close na_borrow_content::<T>(l, t, k, gid)();
        close_full_borrow_strong_m(kstrong, refcell_inv_::<T>(l), na_borrow_content(l, t, k, gid));
        full_borrow_into_nonatomic_borrow_m(kstrong, t, MaskNshrSingle(l), na_borrow_content(l, t, k, gid));
        nonatomic_borrow_mono(kstrong, k, t, MaskNshrSingle(l), na_borrow_content(l, t, k, gid));
        close exists(k);
        close RefCell_share::<T>(k, t, l);
        leak RefCell_share::<T>(k, t, l);
        leak full_borrow(k, RefCell_padding(l));
    }
}

@*/

impl<T> RefCell<T> {
    pub fn new(value: T) -> Self {
        let r = RefCell {
            value: UnsafeCell::new(value),
            mutably_borrowed: UnsafeCell::new(false),
            immutable_borrows: UnsafeCell::new(0),
        };
        //@ close RefCell_own::<T>(_t, r);
        r
    }

    pub fn borrow_mut<'a>(this: &'a Self) -> RefMut<'a, T> {
        //@ open RefCell_share::<T>()('a, _t, this);
        unsafe {
            //@ assert [_]exists::<lifetime_t>(?dk);
            //@ assert [_]exists::<i32>(?gid);
            //@ assert [_]nonatomic_borrow('a, _t, ?mask, na_borrow_content(ref_origin(this), _t, dk, gid));
            //@ open thread_token(_t);
            //@ thread_token_split(_t, MaskTop, mask);
            //@ open_nonatomic_borrow('a, _t, mask, _q_a);
            //@ open na_borrow_content::<T>(ref_origin(this), _t, dk, gid)();
            //@ open RefCell_mutably_borrowed::<T>(ref_origin(this), _);
            if *this.mutably_borrowed.get() == false && *this.immutable_borrows.get() == 0 {
                *this.mutably_borrowed.get() = true;
            } else {
                process::abort();
            }
        }
        //@ assert partial_thread_token(_t, ?mask0);
        //@ close exists(gid);
        //@ close na_borrow_content::<T>(ref_origin(this), _t, dk, gid)();
        //@ close_nonatomic_borrow();
        //@ thread_token_merge(_t, mask0, mask);
        //@ close thread_token(_t);
        // Return a RefMut object that will reset the mutably_borrowed flag when dropped
        //@ assert full_borrow(?kv, <T>.full_borrow_content(_t, &(*ref_origin(this)).value));
        //@ close exists(kv);
        let r = RefMut { refcell: this };
        //@ close RefMut_own::<'a, T>(_t, r);
        r
    }

    pub fn borrow<'a>(this: &'a Self) -> Ref<'a, T> {
        //@ open RefCell_share::<T>()('a, _t, this);
        //@ assert [?qa]lifetime_token('a);
        unsafe {
            //@ assert [_]exists::<lifetime_t>(?klong);
            //@ assert [_]exists::<i32>(?gid);
            //@ assert [_]nonatomic_borrow('a, _t, ?mask, na_borrow_content(ref_origin(this), _t, klong, gid));
            //@ open thread_token(_t);
            //@ thread_token_split(_t, MaskTop, mask);
            //@ open_nonatomic_borrow('a, _t, mask, _q_a / 2);
            //@ open na_borrow_content::<T>(ref_origin(this), _t, klong, gid)();
            //@ assert RefCell_mutably_borrowed::<T>(ref_origin(this), ?borrowed);
            //@ assert RefCell_immutable_borrows::<T>(ref_origin(this), ?immutables);
            if *this.mutably_borrowed.get() {
                process::abort();
            }
            let current_borrows = *this.immutable_borrows.get();
            if let Some(new_borrows) = current_borrows.checked_add(1) {
                *this.immutable_borrows.get() = new_borrows;
            } else {
                process::abort();
            }
            //@ assert partial_thread_token(_t, ?mask0);
            /*@ if immutables == 0
                {
                    let dlft_max = begin_lifetime();
                    let dlft = lifetime_intersection(klong, dlft_max);
                    reborrow(dlft, klong, <T>.full_borrow_content(_t, &(*ref_origin(this)).value));
                    assert counting(dlft_pred, gid, immutables, ?o_dlft_max);
                    stop_counting(dlft_pred, gid);
                    open dlft_pred(gid, o_dlft_max);
                    if o_dlft_max != Option::None {
                        assert o_dlft_max == Option::Some(?old_dlft_max);
                        end_lifetime(old_dlft_max);
                    }

                    ghost_cell_mutate(gid, Option::Some(dlft_max));
                    assert [?qa2]lifetime_token('a);
                    lifetime_token_trade('a, qa2, klong);
                    assert [?qklong]lifetime_token(klong);
                    lifetime_token_inv(klong);


                    if qklong < 1 { }
                    close_lifetime_intersection_token(qklong, klong, dlft_max);

                    share_full_borrow::<T>(dlft, _t, &(*ref_origin(this)).value);

                    open_lifetime_intersection_token(qklong, klong, dlft_max);

                    start_counting(dlft_pred, gid);

                    lifetime_token_trade_back(qklong, klong);

                    let frac = create_ticket(dlft_pred, gid);
                    open [frac]dlft_pred(gid, Option::Some(dlft_max));
                } else {
                    let frac = create_ticket(dlft_pred, gid);
                }
            @*/
            //@ close na_borrow_content::<T>(ref_origin(this), _t, klong, gid)();
            //@ close_nonatomic_borrow();
            //@ thread_token_merge(_t, mask0, mask);
            //@ close thread_token(_t);
        }
        //@ assert [_](<T>.share)(?dlft, _t, &(*ref_origin(this)).value);
        let r = Ref { refcell: this };
        //@ leak exists(klong);
        //@ close Ref_own::<'a, T>(_t, r);
        r
    }
}

impl<T> Drop for RefCell<T> {
    // When the RefCell is dropped, check if it is still mutably borrowed.
    // If it is, abort.
    fn drop(&mut self) {
        //@ open RefCell_full_borrow_content::<T>(_t, self)();
        //@ open RefCell_own::<T>(_t, ?s);
        unsafe {
            if *self.mutably_borrowed.get() || *self.immutable_borrows.get() != 0 {
                process::abort();
            }
        }
    }
}

/*@

pred_ctor RefMut_bc_rest<'a, T>(cell: *RefMut<'a, T>, refcell: *RefCell<T>, t: thread_id_t, dk: lifetime_t, gid: usize)() =
    RefMut_refcell(cell, refcell) &*&
    [_]nonatomic_borrow('a, t, MaskNshrSingle(ref_origin(refcell)), na_borrow_content::<T>(ref_origin(refcell), t, dk, gid)) &*&
    lifetime_inclusion('a, dk) == true;

pred<'a, T> <RefMut<'a, T>>.own(t, cell) =
    [_]exists::<lifetime_t>(?klong) &*&
    exists(?gid) &*&
    lifetime_inclusion('a, klong) == true &*&
    pointer_within_limits(&(*cell.refcell).value) == true &*&
    full_borrow(klong, <T>.full_borrow_content(t, &(*ref_origin(cell.refcell)).value)) &*&
    [_]nonatomic_borrow('a, t, MaskNshrSingle(ref_origin(cell.refcell)), na_borrow_content::<T>(ref_origin(cell.refcell), t, klong, gid));

lem RefMut_own_mono<'a0, 'a1, T>()
    req type_interp::<T>() &*& RefMut_own::<'a0, T>(?t, ?v) &*& lifetime_inclusion('a1, 'a0) == true;
    ens type_interp::<T>() &*& RefMut_own::<'a1, T>(t, RefMut::<'a1, T> { refcell: v.refcell as *_ });
{
    open RefMut_own::<'a0, T>(t, v);
    assert [_]exists::<lifetime_t>(?klong);
    assert exists::<i32>(?gid);
    lifetime_inclusion_trans('a1, 'a0, klong);
    nonatomic_borrow_mono('a0, 'a1, t, MaskNshrSingle(ref_origin(v.refcell)), na_borrow_content::<T>(ref_origin(v.refcell), t, klong, gid));
    close RefMut_own::<'a1, T>(t, v);
}

@*/

pub struct RefMut<'a, T> {
    refcell: &'a RefCell<T>,
}
impl<'a, T> !Send for RefMut<'a, T> {}
impl<'a, T> !Sync for RefMut<'a, T> {}

impl<'a, T> Drop for RefMut<'a, T> {
    fn drop(&mut self) {
        //@ open RefMut_full_borrow_content::<'a, T>(_t, self)();
        //@ open RefMut_own::<'a, T>(_t, ?s);
        unsafe {
            //@ assert [_]exists::<lifetime_t>(?klong);
            //@ assert [_]exists::<i32>(?gid);
            //@ assert RefMut_refcell::<'a, T>(self, ?cell);
            //@ assert [_]nonatomic_borrow('a, _t, ?mask, na_borrow_content(ref_origin(cell), _t, klong, gid));
            //@ open thread_token(_t);
            //@ thread_token_split(_t, MaskTop, mask);
            //@ open_nonatomic_borrow('a, _t, mask, _q_a);
            //@ open na_borrow_content::<T>(ref_origin(cell), _t, klong, gid)();
            /*@ if !(*ref_origin((*self).refcell)).mutably_borrowed {
                leak full_borrow(klong, _);
            }
            @*/
            *self.refcell.mutably_borrowed.get() = false;

            //@ assert partial_thread_token(_t, ?mask0);
            //@ close na_borrow_content::<T>(ref_origin(cell), _t, klong, gid)();
            //@ close_nonatomic_borrow();
            //@ thread_token_merge(_t, mask0, mask);
            //@ close thread_token(_t);
            //@ close exists(klong);
            //@ close RefCell_share::<T>('a, _t, cell);
            //@ leak RefCell_share::<T>('a, _t, cell);
        }
    }
}

impl<'b, T> DerefMut for RefMut<'b, T> {
    fn deref_mut<'a>(&'a mut self) -> &'a mut T {
        unsafe {
            //@ assert [?qb]lifetime_token('b);
            //@ assert [?qa]lifetime_token('a);
            //@ let kstrong = open_full_borrow_strong('a, RefMut_full_borrow_content::<'b, T>(_t, self), qa);
            //@ open RefMut_full_borrow_content::<'b, T>(_t, self)();
            //@ open RefMut_own::<'b, T>(_t, ?mutcell);
            //@ let refcell = ref_origin(mutcell.refcell);
            //@ assert [_]exists::<lifetime_t>(?k);
            //@ lifetime_inclusion_trans('a, 'b, k);
            //@ lifetime_token_trade('b, _q_b, k);
            //@ assert [?qk]lifetime_token(k);
            //@ open_full_borrow(qk, k, <T>.full_borrow_content(_t, &(*refcell).value));
            //@ open_full_borrow_content::<T>(_t, &(*refcell).value);
            //@ close_full_borrow_content::<T>(_t, &(*refcell).value);
            //@ close_full_borrow(<T>.full_borrow_content(_t, &(*refcell).value));
            //@ lifetime_token_trade_back(qk, k);
            let r = &mut *self.refcell.value.get();
            //@ assert exists::<i32>(?gid);
            /*@
            produce_lem_ptr_chunk full_borrow_convert_strong(True,
                sep(RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, k, gid), full_borrow_(k, <T>.full_borrow_content(_t, &(*refcell).value))),
                kstrong,
                RefMut_full_borrow_content::<'b, T>(_t, self))() {
                    open sep(RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, k, gid), full_borrow_(k, <T>.full_borrow_content(_t, &(*refcell).value)))();
                    open RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, k, gid)();
                    open full_borrow_(k, <T>.full_borrow_content(_t, &(*refcell).value))();
                    close exists(k); leak exists(k);
                    close exists(gid);
                    close RefMut_own::<'b, T>(_t, mutcell);
                    close RefMut_full_borrow_content::<'b, T>(_t, self)();
                }{
                    close RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, k, gid)();
                    close full_borrow_(k, <T>.full_borrow_content(_t, &(*refcell).value))();
                    close sep(RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, k, gid), full_borrow_(k, <T>.full_borrow_content(_t, &(*refcell).value)))();
                    close_full_borrow_strong(kstrong, RefMut_full_borrow_content::<'b, T>(_t, self), sep(RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, k, gid), full_borrow_(k, <T>.full_borrow_content(_t, &(*refcell).value))));
                    full_borrow_split(kstrong, RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, k, gid), full_borrow_(k, <T>.full_borrow_content(_t, &(*refcell).value)));
                    full_borrow_unnest(kstrong, k, <T>.full_borrow_content(_t, &(*refcell).value));
                    lifetime_inclusion_glb('a, kstrong, k);
                    full_borrow_mono(lifetime_intersection(kstrong, k), 'a, <T>.full_borrow_content(_t, &(*refcell).value));
                }
            @*/
            //@ leak full_borrow(kstrong, _);
            r
        }
    }
}

impl<'a, T> Deref for RefMut<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        process::abort();
    }
}

/*@

lem init_ref_Ref<'a, T>(p: *Ref<'a, T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]Ref_share::<'a, T>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]Ref_share::<'a, T>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false);
}

pred_ctor Ref_frac_bc(dlft: lifetime_t)(;) = lifetime_token(dlft);

pred_ctor ticket_(dlft: lifetime_t, gid: i32, frac: real)(;) = ticket(dlft_pred, gid, frac) &*& [frac]ghost_cell(gid, Option::Some(dlft));

pred_ctor points_to__<'a, T>(l: *Ref<'a, T>, cell: *RefCell<T>)(;) = Ref_refcell(l, cell);

pred_ctor Ctx<'a, T>(dlft_max: lifetime_t, klong: lifetime_t, t: thread_id_t, gid: isize, l: *Ref<'a, T>, refcell: *RefCell<T>)() =
    [_]exists(dlft_max) &*& [_]exists(klong) &*& [_]exists::<i32>(gid) &*&
    [_](<T>.share)(lifetime_intersection(klong, dlft_max), t, &(*ref_origin(refcell)).value) &*&
    [_]nonatomic_borrow('a, t, MaskNshrSingle(ref_origin(refcell)), na_borrow_content::<T>(ref_origin(refcell), t, klong, gid));


pred<'a, T> <Ref<'a, T>>.own(t, cell) =
    pointer_within_limits(&(*cell.refcell).value) == true &*&
    [_]exists::<i32>(?gid) &*&
    ticket(dlft_pred, gid, ?frac) &*&
    [frac]dlft_pred(gid, ?o_dlft_max) &*&
    o_dlft_max == Option::Some(?dlft_max) &*&
    [_]exists(?klong) &*&
    lifetime_inclusion('a, klong) == true &*&
    [_](<T>.share)(lifetime_intersection(klong, dlft_max), t, &(*ref_origin(cell.refcell)).value) &*&
    [_]nonatomic_borrow('a, t, MaskNshrSingle(ref_origin(cell.refcell)), na_borrow_content::<T>(ref_origin(cell.refcell), t, klong, gid));

lem Ref_own_mono<'a0, 'a1, T>()
    req type_interp::<T>() &*& Ref_own::<'a0, T>(?t, ?v) &*& lifetime_inclusion('a1, 'a0) == true;
    ens type_interp::<T>() &*& Ref_own::<'a1, T>(t, Ref::<'a1, T> { refcell: v.refcell as *_ });
{
    open Ref_own::<'a0, T>(t, v);
    assert [_]nonatomic_borrow('a0, t, ?m, _) &*& [_]exists::<lifetime_t>(?klong) &*& [_]exists::<i32>(?gid);
    nonatomic_borrow_mono('a0, 'a1, t, m, na_borrow_content(ref_origin(v.refcell), t, klong, gid));
    lifetime_inclusion_trans('a1, 'a0, klong);
    close Ref_own::<'a1, T>(t, v);
}

pred<'a, T> <Ref<'a, T>>.share(k, t, cell) =
    exists::<pair<lifetime_t, lifetime_t>>(pair(?klong, ?dlft_max)) &*&
    lifetime_inclusion('a, klong) == true &*&
    exists(?frac) &*&
    exists(?refcell) &*&
    [_]frac_borrow(k, lifetime_token_(frac, dlft_max)) &*& [_]frac_borrow(k, points_to__(cell, refcell)) &*&
    pointer_within_limits(&(*refcell).value) == true &*&
    [_](<T>.share)(lifetime_intersection(klong, dlft_max), t, &(*ref_origin(refcell)).value);

lem Ref_share_mono<'a, T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *_)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*& [_]Ref_share::<'a, T>(k, t, l);
    ens type_interp::<T>() &*& [_]Ref_share::<'a, T>(k1, t, l);
{
    open [?q]Ref_share::<'a, T>(k, t, l);
    assert [_]exists::<real>(?frac);
    assert [_]exists(pair(?klong, ?dlft_max));
    assert [_]exists(?refcell);

    frac_borrow_mono(k, k1, lifetime_token_(frac, dlft_max));
    frac_borrow_mono(k, k1, points_to__::<'a, T>(l, refcell));

    close [q]Ref_share::<'a, T>(k1, t, l);
}

lem Ref_share_full<'a, T>(k: lifetime_t, t: thread_id_t, l: *Ref<'a, T>)
    req type_interp::<T>() &*& atomic_mask(MaskTop) &*& full_borrow(k, Ref_full_borrow_content::<'a, T>(t, l)) &*& [?q]lifetime_token(k) &*& l == ref_origin(l);
    ens type_interp::<T>() &*& atomic_mask(MaskTop) &*& [_]Ref_share::<'a, T>(k, t, l) &*& [q]lifetime_token(k);
{
    let kborrow = open_full_borrow_strong_m(k, Ref_full_borrow_content(t, l), q);
    open Ref_full_borrow_content::<'a, T>(t, l)();
    open Ref_own::<'a, T>(t, ?refcell);
    let cell = (*l).refcell;
    assert [_]exists::<i32>(?gid) &*& [_]exists::<lifetime_t>(?klong) &*& ticket(dlft_pred, gid, ?frac) &*& [frac]dlft_pred(gid, ?o_dlft_max);
    assert o_dlft_max == Option::Some(?dlft_max);
    close sep(ticket_(dlft_max, gid, frac), lifetime_token_(frac, dlft_max))();
    {
        produce_lem_ptr_chunk full_borrow_convert_strong(Ctx(dlft_max, klong, t, gid, l, cell), sep(points_to__(l, cell), sep(ticket_(dlft_max, gid, frac), lifetime_token_(frac, dlft_max))), kborrow, Ref_full_borrow_content(t, l))() {
            open sep(points_to__(l, cell), sep(ticket_(dlft_max, gid, frac), lifetime_token_(frac, dlft_max)))();
            open sep(ticket_(dlft_max, gid, frac), lifetime_token_(frac, dlft_max))();
            open ticket_(dlft_max, gid, frac)();
            open points_to__::<'a, T>(l, cell)();
            open Ctx::<'a, T>(dlft_max, klong, t, gid, l, cell)();
            close [frac]dlft_pred(gid, Option::Some(dlft_max));
            close Ref_own::<'a, T>(t, refcell);
            close Ref_full_borrow_content::<'a, T>(t, l)();
        } {
            close Ctx::<'a, T>(dlft_max, klong, t, gid, l, cell)();
            close points_to__::<'a, T>(l, cell)();
            close sep(points_to__(l, cell), sep(ticket_(dlft_max, gid, frac), lifetime_token_(frac, dlft_max)))();
            close_full_borrow_strong_m(kborrow, Ref_full_borrow_content(t, l), sep(points_to__(l, cell), sep(ticket_(dlft_max, gid, frac), lifetime_token_(frac, dlft_max))));
        }
        close exists(pair(klong, dlft_max));
        full_borrow_mono(kborrow, k, sep(points_to__(l, cell), sep(ticket_(dlft_max, gid, frac), lifetime_token_(frac, dlft_max))));
        full_borrow_split_m(k, points_to__(l, cell), sep(ticket_(dlft_max, gid, frac), lifetime_token_(frac, dlft_max)));
        full_borrow_split_m(k, ticket_(dlft_max, gid, frac), lifetime_token_(frac, dlft_max));
        leak full_borrow(k, ticket_(dlft_max, gid, frac));
        full_borrow_into_frac_m(k, lifetime_token_(frac, dlft_max));
        full_borrow_into_frac_m(k, points_to__(l, cell));
    }

    close exists(frac);
    close exists::<*RefCell<T>>(cell);
    close Ref_share::<'a, T>(k, t, l);
    leak Ref_share::<'a, T>(k, t, l);
}

@*/

pub struct Ref<'a, T> {
    refcell: &'a RefCell<T>,
}

impl<'a, T> !Send for Ref<'a, T> {}
impl<'a, T> !Sync for Ref<'a, T> {}

impl<'a, T> Drop for Ref<'a, T> {
    fn drop(&mut self) {
        //@ open Ref_full_borrow_content::<'a, T>(_t, self)();
        //@ open Ref_own::<'a, T>(_t, ?s);
        unsafe {
            //@ assert [_]exists::<lifetime_t>(?klong);
            //@ assert [_]exists::<i32>(?gid);
            //@ assert Ref_refcell::<'a, T>(self, ?cell);
            //@ assert [_]nonatomic_borrow('a, _t, ?mask, na_borrow_content(ref_origin(cell), _t, klong, gid));
            //@ open thread_token(_t);
            //@ thread_token_split(_t, MaskTop, mask);
            //@ open_nonatomic_borrow('a, _t, mask, _q_a);
            //@ open na_borrow_content::<T>(ref_origin(cell), _t, klong, gid)();
            let current_borrows = *self.refcell.immutable_borrows.get();
            if let Some(new_borrows) = current_borrows.checked_sub(1) {
                *self.refcell.immutable_borrows.get() = new_borrows;
            } else {
                process::abort();
            }
            //@ assert [?frac]dlft_pred(gid, ?o_dlft_max);
            //@ destroy_ticket(dlft_pred, gid);
            //@ assert partial_thread_token(_t, ?mask0);
            //@ assert counting(dlft_pred, gid, ?immutables, o_dlft_max);
            //@ assert o_dlft_max == Option::Some(?dlft_max);
            /*@ if immutables == 0 {
                    stop_counting(dlft_pred, gid);
                    ghost_cell_mutate::<Option<lifetime_t>>(gid, Option::None);
                    start_counting(dlft_pred, gid);
                    end_lifetime(dlft_max);
                    close_lifetime_intersection_dead_token(dlft_max, klong);
                    lifetime_intersection_symm(dlft_max, klong);
                    end_reborrow(lifetime_intersection(klong, dlft_max), klong,  <T>.full_borrow_content(_t, &(*ref_origin(cell)).value));
                }
            @*/
            //@ close na_borrow_content::<T>(ref_origin(cell), _t, klong, gid)();
            //@ close_nonatomic_borrow();
            //@ thread_token_merge(_t, mask0, mask);
            //@ close thread_token(_t);
            //@ close exists(klong);
            //@ close exists(gid);
            //@ close RefCell_share::<T>('a, _t, cell);
            //@ leak RefCell_share::<T>('a, _t, cell);
        }
    }
}

impl<'b, T> Deref for Ref<'b, T> {
    type Target = T;

    fn deref<'a>(&'a self) -> &T {
        //@ open [?qshr]Ref_share::<'b, T>('a, _t, self);
        //@ assert [_]exists(pair(?klong, ?dlft_max));
        //@ assert [_]exists::<real>(?frac);
        //@ assert [_]exists(?refcell);
        //@ assert [?qfrac]frac_borrow('a, points_to__::<'b, T>(self, refcell));

        unsafe {
            //@ open_frac_borrow('a, points_to__::<'b, T>(self, refcell), _q_a / 2);
            //@ assert [?q_p]points_to__::<'b, T>(self, refcell)();
            //@ open [q_p]points_to__::<'b, T>(self, refcell)();
            let r = &*self.refcell.value.get();
            //@ close [q_p]points_to__::<'b, T>(self, refcell)();
            //@ close_frac_borrow(q_p, points_to__::<'b, T>(self, refcell));
            //@ frac_borrow_lft_incl('a, frac, dlft_max);
            //@ produce_type_interp::<T>();
            //@ lifetime_inclusion_trans('a, 'b, klong);
            //@ lifetime_inclusion_glb('a, klong, dlft_max);
            //@ share_mono(lifetime_intersection(klong, dlft_max), 'a, _t, r);
            //@ leak type_interp::<T>();
            r
        }
    }
}
