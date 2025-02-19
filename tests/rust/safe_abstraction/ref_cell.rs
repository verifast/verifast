// verifast_options{ignore_ref_creation}

use std::cell::UnsafeCell;
use std::process;

/*
 * This RefCell is a simplified version of RefCell from the standard library
 * that supports only mutable borrows (borrow_mut), using only UnsafeCell.
 * Todo: Extend to support immutable borrows
 */
pub struct RefCell<T> {
    value: UnsafeCell<T>, // The value being stored. Mutable even when the RefCell is immutable.
    mutably_borrowed: UnsafeCell<bool>, // Tracks whether a mutable borrow is active, using UnsafeCell for interior mutability.
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
    assume(false);
}
pred<T> <RefCell<T>>.own(t, cell) = <T>.own(t, cell.value);

pred_ctor na_borrow_content<T>(ptr: *RefCell<T>, t: thread_id_t, k: lifetime_t)() =
    RefCell_mutably_borrowed(ptr, ?borrowed) &*&
    pointer_within_limits(&(*ptr).mutably_borrowed) == true &*&
    pointer_within_limits(&(*ptr).value) == true &*&
    if borrowed { true }
    else {
        full_borrow(k, <T>.full_borrow_content(t, &(*ptr).value))
    };

pred<T> <RefCell<T>>.share(k, t, l) =
    exists(?dk) &*&
    lifetime_inclusion(k, dk) == true &*&
    [_]nonatomic_borrow(k, t, MaskNshrSingle(ref_origin(l)), na_borrow_content(ref_origin(l), t, dk));


lem RefCell_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *RefCell<T>)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*& [_]RefCell_share::<T>(k, t, l);
    ens type_interp::<T>() &*& [_]RefCell_share::<T>(k1, t, l);
{
    open [?df]RefCell_share::<T>(k, t, l);
    assert [_]nonatomic_borrow(k, t, ?m, _) &*& [_]exists(?dk);
    nonatomic_borrow_mono(k, k1, t, m, na_borrow_content(ref_origin(l), t, dk));
    lifetime_inclusion_trans(k1, k, dk);
    close [df]RefCell_share::<T>(k1, t, l);
}
pred_ctor RefCell_padding<T>(l: *RefCell<T>)(;) = struct_RefCell_padding(l);

lem RefCell_share_full<T>(k: lifetime_t, t: thread_id_t, l: *RefCell<T>)
    req type_interp::<T>() &*& atomic_mask(MaskTop) &*& full_borrow(k, RefCell_full_borrow_content::<T>(t, l)) &*& [?q]lifetime_token(k) &*& l == ref_origin(l);
    ens type_interp::<T>() &*& atomic_mask(MaskTop) &*& [_]RefCell_share::<T>(k, t, l) &*& [q]lifetime_token(k);
{
    produce_lem_ptr_chunk implies(RefCell_full_borrow_content(t, l), sep(RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutably_borrowed))))() {
        open RefCell_full_borrow_content::<T>(t, l)();
        assert (*l).value |-> ?value &*& (*l).mutably_borrowed |-> ?mutably_borrowed;
        open RefCell_own::<T>()(t, RefCell::<T> { value, mutably_borrowed });

        close_full_borrow_content::<T>(t, &(*l).value);
        close bool_full_borrow_content(t, &(*l).mutably_borrowed)();
        close sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutably_borrowed))();
        close RefCell_padding::<T>(l)();
        close sep(RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutably_borrowed)))();
    } {
        produce_lem_ptr_chunk implies(sep(RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutably_borrowed))), RefCell_full_borrow_content(t, l))() {
            open sep(RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutably_borrowed)))();
            open RefCell_padding::<T>(l)();
            open sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutably_borrowed))();
            open_full_borrow_content::<T>(t, &(*l).value);
            open bool_full_borrow_content(t, &(*l).mutably_borrowed)();
            assert (*l).value |-> ?value &*& (*l).mutably_borrowed |-> ?mutably_borrowed;
            close RefCell_own::<T>(t, RefCell::<T> { value: value, mutably_borrowed: mutably_borrowed });
            close RefCell_full_borrow_content::<T>(t, l)();
        } {
            full_borrow_implies(k, RefCell_full_borrow_content(t, l), sep(RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutably_borrowed))));
        }
    }
    full_borrow_split_m(k, RefCell_padding(l), sep(<T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutably_borrowed)));
    full_borrow_split_m(k, <T>.full_borrow_content(t, &(*l).value), bool_full_borrow_content(t, &(*l).mutably_borrowed)); // LFTL-BOR-SPLIT
    open_full_borrow_m(q, k, <T>.full_borrow_content(t, &(*l).value));
    open_full_borrow_content(t, &(*l).value);
    points_to_limits(&(*l).value);
    close_full_borrow_content(t, &(*l).value);
    close_full_borrow_m(<T>.full_borrow_content(t, &(*l).value));


    let kstrong = open_full_borrow_strong_m(k, bool_full_borrow_content(t, &(*l).mutably_borrowed), q); // LFTL-BOR-ACC-STRONG
    produce_lem_ptr_chunk full_borrow_convert_strong(True, na_borrow_content(l, t, k), kstrong, bool_full_borrow_content(t, &(*l).mutably_borrowed))() {
        open na_borrow_content::<T>(l, t, k)();
        if (*l).mutably_borrowed == false {
            leak full_borrow(_, <T>.full_borrow_content(t, &(*l).value));
        }
        close bool_full_borrow_content(t, &(*l).mutably_borrowed)();
    }{
        open bool_full_borrow_content(t, &(*l).mutably_borrowed)();
        close exists(k);

        if (*l).mutably_borrowed == true {
            leak full_borrow(_, <T>.full_borrow_content(t, &(*l).value));
        }
        points_to_limits(&(*l).mutably_borrowed);
        close na_borrow_content::<T>(l, t, k)();
        close_full_borrow_strong_m(kstrong, bool_full_borrow_content(t, &(*l).mutably_borrowed), na_borrow_content(l, t, k));
        full_borrow_into_nonatomic_borrow_m(kstrong, t, MaskNshrSingle(l), na_borrow_content(l, t, k));
        nonatomic_borrow_mono(kstrong, k, t, MaskNshrSingle(l), na_borrow_content(l, t, k));
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
        };
        //@ close RefCell_own::<T>(_t, r);
        r
    }

    pub fn borrow_mut<'a>(this: &'a Self) -> RefMut<'a, T> {
        //@ open RefCell_share::<T>()('a, _t, this);
        unsafe {
            //@ assert [_]exists::<lifetime_t>(?dk);
            //@ assert [_]nonatomic_borrow('a, _t, ?mask, na_borrow_content(ref_origin(this), _t, dk));
            //@ open thread_token(_t);
            //@ thread_token_split(_t, MaskTop, mask);
            //@ open_nonatomic_borrow('a, _t, mask, _q_a);
            //@ open na_borrow_content::<T>(ref_origin(this), _t, dk)();
            if *this.mutably_borrowed.get() == false {
                *this.mutably_borrowed.get() = true;
            } else {
                process::abort();
            }
        }
        //@ assert partial_thread_token(_t, ?mask0);
        //@ close na_borrow_content::<T>(ref_origin(this), _t, dk)();
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
}

impl<T> Drop for RefCell<T> {
    // When the RefCell is dropped, check if it is still mutably borrowed.
    // If it is, abort.
    fn drop(&mut self) {
        //@ assume(self == ref_origin(self)); // TODO: eliminate
        //@ open RefCell_full_borrow_content::<T>(_t, self)();
        //@ open RefCell_own::<T>(_t, ?s);
        unsafe {
            if *self.mutably_borrowed.get() {
                process::abort();
            }
        }
    }
}

/*@

pred<'a, T> <RefMut<'a, T>>.own(t, cell) =
    [_]exists(?dk) &*&
    lifetime_inclusion('a, dk) == true &*&
    pointer_within_limits(&(*cell.refcell).value) == true &*&
    full_borrow(dk, <T>.full_borrow_content(t, &(*ref_origin(cell.refcell)).value)) &*&
    [_]nonatomic_borrow('a, t, MaskNshrSingle(ref_origin(cell.refcell)), na_borrow_content::<T>(ref_origin(cell.refcell), t, dk));
@*/
// Struct to represent a mutable borrow
pub struct RefMut<'a, T> {
    refcell: &'a RefCell<T>,
}

/*@

lem RefMut_own_mono<'a0, 'a1, T>()
    req type_interp::<T>() &*& RefMut_own::<'a0, T>(?t, ?v) &*& lifetime_inclusion('a1, 'a0) == true;
    ens type_interp::<T>() &*& RefMut_own::<'a1, T>(t, RefMut::<'a1, T> { refcell: v.refcell as *_ });
{
    assume(false);
}

lem RefMut_send<'a, T>(t1: thread_id_t)
    req type_interp::<T>() &*& RefMut_own::<'a, T>(?t0, ?v);
    ens type_interp::<T>() &*& RefMut_own::<'a, T>(t1, v);
{
    assume(false);
}

@*/

// When dropped, reset the mutably_borrowed flag
impl<'a, T> Drop for RefMut<'a, T> {
    fn drop(&mut self) {
        //@ open RefMut_full_borrow_content::<'a, T>(_t, self)();
        //@ open RefMut_own::<'a, T>(_t, ?s);
        unsafe {
            //@ assert [_]exists::<lifetime_t>(?dk);
            //@ assert RefMut_refcell::<'a, T>(self, ?cell);
            //@ assert [_]nonatomic_borrow('a, _t, ?mask, na_borrow_content(ref_origin(cell), _t, dk));
            //@ open thread_token(_t);
            //@ thread_token_split(_t, MaskTop, mask);
            //@ open_nonatomic_borrow('a, _t, mask, _q_a);
            //@ open na_borrow_content::<T>(ref_origin(cell), _t, dk)();
            /*@ if !(*ref_origin((*self).refcell)).mutably_borrowed {
                leak full_borrow(dk, _);
            }
            @*/
            *self.refcell.mutably_borrowed.get() = false;
            //@ assert partial_thread_token(_t, ?mask0);
            //@ close na_borrow_content::<T>(ref_origin(cell), _t, dk)();
            //@ close_nonatomic_borrow();
            //@ thread_token_merge(_t, mask0, mask);
            //@ close thread_token(_t);
            //@ close exists(dk);
            //@ close RefCell_share::<T>('a, _t, cell);
            //@ leak RefCell_share::<T>('a, _t, cell);

        }
    }
}

/*@
pred_ctor RefMut_bc_rest<'a, T>(cell: *RefMut<'a, T>, refcell: *RefCell<T>, t: thread_id_t, dk: lifetime_t)() =
    RefMut_refcell(cell, refcell) &*&
    [_]nonatomic_borrow('a, t, MaskNshrSingle(ref_origin(refcell)), na_borrow_content::<T>(ref_origin(refcell), t, dk)) &*&
    lifetime_inclusion('a, dk) == true;
@*/
impl<'b, T> std::ops::DerefMut for RefMut<'b, T> {
    fn deref_mut<'a>(&'a mut self) -> &'a mut T {
        unsafe {
            //@ assert [?qb]lifetime_token('b);
            //@ assert [?qa]lifetime_token('a);
            //@ let kstrong = open_full_borrow_strong('a, RefMut_full_borrow_content::<'b, T>(_t, self), qa);
            //@ open RefMut_full_borrow_content::<'b, T>(_t, self)();
            //@ open RefMut_own::<'b, T>(_t, ?mutcell);
            //@ let refcell = ref_origin(mutcell.refcell);
            //@ assert [_]exists(?dk);
            //@ lifetime_inclusion_trans('a, 'b, dk);
            //@ lifetime_token_trade('b, _q_b, dk);
            //@ assert [?qdk]lifetime_token(dk);
            //@ open_full_borrow(qdk, dk, <T>.full_borrow_content(_t, &(*refcell).value));
            //@ open_full_borrow_content::<T>(_t, &(*refcell).value);
            //@ close_full_borrow_content::<T>(_t, &(*refcell).value);
            //@ close_full_borrow(<T>.full_borrow_content(_t, &(*refcell).value));
            //@ lifetime_token_trade_back(qdk, dk);
            let r = &mut *self.refcell.value.get();
            /*@
            produce_lem_ptr_chunk full_borrow_convert_strong(True,
                sep(RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, dk), full_borrow_(dk, <T>.full_borrow_content(_t, &(*refcell).value))),
                kstrong,
                RefMut_full_borrow_content::<'b, T>(_t, self))() {
                    open sep(RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, dk), full_borrow_(dk, <T>.full_borrow_content(_t, &(*refcell).value)))();
                    open RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, dk)();
                    open full_borrow_(dk, <T>.full_borrow_content(_t, &(*refcell).value))();
                    close exists(dk); leak exists(dk);
                    close RefMut_own::<'b, T>(_t, mutcell);
                    close RefMut_full_borrow_content::<'b, T>(_t, self)();
                }{
                    close RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, dk)();
                    close full_borrow_(dk, <T>.full_borrow_content(_t, &(*refcell).value))();
                    close sep(RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, dk), full_borrow_(dk, <T>.full_borrow_content(_t, &(*refcell).value)))();
                    close_full_borrow_strong(kstrong, RefMut_full_borrow_content::<'b, T>(_t, self), sep(RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, dk), full_borrow_(dk, <T>.full_borrow_content(_t, &(*refcell).value))));
                    full_borrow_split(kstrong, RefMut_bc_rest::<'b, T>(self, mutcell.refcell, _t, dk), full_borrow_(dk, <T>.full_borrow_content(_t, &(*refcell).value)));
                    full_borrow_unnest(kstrong, dk, <T>.full_borrow_content(_t, &(*refcell).value));
                    lifetime_inclusion_glb('a, kstrong, dk);
                    full_borrow_mono(lifetime_intersection(kstrong, dk), 'a, <T>.full_borrow_content(_t, &(*refcell).value));
                }
            @*/
            //@ leak full_borrow(kstrong, _);
            r
        }
    }
}

// Ignore Deref for now //Todo: implement
impl<'a, T> std::ops::Deref for RefMut<'a, T> {
    type Target = T;

    fn deref(&self) -> &T {
        process::abort();
    }
}


