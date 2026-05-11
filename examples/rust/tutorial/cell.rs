use std::cell::UnsafeCell;

pub struct Cell<T> { v: UnsafeCell<T> }

/*@
pred<T> <Cell<T>>.own(t, c) = <T>.own(t, c.v);

lem Cell_send<T>(t1: thread_id_t)
    req type_interp::<T>() &*& is_Send(typeid(Cell<T>)) == true &*& <Cell<T>>.own(?t0, ?c);
    ens type_interp::<T>() &*& <Cell<T>>.own(t1, c);
{
    open <Cell<T>>.own(t0, c);
    Send::send(t0, t1, c.v);
    close <Cell<T>>.own(t1, c);
}

fix ro<T>(l: *T) -> *T { ref_origin(l) }
fix Ncell<T>(l: *T) ->  mask_t { MaskNshrSingle(ro(l)) }

pred<T> <Cell<T>>.share(k, t, l) = [_]nonatomic_borrow(k, t, Ncell(l), <Cell<T>>.full_borrow_content(t, ro(l)));

lem Cell_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *_)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*& [_]Cell_share::<T>(k, t, l);
    ens type_interp::<T>() &*& [_]Cell_share::<T>(k1, t, l);
{
    open <Cell<T>>.share(k, t, l);
    nonatomic_borrow_mono(k, k1, t, Ncell(l), <Cell<T>>.full_borrow_content(t, ro(l)));
    close <Cell<T>>.share(k1, t, l); leak <Cell<T>>.share(k1, t, l);
}

lem Cell_share_full<T>(k: lifetime_t, t: thread_id_t, l: *_)
    req type_interp::<T>() &*& atomic_mask(MaskTop) &*&
        full_borrow(k, <Cell<T>>.full_borrow_content(t, l)) &*&
        [?q]lifetime_token(k) &*& ref_origin(l) == l;
    ens type_interp::<T>() &*& atomic_mask(MaskTop) &*&
        [_]Cell_share::<T>(k, t, l) &*& [q]lifetime_token(k);
{
    full_borrow_into_nonatomic_borrow_m(k, t, Ncell(l), <Cell<T>>.full_borrow_content(t, l));
    close <Cell<T>>.share(k, t, l); leak <Cell<T>>.share(k, t, l);
}

lem init_ref_Cell<T>(p: *Cell<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_]Cell_share::<T>(?k, ?t, x) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_]Cell_share::<T>(k, t, p) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    assume(false);
}
@*/

impl<T> Cell<T> {
    pub fn new(v: T) -> Cell<T> {
        let r = Cell {
            v: UnsafeCell::new(v),
        };
        //@ close Cell_own::<T>(_t, r);
        r
    }

    pub fn into_inner(self) -> T {
        //@ open <Cell<T>>.own(_t, self);
        self.v.into_inner()
    }

    pub fn replace<'a>(&'a self, v: T) -> T {
        let p = self.v.get();
        unsafe {
            //@ open <Cell<T>>.share('a, _t, self);
            //@ open thread_token(_t);
            //@ thread_token_split(_t, MaskTop, Ncell(self));
            //@ open_nonatomic_borrow('a, _t, Ncell(self), _q_a);
            //@ open <Cell<T>>.full_borrow_content(_t, ro(self))();
            let old = p.read();
            p.write(v);
            //@ close <Cell<T>>.own(_t, Cell::<T> {v});
            //@ close <Cell<T>>.full_borrow_content(_t, ro(self))();
            //@ close_nonatomic_borrow();
            //@ thread_token_merge(_t, mask_diff(MaskTop, Ncell(self)), Ncell(self));
            //@ close thread_token(_t);
            //@ open <Cell<T>>.own(_t, _);
            old
        }
    }

    pub fn swap<'a>(&'a self, other: &'a Self) {
        if self as *const Cell<T> == other as *const Cell<T> {
            return;
        }
        let ps = self.v.get();
        let po = other.v.get();
        unsafe {
            //@ let ms = Ncell(ro(self));
            //@ let mo = Ncell(ro(other));
            //@ open thread_token(_t);
            //@ thread_token_split(_t, MaskTop, ms);
            //@ thread_token_split(_t, mask_diff(MaskTop, ms), mo);
            //@ open <Cell<T>>.share('a, _t, self);
            //@ open_nonatomic_borrow('a, _t, ms, _q_a/2);
            //@ open <Cell<T>>.full_borrow_content(_t, ro(self))();
            let tmp = ps.read();
            //@ open <Cell<T>>.share('a, _t, other);
            //@ open_nonatomic_borrow('a, _t, mo, _q_a/2);
            //@ open <Cell<T>>.full_borrow_content(_t, ro(other))();
            ps.write(po.read());
            po.write(tmp);
            //@ close <Cell<T>>.full_borrow_content(_t, ro(self))();
            //@ close <Cell<T>>.full_borrow_content(_t, ro(other))();
            //@ assert partial_thread_token(_t, ?m_rem);
            //@ close_nonatomic_borrow();
            //@ close_nonatomic_borrow();
            //@ thread_token_merge(_t, m_rem, mo);
            //@ assert partial_thread_token(_t, ?m_rem_);
            //@ thread_token_merge(_t, m_rem_, ms);
            //@ close thread_token(_t);
        }
    }
}

// needs support for `T: Copy`
// impl<T: Copy> Cell<T> {
//     pub fn get<'a>(&'a self) -> T {
//         unsafe {
//             //@ open <Cell<T>>.share('a, _t, self);
//             //@ open thread_token(_t);
//             //@ let m = Ncell(ro(self));
//             //@ thread_token_split(_t, MaskTop, m);
//             //@ open_nonatomic_borrow('a, _t, m, _q_a);
//             //@ open <Cell<T>>.full_borrow_content(_t, ro(self))();
//             let r = *self.v.get();
//             //@ close <Cell<T>>.full_borrow_content(_t, ro(self))();
//             //@ close_nonatomic_borrow();
//             //@ thread_token_merge(_t, mask_diff(MaskTop, m), m);
//             //@ close thread_token(_t);
//             r
//         }
//     }
// }

/*@
lem Cell_drop<T>()
    req Cell_own::<T>(?t, ?c);
    ens <T>.own(t, c.v);
{
    open <Cell<T>>.own(t, c);
}
@*/
