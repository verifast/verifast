use std::cell::UnsafeCell;

pub struct Cell<T> { v: UnsafeCell<T> }

/*@
pred<T> <Cell<T>>.own(t, c) = <T>.own(t, c.v);
fix ro<T>(l: *T) -> *T { ref_origin(l) }
fix Ncell<T>(l: *T) ->  mask_t { MaskNshrSingle(ro(l)) }
pred<T> <Cell<T>>.share(k, t, l) =
    [_]nonatomic_borrow(k, t, Ncell(l), <Cell<T>>.full_borrow_content(t, ro(l)));

lem Cell_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Cell<T>)
    req type_interp::<T>() &*& lifetime_inclusion(k1, k) == true &*&
        [_](<Cell<T>>.share(k, t, l));
    ens type_interp::<T>() &*& [_](<Cell<T>>.share(k1, t, l));
{
    open <Cell<T>>.share(k, t, l);
    nonatomic_borrow_mono(k, k1, t, Ncell(l), <Cell<T>>.full_borrow_content(t, ro(l)));
    close <Cell<T>>.share(k1, t, l); leak <Cell<T>>.share(k1, t, l);
}

lem Cell_share_full<T>(k: lifetime_t, t: thread_id_t, l: *Cell<T>)
    req type_interp::<T>() &*& atomic_mask(MaskTop) &*&
        full_borrow(k, <Cell<T>>.full_borrow_content(t, l)) &*&
        [?q]lifetime_token(k) &*& ref_origin(l) == l;
    ens type_interp::<T>() &*& atomic_mask(MaskTop) &*&
        [_](<Cell<T>>.share(k, t, l)) &*& [q]lifetime_token(k);
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

    pub fn replace<'a>(&'a self, v: T) -> T
    /*@ req thread_token(?t) &*& [?qa]lifetime_token('a) &*&
        [_](<Cell<T>>.share('a, t, self)) &*& <T>.own(t, v); @*/
    //@ ens thread_token(t) &*& [qa]lifetime_token('a) &*& <T>.own(t, result);
    {
        let p = self.v.get();
        unsafe {
            //@ open <Cell<T>>.share('a, t, self);
            //@ open thread_token(t);
            /*|\begin{vfHeap}
            \vfResAdd{ptt(t, MaskTop)}, \vfResAdd{[qa]lft('a)},
            \vfResAdd{[_]nabor('a, t, Ncell(self), <Cell<T>>.fbc(t, ro(self)))},
            \vfResAdd{<T>.own(t, v)}
            \end{vfHeap}|*/
            //@ thread_token_split(t, MaskTop, Ncell(self));
            /*|\begin{vfHeap}
            [qa]lft('a),
            [_]nabor('a, t, Ncell(self), <Cell<T>>.fbc(t, ro(self))),
            <T>.own(t, v), \vfResRm{ptt(t, MaskTop)},
            \vfResAdd{ptt(t, mask_diff(MaskTop, Ncell(self)))}, \vfResAdd{ptt(t, Ncell(self))}
            \end{vfHeap}|*/
            //@ open_nonatomic_borrow('a, t, Ncell(self), qa);
            /*|\begin{vfHeap}
            <T>.own(t, v), ptt(t, mask_diff(MaskTop, Ncell(self))), \vfResRm{[qa]lft('a)},
            \vfResRm{[_]nabor('a, t, Ncell(self), <Cell<T>>.fbc(t, ro(self)))},
            \vfResRm{ptt(t, Ncell(self))}, \vfResAdd{<Cell<T>>.fbc(t, ro(self))()},
            \vfResAdd{c_nabor_tk(<Cell<T>>.fbc(t, ro(self)), qa, 'a, t, Ncell(self))}
            \end{vfHeap}|*/
            //@ open <Cell<T>>.full_borrow_content(t, ro(self))();
            /*|\begin{vfHeap}
            <T>.own(t, v), ptt(t, mask_diff(MaskTop, Ncell(self))),
            c_nabor_tk(<Cell<T>>.fbc(t, ro(self)), qa, 'a, t, Ncell(self)),
            \vfResRm{<Cell<T>>.fbc(t, ro(self))()}, \vfResAdd{(*ro(self)).v |-> old},
            \vfResAdd{<Cell<T>>.own(t, Cell\{v: old\})}
            \end{vfHeap}|*/
            let old = p.read();
            p.write(v);
            /*|\begin{vfHeap}
            ..., <T>.own(t, v), \vfResRm{(*ro(self)).v |-> old}, \vfResAdd{(*ro(self)).v |-> v}
            \end{vfHeap}|*/
            //@ close <Cell<T>>.own(t, Cell::<T> {v});
            //@ close <Cell<T>>.full_borrow_content(t, ro(self))();
            /*|\begin{vfHeap}
            ..., \vfResRm{(*ro(self)).v |-> v}, \vfResRm{<T>.own(t, v)}, \vfResAdd{<Cell<T>>.fbc(t, ro(self))()}
            \end{vfHeap}|*/
            //@ close_nonatomic_borrow();
            /*|\begin{vfHeap}
            ptt(t, mask_diff(MaskTop, Ncell(self))),
            <Cell<T>>.own(t, Cell\{v: old\}),
            \vfResRm{c_nabor_tk(<Cell<T>>.fbc(t, ro(self)), qa, 'a, t, Ncell(self))},
            \vfResRm{<Cell<T>>.fbc(t, ro(self))()}, \vfResAdd{[qa]lft('a)}, \vfResAdd{ptt(t, Ncell(self))}
            \end{vfHeap}|*/
            //@ thread_token_merge(t, mask_diff(MaskTop, Ncell(self)), Ncell(self));
            /*|\begin{vfHeap}
            <Cell<T>>.own(t, Cell\{v: old\}), [qa]lft('a),
            \vfResRm{ptt(t, mask_diff(MaskTop, Ncell(self)))}, \vfResRm{ptt(t, Ncell(self))},
            \vfResAdd{ptt(t, mask_union(mask_diff(MaskTop, Ncell(self)), Ncell(self)))}
            \end{vfHeap}|*/
            //@ close thread_token(t);
            //@ open <Cell<T>>.own(t, _);
            /*|\begin{vfHeap}
            [qa]lft('a), \vfResRm{<Cell<T>>.own(t, Cell\{v: old\})},
            \vfResRm{ptt(t, mask_union(mask_diff(MaskTop, Ncell(self)), Ncell(self)))},
            \vfResAdd{thread_token(t)}, \vfResAdd{<T>.own(t, old)}
            \end{vfHeap}|*/
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

lem Cell_send<T>(t1: thread_id_t)
    req type_interp::<T>() &*& is_Send(typeid(Cell<T>)) == true &*& <Cell<T>>.own(?t0, ?c);
    ens type_interp::<T>() &*& <Cell<T>>.own(t1, c);
{
    open <Cell<T>>.own(t0, c);
    Send::send(t0, t1, c.v);
    close <Cell<T>>.own(t1, c);
}
@*/
