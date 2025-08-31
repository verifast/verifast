// verifast_options{ignore_ref_creation}

#![allow(dead_code)]

use std::cell::UnsafeCell;

pub struct Cell<T> {
    v: UnsafeCell<T>,
}

/*@

pred<T> <Cell<T>>.own(t, cell) = <T>.own(t, cell.v);

lem Cell_send<T>(t1: thread_id_t)
    req type_interp::<T>() &*& <Cell<T>>.own(?t0, ?cell) &*& is_Send(typeid(T)) == true;
    ens type_interp::<T>() &*& <Cell<T>>.own(t1, cell);
{
    open <Cell<T>>.own(t0, cell);
    Send::send(t0, t1, cell.v);
    close <Cell<T>>.own(t1, cell);
}

pred<T> <Cell<T>>.share(k, t, l) =
  [_]nonatomic_borrow(k, t, MaskNshrSingle(ref_origin(l)), <Cell<T>>.full_borrow_content(t, ref_origin(l)));

lem Cell_share_full<T>(k: lifetime_t, t: thread_id_t, l: *Cell<T>)
  req atomic_mask(MaskTop) &*& full_borrow(k, <Cell<T>>.full_borrow_content(t, l)) &*& [?q]lifetime_token(k) &*& ref_origin(l) == l;
  ens atomic_mask(MaskTop) &*& [_](<Cell<T>>.share(k, t, l)) &*& [q]lifetime_token(k);
{
  full_borrow_into_nonatomic_borrow_m(k, t, MaskNshrSingle(ref_origin(l)), <Cell<T>>.full_borrow_content(t, l));
  close <Cell<T>>.share(k, t, l);
  leak <Cell<T>>.share(k, t, l);
}

lem Cell_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Cell<T>)
  req lifetime_inclusion(k1, k) == true &*& [_](<Cell<T>>.share(k, t, l));
  ens [_](<Cell<T>>.share(k1, t, l));
{
  open <Cell<T>>.share(k, t, l);
  nonatomic_borrow_mono(k, k1, t, MaskNshrSingle(ref_origin(l)), <Cell<T>>.full_borrow_content(t, ref_origin(l)));
  close <Cell<T>>.share(k1, t, l);
  leak <Cell<T>>.share(k1, t, l);
}

lem init_ref_Cell<T>(p: *Cell<T>)
    req type_interp::<T>() &*& atomic_mask(Nlft) &*& ref_init_perm(p, ?x) &*& [_](<Cell<T>>.share(?k, ?t, x)) &*& [?q]lifetime_token(k);
    ens type_interp::<T>() &*& atomic_mask(Nlft) &*& [q]lifetime_token(k) &*& [_](<Cell<T>>.share(k, t, p)) &*& [_]frac_borrow(k, ref_initialized_(p));
{
    open <Cell<T>>.share(k, t, x);
    close <Cell<T>>.share(k, t, p);
    leak <Cell<T>>.share(k, t, p);
    
    open_ref_init_perm_Cell(p);
    close_ref_initialized_Cell(p, 1/2);
    
    close [1/2]ref_initialized_::<Cell<T>>(p)();
    close scaledp(1/2, ref_initialized_(p))();
    borrow_m(k, scaledp(1/2, ref_initialized_(p)));
    full_borrow_into_frac_m(k, scaledp(1/2, ref_initialized_(p)));
    frac_borrow_implies_scaled(k, 1/2, ref_initialized_(p));
    leak borrow_end_token(_, _);
}

@*/

impl<T> Cell<T> {

    fn new(v: T) -> Cell<T> {
        let c = Cell {
            v: UnsafeCell::new(v),
        };
        //@ close <Cell<T>>.own(_t, c);
        c
    }
    
    fn replace<'a>(&'a self, v: T) -> T {
        unsafe {
            //@ open <Cell<T>>.share('a, _t, self);
            //@ open thread_token(_t);
            //@ let mask = MaskNshrSingle(ref_origin(self));
            //@ thread_token_split(_t, MaskTop, mask);
            //@ open_nonatomic_borrow('a, _t, mask, _q_a);
            //@ open <Cell<T>>.full_borrow_content(_t, ref_origin(self))();
            //@ open <Cell<T>>.own(_t, ?cell);
            let result = self.v.get().read();
            self.v.get().write(v);
            //@ assert partial_thread_token(_t, ?mask1);
            //@ close <Cell<T>>.own(_t, Cell::<T> { v });
            //@ close <Cell<T>>.full_borrow_content(_t, ref_origin(self))();
            //@ close_nonatomic_borrow();
            //@ thread_token_merge(_t, mask1, mask);
            //@ close thread_token(_t);
            result
        }
    }

    fn swap<'a>(&'a self, other: &'a Self) {
        //@ open <Cell<T>>.share('a, _t, self);
        //@ open <Cell<T>>.share('a, _t, other);
        if self as *const Cell<T> == other as *const Cell<T> {
            return;
        }
        //@ let ms = MaskNshrSingle(ref_origin(self));
        //@ let mo = MaskNshrSingle(ref_origin(other));
        //@ open thread_token(_t);
        //@ thread_token_split(_t, MaskTop, ms);
        //@ thread_token_split(_t, mask_diff(MaskTop, ms), mo);
        //@ open_nonatomic_borrow('a, _t, ms, _q_a/2);
        //@ open <Cell<T>>.full_borrow_content(_t, ref_origin(self))();
        //@ open_nonatomic_borrow('a, _t, mo, _q_a/2);
        //@ open <Cell<T>>.full_borrow_content(_t, ref_origin(other))();
        let ps = self.v.get();
        let po = other.v.get();
        unsafe {
            let tmp = po.read();
            po.write(ps.read());
            ps.write(tmp);
        }
        //@ close <Cell<T>>.full_borrow_content(_t, ref_origin(other))();
        //@ close <Cell<T>>.full_borrow_content(_t, ref_origin(self))();
        //@ assert partial_thread_token(_t, ?mr);
        //@ close_nonatomic_borrow();
        //@ close_nonatomic_borrow();
        //@ thread_token_merge(_t, mr, mo);
        //@ thread_token_merge(_t, mask_diff(MaskTop, ms), ms);
        //@ close thread_token(_t);
    }
}

impl<T> Drop for Cell<T> {

    fn drop<'a>(self: &'a mut Cell<T>) {
        //@ open <Cell<T>>.full_borrow_content(_t, self)();
        //@ open <Cell<T>>.own(_t, ?v);
    }

}
