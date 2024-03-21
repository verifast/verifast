#![allow(dead_code)]

pub struct Cell<T> {
    v: std::cell::UnsafeCell<T>,
}

/*@

pred Cell_own<T>(t: thread_id_t, v: T) = <T>.own(t, v);

/*

A note on `|= cell(tau) copy` judgement:
In RustBelt `|= tau copy => |= cell(tau) copy` but it is not the case in Rust as it is prohibited
exceptionally for preventing potential pitfalls.
The real `Cell<T>` in std library will have the `get` method if `tau copy` syn-typing judgement
is derivable.

*/

pred_ctor Cell_nonatomic_borrow_content<T>(l: *Cell<T>, t: thread_id_t)() =
  Cell_v(l, ?v) &*& struct_Cell_padding(l) &*& Cell_own(t, v);

// `SHR` for Cell<u32>
pred Cell_share<T>(k: lifetime_t, t: thread_id_t, l: *Cell<T>) =
  [_]nonatomic_borrow(k, t, MaskNshrSingle(l), Cell_nonatomic_borrow_content(l, t));

// Proof obligations
lem Cell_share_mono<T>(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *Cell<T>)
  req lifetime_inclusion(k1, k) == true &*& [_]Cell_share(k, t, l);
  ens [_]Cell_share(k1, t, l);
{
  open Cell_share(k, t, l);
  assert [_]nonatomic_borrow(k, t, ?m, _);
  nonatomic_borrow_mono(k, k1, t, m, Cell_nonatomic_borrow_content(l, t));
  close Cell_share(k1, t, l);
  leak Cell_share(k1, t, l);
}

lem Cell_share_full<T>(k: lifetime_t, t: thread_id_t, l: *Cell<T>)
  req atomic_mask(Nlft) &*& full_borrow(k, Cell_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
  ens atomic_mask(Nlft) &*& [_]Cell_share(k, t, l) &*& [q]lifetime_token(k);
{
  produce_lem_ptr_chunk implies(Cell_full_borrow_content(t, l), Cell_nonatomic_borrow_content(l, t))() {
    open Cell_full_borrow_content::<T>(t, l)();
    close Cell_nonatomic_borrow_content::<T>(l, t)();
  } {
    produce_lem_ptr_chunk implies(Cell_nonatomic_borrow_content(l, t), Cell_full_borrow_content(t, l))() {
      open Cell_nonatomic_borrow_content::<T>(l, t)();
      close Cell_full_borrow_content::<T>(t, l)();
    } {
      full_borrow_implies(k, Cell_full_borrow_content(t, l), Cell_nonatomic_borrow_content(l, t));
    }
  }
  full_borrow_into_nonatomic_borrow_m(k, t, MaskNshrSingle(l), Cell_nonatomic_borrow_content(l, t));
  close Cell_share(k, t, l);
  leak Cell_share(k, t, l);
}
@*/

impl<T> Cell<T> {

    fn new(v: T) -> Cell<T> {
        let c = Cell {
            v: std::cell::UnsafeCell::new(v),
        };
        //@ close Cell_own::<T>(_t, v);
        c
    }
    
    fn replace<'a>(&'a self, v: T) -> T {
        unsafe {
            //@ open Cell_share(a, _t, self);
            //@ assert [_]nonatomic_borrow(a, _t, ?mask, Cell_nonatomic_borrow_content(self, _t));
            //@ open thread_token(_t);
            //@ thread_token_split(_t, MaskTop, mask);
            //@ open_nonatomic_borrow(a, _t, mask, _q_a);
            //@ open Cell_nonatomic_borrow_content::<T>(self, _t)();
            //@ open Cell_own::<T>(_t, ?v0);
            //@ open Cell_v(self, v0);
            let result = std::ptr::read(self.v.get());
            std::ptr::write(self.v.get(), v);
            //@ assert partial_thread_token(_t, ?mask0);
            //@ close Cell_v(self, v);
            //@ close Cell_own::<T>(_t, v);
            //@ close Cell_nonatomic_borrow_content::<T>(self, _t)();
            //@ close_nonatomic_borrow();
            //@ thread_token_merge(_t, mask0, mask);
            //@ close thread_token(_t);
            result
        }
    }

    fn swap<'a>(&'a self, other: &'a Self) {
        //@ open Cell_share(a, _t, self);
        //@ open Cell_share(a, _t, other);
        if self as *const Cell<T> == other as *const Cell<T> {
            return;
        }
        //@ assert [_]nonatomic_borrow(a, _t, ?ms, Cell_nonatomic_borrow_content(self, _t));
        //@ assert [_]nonatomic_borrow(a, _t, ?mo, Cell_nonatomic_borrow_content(other, _t));
        //@ open thread_token(_t);
        //@ thread_token_split(_t, MaskTop, ms);
        //@ thread_token_split(_t, mask_diff(MaskTop, ms), mo);
        //@ open_nonatomic_borrow(a, _t, ms, _q_a/2);
        //@ open Cell_nonatomic_borrow_content::<T>(self, _t)();
        //@ open Cell_v(self, ?vs);
        //@ open_nonatomic_borrow(a, _t, mo, _q_a/2);
        //@ open Cell_nonatomic_borrow_content::<T>(other, _t)();
        //@ open Cell_v(other, ?vo);
        let ps = self.v.get();
        let po = other.v.get();
        unsafe {
            let tmp = std::ptr::read(po);
            std::ptr::write(po, std::ptr::read(ps));
            std::ptr::write(ps, tmp);
        }
        //@ close Cell_v(other, vs);
        //@ close Cell_nonatomic_borrow_content::<T>(other, _t)();
        //@ close Cell_v(self, vo);
        //@ close Cell_nonatomic_borrow_content::<T>(self, _t)();
        //@ assert partial_thread_token(_t, ?rem);
        //@ close_nonatomic_borrow();
        //@ close_nonatomic_borrow();
        //@ thread_token_merge(_t, rem, mo);
        //@ thread_token_merge(_t, mask_diff(MaskTop, ms), ms);
        //@ close thread_token(_t);
    }
}
