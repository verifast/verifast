#![allow(dead_code)]

pub struct CellU32 {
    v: std::cell::UnsafeCell<u32>,
}
/*@
// Interpretation
// `OWN` for Cell<u32>
// [[cell(tau)]].OWN(t, vs) = [[tau]].OWN(t, vs)
pred CellU32_own(t: thread_id_t, v: u32;) = true; // The `v` parameter type carries the info

/* A note on `|= cell(tau) copy` judgement:
In RustBelt `|= tau copy => |= cell(tau) copy` but it is not the case in Rust as it is prohibited
exceptionally for preventing potential pitfalls.
The real `Cell<T>` in std library will have the `get` method if `tau copy` syn-typing judgement
is derivable. Here, u32 is obviously copy and we are providing the `get` method.
However, we do not need `|= u32 copy` explicitly because VeriFast allows copying integer values,
i.e. in VeriFast the `[[u32]].OWN` is implicitly persistent.
*/

pred_ctor CellU32_nonatomic_borrow_content(l: *CellU32, t: thread_id_t)(;) =
  (*l).v |-> ?v &*& struct_CellU32_padding(l);

// `SHR` for Cell<u32>
pred CellU32_share(k: lifetime_t, t: thread_id_t, l: *CellU32) =
  [_]nonatomic_borrow(k, t, MaskNshrSingle(l), CellU32_nonatomic_borrow_content(l, t));

// Proof obligations
lem CellU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *CellU32)
  req lifetime_inclusion(k1, k) == true &*& [_]CellU32_share(k, t, l);
  ens [_]CellU32_share(k1, t, l);
{
  open CellU32_share(k, t, l);
  assert [_]nonatomic_borrow(k, t, ?m, _);
  nonatomic_borrow_mono(k, k1, t, m, CellU32_nonatomic_borrow_content(l, t));
  close CellU32_share(k1, t, l);
  leak CellU32_share(k1, t, l);
}

lem CellU32_share_full(k: lifetime_t, t: thread_id_t, l: *CellU32)
  req atomic_mask(Nlft) &*& full_borrow(k, CellU32_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
  ens atomic_mask(Nlft) &*& [_]CellU32_share(k, t, l) &*& [q]lifetime_token(k);
{
  produce_lem_ptr_chunk implies(CellU32_full_borrow_content(t, l), CellU32_nonatomic_borrow_content(l, t))() {
    open CellU32_full_borrow_content(t, l)();
    close CellU32_nonatomic_borrow_content(l, t)();
  } {
    produce_lem_ptr_chunk implies(CellU32_nonatomic_borrow_content(l, t), CellU32_full_borrow_content(t, l))() {
      open CellU32_nonatomic_borrow_content(l, t)();
      close CellU32_full_borrow_content(t, l)();
    } {
      full_borrow_implies(k, CellU32_full_borrow_content(t, l), CellU32_nonatomic_borrow_content(l, t));
    }
  }
  full_borrow_into_nonatomic_borrow_m(k, t, MaskNshrSingle(l), CellU32_nonatomic_borrow_content(l, t));
  close CellU32_share(k, t, l);
  leak CellU32_share(k, t, l);
}
@*/

impl CellU32 {
    pub fn new(u: u32) -> CellU32 {
        let c = CellU32 {
            v: std::cell::UnsafeCell::new(u),
        };
        //@ close CellU32_own(_t, u);
        c
    }

    /* VeriFast generates the contract of the safe functions based on the function's semantic type */
    pub fn get<'a>(&'a self) -> u32 {
        //@ open CellU32_share(a, _t, self);
        //@ assert [_]nonatomic_borrow(a, _t, ?_m, _);
        //@ open thread_token(_t);
        //@ thread_token_split(_t, MaskTop, _m);
        //@ open_nonatomic_borrow(a, _t, _m, _q_a);
        let v = unsafe { *self.v.get() };
        //@ close_nonatomic_borrow();
        //@ thread_token_merge(_t, mask_diff(MaskTop, _m), _m);
        //@ close thread_token(_t);
        v
    }

    /* User can also write the contract of safe functions to have it explicit.
    Verifast would check the compatibility of the contract with the function semantic type. */
    pub fn set<'a>(&'a self, u: u32)
    //@ req thread_token(?t) &*& [?q]lifetime_token(?a) &*& [_]CellU32_share(a, t, self);
    //@ ens thread_token(t) &*& [q]lifetime_token(a);
    {
        let p = self.v.get();
        //@ open CellU32_share(a, t, self);
        //@ assert [_]nonatomic_borrow(a, t, ?m, _);
        //@ open thread_token(t);
        //@ thread_token_split(t, MaskTop, m);
        //@ open_nonatomic_borrow(a, t, m, q);
        unsafe {
            *p = u;
        }
        //@ close_nonatomic_borrow();
        //@ thread_token_merge(t, mask_diff(MaskTop, m), m);
        //@ close thread_token(t);
    }

    pub fn swap<'a>(&'a self, other: &'a Self) {
        //@ open CellU32_share(a, _t, self);
        //@ open CellU32_share(a, _t, other);
        if self as *const CellU32 == other as *const CellU32 {
            return;
        }
        //@ assert [_]nonatomic_borrow(a, _t, ?ms, CellU32_nonatomic_borrow_content(self, _t));
        //@ assert [_]nonatomic_borrow(a, _t, ?mo, CellU32_nonatomic_borrow_content(other, _t));
        //@ open thread_token(_t);
        //@ thread_token_split(_t, MaskTop, ms);
        //@ thread_token_split(_t, mask_diff(MaskTop, ms), mo);
        //@ open_nonatomic_borrow(a, _t, ms, _q_a/2);
        //@ open_nonatomic_borrow(a, _t, mo, _q_a/2);
        let ps = self.v.get();
        let po = other.v.get();
        unsafe {
            let tmp = *po;
            *po = *ps;
            *ps = tmp;
        }
        //@ assert partial_thread_token(_t, ?rem);
        //@ close_nonatomic_borrow();
        //@ close_nonatomic_borrow();
        //@ thread_token_merge(_t, rem, mo);
        //@ thread_token_merge(_t, mask_diff(MaskTop, ms), ms);
        //@ close thread_token(_t);
    }
}
