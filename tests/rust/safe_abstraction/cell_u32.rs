#![allow(dead_code)]

pub struct CellU32 {
    v: std::cell::UnsafeCell<u32>,
}
/*@
// Interpretation
// `OWN` for Cell<u32>
// [[cell(tau)]].OWN(t, vs) = [[tau]].OWN(t, vs)
pred CellU32_own(t: thread_id_t, v: u32) = true; // The `v` parameter type carries the info

/* A note on `|= cell(tau) copy` judgement:
In RustBelt `|= tau copy => |= cell(tau) copy` but it is not the case in Rust as it is prohibited
exceptionally for preventing potential pitfalls.
The real `Cell<T>` in std library will have the `get` method if `tau copy` syn-typing judgement
is derivable. Here, u32 is obviously copy and we are providing the `get` method.
However, we do not need `|= u32 copy` explicitly because VeriFast allows copying integer values,
i.e. in VeriFast the `[[u32]].OWN` is implicitly persistent.
*/

pred_ctor CellU32_nonatomic_borrow_content(l: *CellU32, t: thread_id_t)() =
  CellU32_v(l, ?v) &*& struct_CellU32_padding(l) &*& CellU32_own(t, v);

// `SHR` for Cell<u32>
pred CellU32_share(k: lifetime_t, t: thread_id_t, l: *CellU32) =
  [_]nonatomic_borrow(k, t, CellU32_nonatomic_borrow_content(l, t));

// Proof obligations
lem CellU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *CellU32)
  req lifetime_inclusion(k1, k) == true &*& [_]CellU32_share(k, t, l);
  ens [_]CellU32_share(k1, t, l);
{
  open CellU32_share(k, t, l);
  nonatomic_borrow_mono(k, k1, t, CellU32_nonatomic_borrow_content(l, t));
  close CellU32_share(k1, t, l);
  leak CellU32_share(k1, t, l);
}

lem CellU32_share_full(k: lifetime_t, t: thread_id_t, l: *CellU32)
  req full_borrow(k, CellU32_full_borrow_content(t, l)) &*& [?q]lifetime_token(k);
  ens [_]CellU32_share(k, t, l) &*& [q]lifetime_token(k);
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
  full_borrow_into_nonatomic_borrow(k, t, CellU32_nonatomic_borrow_content(l, t));
  close CellU32_share(k, t, l);
  leak CellU32_share(k, t, l);
}
@*/

impl CellU32 {
    fn new(u: u32) -> CellU32 {
        let c = CellU32 { v: std::cell::UnsafeCell::new(u) };
        //@ close CellU32_own(_t, u);
        c
    }

    /* VeriFast generates the contract of the safe functions based on the function's semantic type */
    fn get<'a>(&'a self) -> u32 {
        //@ open CellU32_share(a, _t, self);
        //@ open_nonatomic_borrow(a, _t, _q_a);
        //@ open CellU32_nonatomic_borrow_content(self, _t)();
        let v = unsafe { *self.v.get() };
        //@ close CellU32_nonatomic_borrow_content(self, _t)();
        //@ close_nonatomic_borrow();
        v
    }

    /* User can also write the contract of public functions to have it explicit.
    Verifast would check the compatibility of the contract with the function semantic type. */
    fn set<'a>(&'a self, u: u32)
    //@ req thread_token(?t) &*& [?q]lifetime_token(?a) &*& CellU32_share(a, t, self);
    //@ ens thread_token(t) &*& [q]lifetime_token(a);
    {
        let p = self.v.get();
        //@ open CellU32_share(a, t, self);
        //@ open_nonatomic_borrow(a, t, q);
        //@ open CellU32_nonatomic_borrow_content(self, t)();
        unsafe {
            *p = u;
        }
        //@ open CellU32_own(t, _);
        //@ close CellU32_own(t, u);
        //@ close CellU32_nonatomic_borrow_content(self, t)();
        //@ close_nonatomic_borrow();
    }
}
