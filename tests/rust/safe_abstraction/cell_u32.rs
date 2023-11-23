#![allow(dead_code)]
pub struct CellU32 {
    v: u32,
}
/*@
// Interpretation
// `OWN` for Cell<u32>
// [[cell(tau)]].OWN(t, vs) = [[tau]].OWN(t, vs)
pred CellU32_own(t: thread_id_t, v: uint32_t) = true; // The `v` parameter type carries the info

/* A note on `|= cell(tau) copy` judgement:
In RustBelt `|= tau copy => |= cell(tau) copy` but it is not the case in Rust as it is prohibited
exceptionally for preventing potential pitfalls.
The real `Cell<T>` in std library will have the `get` method if `tau copy` syn-typing judgement
is derivable. Here, u32 is obviously copy and we are providing the `get` method.
However, we do not need `|= u32 copy` explicitly because VeriFast allows copying integer values,
i.e. in VeriFast the `[[u32]].OWN` is implicitly persistent.
*/

pred_ctor CellU32_nonatomic_borrow_content(l: *CellU32, t: thread_id_t)() =
  CellU32_v(l, ?v) &*& CellU32_own(t, v);

// `SHR` for Cell<u32>
pred CellU32_share(k: lifetime_t, t: thread_id_t, l: *CellU32) =
  [_]nonatomic_borrow(k, Tlns(t, Nshr, [l]), CellU32_nonatomic_borrow_content(l, t));

// Proof obligations
lem CellU32_share_mono(k: lifetime_t, k1: lifetime_t, t: thread_id_t, l: *CellU32)
  req lifetime_inclusion(k1, k) == true &*& [_]CellU32_share(k, t, l);
  ens [_]CellU32_share(k1, t, l);
{
  open CellU32_share(k, t, l);
  nonatomic_borrow_mono(k, k1, Tlns(t, Nshr, [l]), CellU32_nonatomic_borrow_content(l, t));
  close CellU32_share(k1, t, l);
  leak CellU32_share(k1, t, l);
}

lem CellU32_share_full(k: lifetime_t, t: thread_id_t, l: *CellU32)
  req full_borrow(k, CellU32_full_borrow_content(l, t)) &*& [?q]lifetime_token(k);
  ens [_]CellU32_share(k, t, l) &*& [q]lifetime_token(k);
{
  produce_lem_ptr_chunk implies(CellU32_full_borrow_content(l, t), CellU32_nonatomic_borrow_content(l, t))() {
    open CellU32_full_borrow_content(l, t)();
    close CellU32_nonatomic_borrow_content(l, t)();
  } {
    produce_lem_ptr_chunk implies(CellU32_nonatomic_borrow_content(l, t), CellU32_full_borrow_content(l, t))() {
      open CellU32_nonatomic_borrow_content(l, t)();
      close CellU32_full_borrow_content(l, t)();
    } {
      full_borrow_implies(k, CellU32_full_borrow_content(l, t), CellU32_nonatomic_borrow_content(l, t));
    }
  }
  full_borrow_into_nonatomic_borrow(k, Tlns(t, Nshr, [l]), CellU32_nonatomic_borrow_content(l, t));
  close CellU32_share(k, t, l);
  leak CellU32_share(k, t, l);
}
@*/

fn new(u: u32) -> CellU32 {
    let c = CellU32 { v: u };
    //@ close CellU32_own(_t, u);
    c
}

/* VeriFast generates the contract of the safe functions based on the function's semantic type */
fn get<'a>(c: &'a CellU32) -> u32 {
    //@ open CellU32_share(a, _t, c);
    //@ nonatomic_inv_complement_token_split(_t, Nshr, [c]);
    //@ open_nonatomic_borrow(a, Tlns(_t, Nshr, [c]), _q_a);
    //@ open CellU32_nonatomic_borrow_content(c, _t)();
    let v = c.v;
    //@ close CellU32_nonatomic_borrow_content(c, _t)();
    //@ close_nonatomic_borrow();
    //@ nonatomic_inv_complement_token_merge(_t, Nshr, [c]);
    v
}

/* User can also write the contract of public functions to have it explicit.
Verifast would check the compatibility of the contract with the function semantic type. */
fn set<'a>(c: &'a CellU32, u: u32)
//@ req nonatomic_inv_complement_token(?t, Nshr, []) &*& [?q]lifetime_token(?a) &*& CellU32_share(a, t, c);
//@ ens nonatomic_inv_complement_token(t, Nshr, []) &*& [q]lifetime_token(a);
{
    let p = &c.v as *const u32 as *mut u32;
    //@ open CellU32_share(a, t, c);
    //@ nonatomic_inv_complement_token_split(t, Nshr, [c]);
    //@ open_nonatomic_borrow(a, Tlns(t, Nshr, [c]), q);
    //@ open CellU32_nonatomic_borrow_content(c, t)();
    unsafe {
        *p = u;
    }
    //@ open CellU32_own(t, _);
    //@ close CellU32_own(t, u);
    //@ close CellU32_nonatomic_borrow_content(c, t)();
    //@ close_nonatomic_borrow();
    //@ nonatomic_inv_complement_token_merge(t, Nshr, [c]);
}

// fn swap<'a, 'b>(c1: &'a CellU32, c2: &'b CellU32) {
//     let p1 = &c1.v as *const u32 as *mut u32;
//     let p2 = &c2.v as *const u32 as *mut u32;
//     unsafe {
//         let temp = *p1;
//         *p1 = *p2;
//         *p2 = temp;
//     }
// }
