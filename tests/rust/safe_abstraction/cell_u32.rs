#![allow(dead_code)]
pub struct CellU32 {
    v: u32,
}
/*@
// Interpretation
// `OWN` for Cell<u32>
//[[cell(tau)]].OWN(t, vs) = [[tau]].OWN(t, vs)
predicate CellU32_own(thread_id_t t, uint32_t v) = true; // The field chunk will carry the information

/* A note on `|= cell(tau) copy` judgement:
In RustBelt `|= tau copy => |= cell(tau) copy` but it is not the case in Rust as it is prohibited
exceptionally for preventing potential pitfalls.
The real `Cell<T>` in std library will have the `get` method if `tau copy` syn-typing judgement
is derivable. Here, u32 is obviously copy and we are providing the `get` method.
However, we do not need `|= u32 copy` explicitly because VeriFast allows copying integer values,
i.e. in VeriFast the `[[u32]].OWN` is implicitly persistent.
*/

predicate_ctor CellU32_nonatomic_borrow_content(void *l, thread_id_t t)() =
  CellU32_v(l, ?v) &*& CellU32_own(t, v);

// `SHR` for Cell<u32>
predicate CellU32_share(lifetime_t k, thread_id_t t, void *l) =
  [_]nonatomic_borrow(k, t, CellU32_nonatomic_borrow_content(l, t));

// Proof obligations
lemma void CellU32_share_mono(lifetime_t k, lifetime_t k1, thread_id_t t, void *l)
  requires lifetime_inclusion(k1, k) == true &*& [_]CellU32_share(k, t, l);
  ensures [_]CellU32_share(k1, t, l);
{
  open CellU32_share(k, t, l);
  nonatomic_borrow_mono(k, k1, t, CellU32_nonatomic_borrow_content(l, t));
  close CellU32_share(k1, t, l);
  leak CellU32_share(k1, t, l);
}

lemma void CellU32_share_full(lifetime_t k, thread_id_t t, void *l)
  requires full_borrow(k, CellU32_full_borrow_content(l, t)) &*& [?q]lifetime_token(k);
  ensures [_]CellU32_share(k, t, l) &*& [q]lifetime_token(k);
{
  produce_lemma_function_pointer_chunk implies(CellU32_full_borrow_content(l, t), CellU32_nonatomic_borrow_content(l, t))() {
    open CellU32_full_borrow_content(l, t)();
    close CellU32_nonatomic_borrow_content(l, t)();
  } {
    produce_lemma_function_pointer_chunk implies(CellU32_nonatomic_borrow_content(l, t), CellU32_full_borrow_content(l, t))() {
      open CellU32_nonatomic_borrow_content(l, t)();
      close CellU32_full_borrow_content(l, t)();
    } {
      full_borrow_implies(k, CellU32_full_borrow_content(l, t), CellU32_nonatomic_borrow_content(l, t));
    }
  }
  full_borrow_into_nonatomic_borrow(k, t, CellU32_nonatomic_borrow_content(l, t));
  close CellU32_share(k, t, l);
  leak CellU32_share(k, t, l);
}
@*/

fn new(u: u32) -> CellU32 {
    CellU32 { v: u }
    //@ close CellU32_own(_t, u);
}

/* VeriFast generates the contract of the safe functions based on the function's semantic type */
fn get<'a>(c: &'a CellU32) -> u32 {
    //@ open CellU32_share(a, _t, c);
    //@ open_nonatomic_borrow(a, _t, _q_a);
    //@ open CellU32_nonatomic_borrow_content(c, _t)();
    c.v
    //@ close CellU32_nonatomic_borrow_content(c, _t)();
    //@ close_nonatomic_borrow();
}

/* User can also write the contract of public functions to have it explicit.
Verifast would check the compatibility of the contract with the function semantic type. */
fn set<'a>(c: &'a CellU32, u: u32)
//@ requires [?q]lifetime_token(?a) &*& thread_token(?t) &*& CellU32_share(a, t, c);
//@ ensures [q]lifetime_token(a) &*& thread_token(t);
{
    let p = &c.v as *const u32 as *mut u32;
    //@ open CellU32_share(a, t, c);
    //@ open_nonatomic_borrow(a, t, q);
    //@ open CellU32_nonatomic_borrow_content(c, t)();
    unsafe {
        *p = u;
    }
    //@ open CellU32_own(t, _);
    //@ close CellU32_own(t, u);
    //@ close CellU32_nonatomic_borrow_content(c, t)();
    //@ close_nonatomic_borrow();
}