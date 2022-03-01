/*@

// Lifetime logic

abstract_type lifetime; // Type of lifetimes
abstract_type thread_id; // Type of thread IDs

predicate lifetime(lifetime k;); // Lifetime token
predicate thread_token(thread_id t); // nonatomic token with Top mask ([NaInv: t.Top] in RustBelt)

predicate nonatomic_borrow(lifetime k, thread_id t, void *l, predicate() P); // nonatomic borrow with mask Nshr.l

lemma void open_nonatomic_borrow(lifetime k, thread_id t, void *l, real q); // Rule LftL-na-acc with N = Nshr.l and requiring NaInv: t.Top instead of NaInv: t.N
    requires nonatomic_borrow(k, t, l, ?P) &*& [q]lifetime(k) &*& thread_token(t);
    ensures P() &*& close_nonatomic_borrow_token(P, q, k, t);

predicate close_nonatomic_borrow_token(predicate() P, real q, lifetime k, thread_id t);

lemma void close_nonatomic_borrow();
    requires close_nonatomic_borrow_token(?P, ?q, ?k, ?t) &*& P();
    ensures [q]lifetime(k) &*& thread_token(t);

// Cell<i32> type interpretation

predicate_ctor Cell_i32_nonatomic_borrow_content(void *l, thread_id t)() =
    integer(l, _);
predicate Cell_i32_shared(lifetime k, thread_id t, void *l) = // SHR predicate for Cell<i32>
    nonatomic_borrow(k, t, l, Cell_i32_nonatomic_borrow_content(l, t));

@*/

// fn replace<'a>(self: &'a Cell<i32>, val: i32) -> i32
int replace(int *self, int val)
//@ requires [?q]lifetime(?a) &*& Cell_i32_shared(a, ?t, self) &*& thread_token(t);
//@ ensures [q]lifetime(a) &*& thread_token(t);
{
  //@ open Cell_i32_shared(a, t, self);
  //@ open_nonatomic_borrow(a, t, self, q);
  //@ open Cell_i32_nonatomic_borrow_content(self, t)();
  int result = *self;
  *self = val;
  //@ close Cell_i32_nonatomic_borrow_content(self, t)();
  //@ close_nonatomic_borrow();
  return result;
}
