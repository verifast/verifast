/*@

// Lifetime logic

abstract_type lft; // Type of lifetimes
abstract_type tid; // Type of thread IDs

predicate lft(lft k;); // Lifetime token
predicate NaInv_top(tid t); // nonatomic token with Top mask

predicate na_bor_Nshr_l(lft k, tid t, void *l, predicate() P); // nonatomic borrow with mask Nshr.l

lemma void lftl_na_acc_Nshr_l(lft k, tid t, void *l, real q); // Rule LftL-na-acc with N = Nshr.l and requiring NaInv: t.Top instead of NaInv: t.N
    requires na_bor_Nshr_l(k, t, l, ?P) &*& [q]lft(k) &*& NaInv_top(t);
    ensures P() &*& lft_na_acc_Nshr_l_close_token(P, q, k, t);

predicate lft_na_acc_Nshr_l_close_token(predicate() P, real q, lft k, tid t);

lemma void lftl_na_acc_Nshr_l_close();
    requires lft_na_acc_Nshr_l_close_token(?P, ?q, ?k, ?t) &*& P();
    ensures [q]lft(k) &*& NaInv_top(t);

// Cell<i32> type interpretation

predicate_ctor Cell_i32_shr_na(void *l, tid t)() =
    integer(l, _);
predicate Cell_i32_shr(lft k, tid t, void *l) = // SHR predicate for Cell<i32>
    na_bor_Nshr_l(k, t, l, Cell_i32_shr_na(l, t));

@*/

// fn replace<'a>(self: &'a Cell<i32>, val: i32) -> i32
int replace(int *self, int val)
//@ requires [?q]lft(?a) &*& Cell_i32_shr(a, ?t, self) &*& NaInv_top(t);
//@ ensures [q]lft(a) &*& NaInv_top(t);
{
  //@ open Cell_i32_shr(a, t, self);
  //@ lftl_na_acc_Nshr_l(a, t, self, q);
  //@ open Cell_i32_shr_na(self, t)();
  int result = *self;
  *self = val;
  //@ close Cell_i32_shr_na(self, t)();
  //@ lftl_na_acc_Nshr_l_close();
  return result;
}
