#include "threading.h"

int x;

//@ predicate inv() = x |-> ?v &*& v == 2 || v == -2;

//@ predicate pre() = [_]atomic_space(inv);

void negate_x()
//@ requires pre();
//@ ensures true;
{
  int v;
  {
      //@ predicate post(int result) = result == 2 || result == -2;
      /*@
      produce_lemma_function_pointer_chunk atomic_fetch_and_negate_safety_proof(&x, pre, post)() {
          open pre();
          open_atomic_space(inv);
          open inv();
          int result = do_atomic_fetch_and_negate(&x);
          close inv();
          close_atomic_space(inv);
          close post(result);
      };
      @*/
      v = atomic_fetch_and_negate(&x);
      //@ open post(v);
  }
  assert(v == 2 || v == -2);
}

int main()
//@ requires module(finegrained, true);
//@ ensures false;
{
  //@ open_module();
  x = 2;
  //@ close inv();
  //@ create_atomic_space(inv);
  for (;;)
  //@ invariant [_]atomic_space(inv);
  {
    //@ produce_function_pointer_chunk forkee(negate_x)(pre)() { call(); }
    //@ close pre();
    fork(negate_x);
  }
}
