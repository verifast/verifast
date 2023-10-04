// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

//@ #include <quantifiers.gh>
#include <stdlib.h>
#include <busywaiting.h>
#include "ticketlock_classic.h"

bool x;
ticketlock_classic lock;

/*@

predicate inv() = x |-> ?v;

@*/

void invert()
//@ requires obs(?p, ?obs) &*& [1/2]lock |-> ?l &*& [1/2]ticketlock_classic(l, level(main, {1, 0}), inv) &*& forall(map(snd, obs), (level_lt)(level(main, {1, 0}))) == true;
//@ ensures obs(_, obs) &*& [1/2]lock |-> l &*& [1/2]ticketlock_classic(l, level(main, {1, 0}), inv);
//@ terminates;
{
  ticketlock_classic_acquire(lock);
  //@ open inv();
  x = !x;
  //@ close inv();
  /*@
  if (!forall(map(snd, obs), (func_lt_level)(ticketlock_classic_acquire))) {
      level badLevel = not_forall(map(snd, obs), (func_lt_level)(ticketlock_classic_acquire));
      forall_elim(map(snd, obs), (level_lt)(level(main, {1, 0})), badLevel);
      assert false;
  }
  @*/
  ticketlock_classic_release(lock);
}

int main() //@ : custom_main_spec
//@ requires obs({}, {}) &*& module(simple_classic_client, true);
//@ ensures obs(_, {}) &*& module(simple_classic_client, false);
//@ terminates;
{
  //@ open_module();
  x = false;
  //@ close inv();
  //@ produce_func_lt(ticketlock_classic_acquire);
  //@ close exists(pair(level(main, {1, 0}), inv));
  lock = create_ticketlock_classic();

  {
    //@ predicate thread_data(;) = [1/2]lock |-> ?l &*& [1/2]ticketlock_classic(l, level(main, {1, 0}), inv);
    /*@
    produce_function_pointer_chunk thread_run_joinable(invert)({}, {}, thread_data, thread_data, level(main, {1, 1}))() {
      open thread_data();
      call();
      close thread_data();
    }
    @*/
    //@ close thread_data();
    thread t = fork_joinable(invert);

    invert();
  
    join(t);
    //@ open thread_data();
  }
  
  ticketlock_classic_dispose(lock);
  //@ open inv();
  //@ close_module();
  
  return 0;
}
