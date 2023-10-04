// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#include "atomics.h"
#include "ticketlock.h"

struct globals {
  unsigned long long flag;
  ticketlock lock;
  //@ bool lockHeld;
  //@ bool spaceRemoved;
};
struct globals g;

/*@

predicate ticketlock_inv(int owner, bool held) =
  [1/2]g.lockHeld |-> held;

predicate_ctor atomic_space_inv(void *signal)() =
  [1/2]counter(&g.flag, ?flag) &*&
  [1/2]g.spaceRemoved |-> ?spaceRemoved &*&
  signal(signal, level(main, {1}), flag != 0) &*&
  flag == 0 ?
      !spaceRemoved
  :
      flag == 1 &*&
      g.lock |-> ?lock &*& ticketlock_held(lock, ticketlock_inv, 1, _) &*&
      [1/2]counter(&g.flag, flag) &*&
      [1/2]g.lockHeld |-> true &*&
      spaceRemoved ?
          true
      :
          [1/2]atomic_space(main, atomic_space_inv(signal));

@*/

/*@

predicate_ctor acquirer_pre(void *signal)() =
  [1/2]atomic_space(main, atomic_space_inv(signal)) &*&
  [1/2]counter(&g.flag, 0) &*&
  g.lock |-> ?lock &*& [1/2]g.lockHeld |-> false &*&
  pointer_within_limits(&g.flag) == true &*&
  ticketlock(lock, ticketlock_inv);

@*/

void acquirer()
/*@
requires
  obs({Forkee}, cons(pair(?signal, level(main, {1})), {})) &*& [1/2]atomic_space(main, atomic_space_inv(signal)) &*&
  [1/2]counter(&g.flag, 0) &*&
  g.lock |-> ?lock &*& [1/2]g.lockHeld |-> false &*&
  pointer_within_limits(&g.flag) == true &*&
  ticketlock(lock, ticketlock_inv);
@*/
//@ ensures obs(_, {});
//@ terminates;
{
  {
    /*@
    predicate wait_inv(int owner, list<int> M, list<pathcomp> p1, list<pair<void *, level> > obs) =
      [1/2]g.lockHeld |-> false &*& owner == -1 &*&
      obs == {pair(signal, level(main, {1}))};
    predicate post(int ticket) = obs(?p, {pair(signal, level(main, {1}))}) &*& [1/2]g.lockHeld |-> true;
    @*/
    /*@
    produce_lemma_function_pointer_chunk ticketlock_wait_ghost_op(ticketlock_inv, wait_inv, currentThread)(f) {
      open ticketlock_inv(_, _);
      open wait_inv(_, _, _, _);
      assert false;
    };
    @*/
    /*@
    produce_lemma_function_pointer_chunk ticketlock_acquire_ghost_op(ticketlock_inv, wait_inv, post, currentThread)() {
      open ticketlock_inv(?owner, _);
      open wait_inv(_, _, _, _);
      g.lockHeld = true;
      close ticketlock_inv(owner, true);
      close post(owner);
    };
    @*/
    //@ close wait_inv(-1, {}, {Forkee}, _);
    ticketlock_acquire(g.lock);
    //@ open post(_);
  }
  {
    /*@
    predicate pre() =
      obs(_, cons(pair(signal, level(main, {1})), {})) &*& [1/2]atomic_space(main, atomic_space_inv(signal)) &*&
      g.lock |-> lock &*& [1/2]g.lockHeld |-> true &*& [1/2]counter(&g.flag, 0) &*&
      ticketlock_held(lock, ticketlock_inv, 1, _);
    predicate post() = obs(_, {});
    @*/
    /*@
    produce_lemma_function_pointer_chunk atomic_store_counter_ghost_op(&g.flag, 1, pre, post, currentThread)() {
      open pre();
      open_atomic_space(main, atomic_space_inv(signal));
      open atomic_space_inv(signal)();
      assert is_atomic_store_counter_op(?op, &g.flag, 1, ?P, ?Q);
      op();
      set_signal(signal);
      close atomic_space_inv(signal)();
      close_atomic_space(main, atomic_space_inv(signal));
      close post();
    };
    @*/
    //@ close pre();
    atomic_store_counter(&g.flag, 1);
    //@ open post();
  }
}

void releaser()
/*@
requires
    exists<void *>(?signal) &*& obs({Forker}, {}) &*& [1/2]atomic_space(main, atomic_space_inv(signal)) &*& [1/2]g.spaceRemoved |-> false &*&
    pointer_within_limits(&g.flag) == true &*& call_below_perm_(currentThread, main);
@*/
//@ ensures obs(_, {}) &*& module(simple_cross_thread_client, false);
//@ terminates;
{
  //@ open exists(_);
  //@ pathize_call_below_perm_();
  //@ create_wait_perm(signal, level(main, {1}), releaser);
  for (;;)
  /*@
  invariant
      obs({Forker}, {}) &*& [1/2]atomic_space(main, atomic_space_inv(signal)) &*& [1/2]g.spaceRemoved |-> false &*& wait_perm({Forker}, signal, level(main, {1}), releaser);
  @*/
  {
    unsigned long long value;
    {
      /*@
      predicate pre() =
        obs({Forker}, {}) &*& [1/2]atomic_space(main, atomic_space_inv(signal)) &*& [1/2]g.spaceRemoved |-> false &*& wait_perm({Forker}, signal, level(main, {1}), releaser);
      predicate post(int result) =
        obs({Forker}, {}) &*& wait_perm({Forker}, signal, level(main, {1}), releaser) &*&
        result == 1 ?
          atomic_space(main, atomic_space_inv(signal)) &*& [1/2]g.spaceRemoved |-> true
        :
          [1/2]atomic_space(main, atomic_space_inv(signal)) &*& [1/2]g.spaceRemoved |-> false &*& call_perm_(currentThread, releaser);
      @*/
      /*@
      produce_lemma_function_pointer_chunk atomic_load_counter_ghost_op(&g.flag, pre, post, currentThread)() {
        open pre();
        open_atomic_space(main, atomic_space_inv(signal));
        open atomic_space_inv(signal)();
        assert is_atomic_load_counter_op(?op, &g.flag, ?P, ?Q);
        assert [1/2]counter(&g.flag, ?flag);
        op();
        if (flag == 1)
          g.spaceRemoved = true;
        else
          wait(signal);
        close atomic_space_inv(signal)();
        close_atomic_space(main, atomic_space_inv(signal));
        close post(flag);
      };
      @*/
      //@ close pre();
      value = atomic_load_counter(&g.flag);
      //@ open post(value);
    }
    if (value == 1)
      break;
  }
  //@ destroy_atomic_space();
  //@ open atomic_space_inv(signal)();
  //@ ticketlock lock = g.lock;
  //@ assert ticketlock_held(lock, _, _, ?ticket);
  {
    /*@
    predicate pre() = [1/2]g.lockHeld |-> true;
    predicate post(list<pathcomp> p1, list<pair<void *, level> > obs1) = [1/2]g.lockHeld |-> false &*& is_ancestor_of({Forker}, p1) == true &*& obs1 == {};
    @*/
    /*@
    produce_lemma_function_pointer_chunk ticketlock_release_ghost_op(ticketlock_inv, ticket, {Forker}, {}, pre, post, currentThread)() {
      open pre();
      open ticketlock_inv(?owner, true);
      g.lockHeld = false;
      close ticketlock_inv(owner + 1, false);
      assert obs_(_, ?p1, _);
      close post(p1, _);
    };
    @*/
    //@ close pre();
    ticketlock_release(g.lock);
    //@ open post(?p2, _);
  }
  ticketlock_dispose(g.lock);
  //@ open ticketlock_inv()(_, _);
  //@ destroy_counter(&g.flag);
  //@ close_module();
  //@ leak signal(_, _, _);
  //@ leak wait_perm(_, _, _, _);
}


int main() //@ : custom_main_spec
//@ requires obs({}, {}) &*& module(simple_cross_thread_client, true);
//@ ensures obs(_, {}) &*& module(simple_cross_thread_client, false);
//@ terminates;
{
  //@ open_module();
  //@ void *signal = create_signal();
  //@ init_signal(signal, level(main, {1}));
  //@ create_counter(&g.flag);
  //@ g.spaceRemoved = false;
  //@ close atomic_space_inv(signal)();
  //@ create_atomic_space(main, atomic_space_inv(signal));
  
  //@ g.lockHeld = false;
  //@ close ticketlock_inv(0, false);
  //@ close exists(ticketlock_inv);
  ticketlock lock = create_ticketlock();
  g.lock = lock;
  /*@
  produce_function_pointer_chunk thread_run(acquirer)({}, {pair(signal, level(main, {1}))}, acquirer_pre(signal))() {
    open acquirer_pre(signal)();
    call();
  }
  @*/
  //@ close acquirer_pre(signal)();
  fork(acquirer);
  
  //@ close exists(signal);
  //@ produce_call_below_perm_();
  releaser();
  
  return 0;
}
