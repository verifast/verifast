#include <stdlib.h>
#include "atomics.h"
#include "../busywaiting.h"

typedef struct spinlock {
    int locked;
    //@ predicate(int) inv_;
} *spinlock_t;

/*@

predicate_ctor spinlock_inv(spinlock_t spinlock, predicate(int) inv)() =
    spinlock->locked |-> ?locked &*& inv(locked);

predicate spinlock(spinlock_t spinlock; predicate(int) inv) =
    spinlock->inv_ |-> inv &*&
    malloc_block_spinlock(spinlock) &*&
    atomic_space(spinlock_inv(spinlock, inv));

@*/

spinlock_t create_spinlock()
//@ requires exists<predicate(int)>(?inv) &*& inv(0);
//@ ensures spinlock(result, inv);
//@ terminates;
{
  spinlock_t result = malloc(sizeof(struct spinlock));
  if (result == 0) abort();
  result->locked = 0;
  //@ result->inv_ = inv;
  //@ close spinlock_inv(result, inv)();
  //@ create_atomic_space(spinlock_inv(result, inv));
  return result;
}

/*@

typedef lemma void spinlock_acquire_ghost_op(predicate(int) inv, predicate() pre, predicate() post, int callerThread)();
    requires inv(?locked) &*& pre() &*& currentThread == callerThread;
    ensures
        locked == 0 ?
            inv(1) &*& post()
        :
            inv(locked) &*& pre() &*& call_perm_(currentThread, spinlock_acquire);

@*/

void spinlock_acquire(spinlock_t spinlock)
//@ requires [?f]spinlock(spinlock, ?inv) &*& is_spinlock_acquire_ghost_op(?ghop, inv, ?pre, ?post, currentThread) &*& pre();
//@ ensures [f]spinlock(spinlock, inv) &*& post();
//@ terminates;
{
  for (;;)
  //@ invariant [f]spinlock(spinlock, inv) &*& is_spinlock_acquire_ghost_op(ghop, inv, pre, post, currentThread) &*& pre();
  {
    int result;
    //@ open spinlock(spinlock, inv);
    {
      /*@
      predicate pre_() = is_spinlock_acquire_ghost_op(ghop, inv, pre, post, currentThread) &*& pre();
      predicate post_(int result_) = result_ == 0 ? post() : is_spinlock_acquire_ghost_op(ghop, inv, pre, post, currentThread) &*& pre() &*& call_perm_(currentThread, spinlock_acquire);
      @*/
      /*@
      produce_lemma_function_pointer_chunk compare_and_swap_int_ghost_op(spinlock_inv(spinlock, inv), &spinlock->locked, 0, 1, pre_, post_, currentThread)() {
        assert is_compare_and_swap_int_op(?op, _, _, _, _, _);
        open spinlock_inv(spinlock, inv)();
        open pre_();
        assert spinlock->locked |-> ?locked;
        op();
        ghop();
        if (locked == 0) {
          leak is_spinlock_acquire_ghost_op(_, _, _, _, currentThread);
        } else {
        }
        close spinlock_inv(spinlock, inv)();
        close post_(locked);
      };
      @*/
      //@ close pre_();
      result = compare_and_swap_int(&spinlock->locked, 0, 1);
      //@ open post_(result);
    }
    if (result == 0) {
      break;
    }
  }
}

/*@

typedef lemma void spinlock_release_ghost_op(predicate(int) inv, predicate() pre, predicate() post)();
    requires inv(_) &*& pre();
    ensures inv(0) &*& post();

@*/

void spinlock_release(spinlock_t spinlock)
//@ requires [?f]spinlock(spinlock, ?inv) &*& is_spinlock_release_ghost_op(?ghop, inv, ?pre, ?post) &*& pre();
//@ ensures [f]spinlock(spinlock, inv) &*& post();
//@ terminates;
{
  //@ open spinlock(spinlock, inv);
  {
    /*@
    predicate pre_() = is_spinlock_release_ghost_op(ghop, inv, pre, post) &*& pre();
    predicate post_() = post();
    @*/
    /*@
    produce_lemma_function_pointer_chunk atomic_store_int_ghost_op(spinlock_inv(spinlock, inv), &spinlock->locked, 0, pre_, post_, currentThread)() {
      assert is_atomic_store_int_op(?op, _, _, _, _);
      open spinlock_inv(spinlock, inv)();
      open pre_();
      op();
      ghop();
      leak is_spinlock_release_ghost_op(_, _, _, _);
      close spinlock_inv(spinlock, inv)();
      close post_();
    };
    @*/
    //@ close pre_();
    atomic_store_int(&spinlock->locked, 0);
    //@ leak is_atomic_store_int_ghost_op(_, _, _, _, _, _, _);
    //@ open post_();
  }
  //@ close [f]spinlock(spinlock, inv);
}

