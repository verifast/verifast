#include <stdlib.h>
#include "atomics.h"

typedef struct spinlock {
    int locked;
    //@ int acquireCredits;
    //@ predicate(int, int) inv_;
} *spinlock_t;

/*@

predicate_ctor spinlock_inv(spinlock_t spinlock, predicate(int, int) inv)() =
    spinlock->locked |-> ?locked &*& spinlock->acquireCredits |-> ?acquireCredits &*& inv(acquireCredits, locked);

predicate spinlock(spinlock_t spinlock; predicate(int, int) inv) =
    spinlock->inv_ |-> inv &*&
    malloc_block_spinlock(spinlock) &*&
    atomic_space(spinlock_inv(spinlock, inv));

@*/

spinlock_t create_spinlock()
//@ requires exists<pair<predicate(int, int), int> >(pair(?inv, ?acquireCredits)) &*& inv(acquireCredits, 0);
//@ ensures spinlock(result, inv);
{
  spinlock_t result = malloc(sizeof(struct spinlock));
  if (result == 0) abort();
  result->locked = 0;
  //@ result->acquireCredits = acquireCredits;
  //@ result->inv_ = inv;
  //@ close spinlock_inv(result, inv)();
  //@ create_atomic_space(spinlock_inv(result, inv));
  return result;
}

/*@

typedef lemma void spinlock_acquire_ghost_op(predicate(int, int) inv, predicate() pre, predicate() post)();
    requires inv(?acquireCredits, 0) &*& pre();
    ensures inv(acquireCredits - 1, 1) &*& post() &*& 1 <= acquireCredits;

@*/

void spinlock_acquire(spinlock_t spinlock)
//@ requires [?f]spinlock(spinlock, ?inv) &*& is_spinlock_acquire_ghost_op(?ghop, inv, ?pre, ?post) &*& pre();
//@ ensures [f]spinlock(spinlock, inv) &*& post();
{
  for (;;)
  //@ invariant [f]spinlock(spinlock, inv) &*& is_spinlock_acquire_ghost_op(ghop, inv, pre, post) &*& pre();
  {
    int result;
    //@ open spinlock(spinlock, inv);
    {
      /*@
      predicate pre_() = is_spinlock_acquire_ghost_op(ghop, inv, pre, post) &*& pre();
      predicate post_(int result_) = result_ == 0 ? post() : is_spinlock_acquire_ghost_op(ghop, inv, pre, post) &*& pre();
      @*/
      /*@
      produce_lemma_function_pointer_chunk compare_and_swap_int_ghost_op(spinlock_inv(spinlock, inv), &spinlock->locked, 0, 1, pre_, post_)() {
        assert is_compare_and_swap_int_op(?op, _, _, _, _, _);
        open spinlock_inv(spinlock, inv)();
        open pre_();
        assert spinlock->locked |-> ?locked;
        op();
        if (locked == 0) {
          ghop();
          leak is_spinlock_acquire_ghost_op(_, _, _, _);
          spinlock->acquireCredits--;
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

typedef lemma void spinlock_release_ghost_op(predicate(int, int) inv, predicate() pre, predicate() post)();
    requires inv(?acquireCredits, _) &*& pre();
    ensures inv(acquireCredits, 0) &*& post();

@*/

void spinlock_release(spinlock_t spinlock)
//@ requires [?f]spinlock(spinlock, ?inv) &*& is_spinlock_release_ghost_op(?ghop, inv, ?pre, ?post) &*& pre();
//@ ensures [f]spinlock(spinlock, inv) &*& post();
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

