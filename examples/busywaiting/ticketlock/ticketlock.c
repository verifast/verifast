#include <stdlib.h>
#include "../busywaiting.h"
#include "atomics.h"
#include "ticketlock.h"

/*@

box_class growing_list(list<void *> xs) {
  invariant true;
  action noop();
    requires true;
    ensures xs == old_xs;
  action add(void *elem);
    requires true;
    ensures xs == append(old_xs, {elem});
  handle_predicate has_at(int k, void *x) {
    invariant 0 <= k && k < length(xs) && nth(k, xs) == x;
    preserved_by noop() {}
    preserved_by add(elem) {
      nth_append(old_xs, {elem}, k);
    }
  }
}

@*/

typedef struct ticketlock {
    //@ list<int> level;
    //@ predicate(int, bool) inv_;
    unsigned long long next;
    unsigned long long owner;
    //@ bool held;
    //@ box signalsBox;
} *ticketlock;

/*@

lemma_auto void ticketlock_nb_level_dims_nonneg()
    requires true;
    ensures 0 <= ticketlock_nb_level_dims();
{}

predicate signals(list<void *> signals, list<int> baseLevel, int start) =
    start == length(signals) ?
        true
    :
        signal(nth(start, signals), append(baseLevel, {start}), false) &*& signals(signals, baseLevel, start + 1);

predicate_ctor ticketlock_inv(ticketlock lock, list<int> level, predicate(int, bool) inv, box signalsBox)() =
    growing_list(signalsBox, ?signals) &*&
    lock->next |-> ?next &*& length(signals) == next &*&
    [1/2]lock->owner |-> ?owner &*& 0 <= owner &*&
    [1/2]lock->held |-> ?held &*&
    signals(signals, level, held ? owner + 1 : owner) &*&
    inv(owner, held) &*&
    held ?
        owner < next
    :
        [1/2]lock->owner |-> owner &*& [1/2]lock->held |-> held;

predicate ticketlock(ticketlock lock; list<int> level, predicate(int, bool) inv) =
    lock->level |-> level &*& lock->inv_ |-> inv &*& lock->signalsBox |-> ?signalsBox &*& malloc_block_ticketlock(lock) &*&
    atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox));

@*/


ticketlock create_ticketlock()
/*@
requires
    exists<pair<list<int>, predicate(int, bool)> >(pair(?level, ?inv)) &*& inv(0, false) &*&
    level == cons(?level_max_length, ?level0) &*& length(level0) + ticketlock_nb_level_dims <= level_max_length;
@*/
//@ ensures ticketlock(result, level, inv);
//@ terminates;
{
    //@ open exists(_);
    ticketlock result = malloc(sizeof(struct ticketlock));
    if (result == 0) abort();
    result->next = 0;
    result->owner = 0;
    //@ result->level = level;
    //@ result->inv_ = inv;
    //@ create_box signalsBox = growing_list({});
    //@ result->signalsBox = signalsBox;
    //@ result->held = false;
    //@ close signals({}, level, 0);
    //@ close ticketlock_inv(result, level, inv, signalsBox)();
    //@ create_atomic_space(create_ticketlock, ticketlock_inv(result, level, inv, signalsBox));
    return result;
}

void ticketlock_acquire_helper(ticketlock lock, unsigned long long ticket)
{
    for (;;)
    {
        unsigned long long owner;
        owner = atomic_load_counter(&lock->owner);
        if (owner == ticket)
            break;
    }
}

void ticketlock_acquire(ticketlock lock)
/*@
requires
    [?f]ticketlock(lock, ?level, ?inv) &*&
    obs(?p, ?obs) &*& 
    forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, level)) == true &*&
    is_ticketlock_wait_ghost_op(?wop, p, level, inv, ?wait_inv, currentThread) &*&
    is_ticketlock_acquire_ghost_op(?aop, p, level, inv, wait_inv, ?post, currentThread) &*&
    wait_inv(-1, _);
@*/
//@ ensures [f]ticketlock(lock, level, inv) &*& post();
//@ terminates;
{
    //@ box signalsBox = lock->signalsBox;
    unsigned long long ticket;
    {
        /*@
        predicate pre_() = [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox));
        predicate post_(int result) = [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox));
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_fetch_and_increment_counter_ghost_op(&lock->next, pre_, post_, currentThread)() {
            open pre_();
            open_atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox));
            open ticketlock_inv(lock, level, inv, signalsBox)();
            assert is_atomic_fetch_and_increment_counter_op(?op, &lock->next, ?P, ?Q);
            assert lock->next |-> ?next;
            open ticketlock_next(lock, _);
            op();
            close post_(next);
        };
        @*/
        //@ close pre();
        ticket = atomic_fetch_and_increment_counter(&lock->next);
        //@ open post(_);
    }
    ticketlock_acquire_helper(lock, ticket);
}

void ticketlock_release(ticketlock lock)
//@ requires [?f]ticketlock(lock, ?level, ?inv) &*& is_ticketlock_release_ghost_op(?ghop, inv, ?pre, ?post, currentThread) &*& pre();
//@ ensures [f]ticketlock(lock, level, inv) &*& post();
//@ terminates;
{
    unsigned long long owner = load_counter(&lock->owner);
    atomic_store_counter(&lock->owner, owner + 1);
}
