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

lemma void signals_append(void *signal)
    requires signals(?signals, ?level, ?start) &*& signal(signal, append(level, {length(signals)}), false) &*& 0 <= start &*& start <= length(signals);
    ensures signals(append(signals, {signal}), level, start);
{
    open signals(signals, level, start);
    if (start == length(signals)) {
        close signals(append(signals, {signal}), level, start + 1);
        nth_append_r(signals, {signal}, 0);
    } else {
        signals_append(signal);
        nth_append(signals, {signal}, start);
    }
    close signals(append(signals, {signal}), level, start);
}

predicate_ctor ticketlock_inv(ticketlock lock, list<int> level, predicate(int, bool) inv, box signalsBox)() =
    growing_list(signalsBox, ?signals) &*&
    lock->next |-> ?next &*& length(signals) == next &*&
    [1/2]lock->owner |-> ?owner &*& 0 <= owner &*& owner <= next &*&
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
/*@
requires
    [?f]lock->level |-> ?level &*& [f]lock->inv_ |-> ?inv &*& [f]lock->signalsBox |-> ?signalsBox &*& [f]malloc_block_ticketlock(lock) &*&
    [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox)) &*&
    has_at(?hasAtHandle, signalsBox, ticket, ?signal) &*&
    is_ticketlock_wait_ghost_op(?wop, ?p, level, inv, ?wait_inv, currentThread) &*&
    is_ticketlock_acquire_ghost_op(?aop, p, level, inv, wait_inv, ?post, currentThread) &*&
    wait_inv(-1, _) &*&
    pointer_within_limits(&lock->owner) == true &*&
    obs(p, cons(pair(signal, append(level, {ticket})), ?obs)) &*& call_below_perm_(currentThread, ticketlock_acquire);
@*/
//@ ensures [f]ticketlock(lock, level, inv) &*& post();
{
    //@ close exists(false);
    for (;;)
    /*@
    invariant
        [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox)) &*&
        has_at(hasAtHandle, signalsBox, ticket, signal) &*&
        is_ticketlock_wait_ghost_op(wop, p, level, inv, wait_inv, currentThread) &*&
        is_ticketlock_acquire_ghost_op(aop, p, level, inv, wait_inv, post, currentThread) &*&
        obs(p, cons(pair(signal, append(level, {ticket})), obs)) &*&
        exists<bool>(?startedWaiting) &*&
        wait_inv(?owner0, ?f0) &*& (owner0 == -1 || f0 == ticketlock_acquire_helper) &*&            
        startedWaiting ?
            1 <= ticket &*& has_at(_, signalsBox, ticket - 1, ?predecessorSignal) &*& wait_perm(p, predecessorSignal, append(level, {ticket - 1}), ticketlock_acquire_helper)
        :
            call_below_perm_(currentThread, ticketlock_acquire);
    @*/
    {
        unsigned long long owner;
        {
            /*@
            predicate pre_() =
                [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox)) &*&
                has_at(hasAtHandle, signalsBox, ticket, signal) &*&
		is_ticketlock_wait_ghost_op(wop, p, level, inv, wait_inv, currentThread) &*&
		is_ticketlock_acquire_ghost_op(aop, p, level, inv, wait_inv, post, currentThread) &*&
		obs(p, cons(pair(signal, append(level, {ticket})), obs)) &*&
		exists<bool>(startedWaiting) &*&
		wait_inv(owner0, f0) &*& (owner0 == -1 || f0 == ticketlock_acquire_helper) &*&            
		startedWaiting ?
		    1 <= ticket &*& has_at(_, signalsBox, ticket - 1, ?predecessorSignal) &*& wait_perm(p, predecessorSignal, append(level, {ticket - 1}), ticketlock_acquire_helper)
		:
		    call_below_perm_(currentThread, ticketlock_acquire);
            predicate post_(int result) =
                [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox)) &*&
                result == ticket ?
                    post()
                :
                    call_perm_(currentThread, ticketlock_acquire_helper) &*&
                    has_at(hasAtHandle, signalsBox, ticket, signal) &*&
		    is_ticketlock_wait_ghost_op(wop, p, level, inv, wait_inv, currentThread) &*&
		    is_ticketlock_acquire_ghost_op(aop, p, level, inv, wait_inv, post, currentThread) &*&
		    obs(p, cons(pair(signal, append(level, {ticket})), obs)) &*&
		    exists<bool>(?startedWaiting1) &*&
		    wait_inv(?owner1, ?f1) &*& (owner1 == -1 || f1 == ticketlock_acquire_helper) &*&            
		    startedWaiting1 ?
		        1 <= ticket &*& has_at(_, signalsBox, ticket - 1, ?predecessorSignal) &*& wait_perm(p, predecessorSignal, append(level, {ticket - 1}), ticketlock_acquire_helper)
		    :
		        call_below_perm_(currentThread, ticketlock_acquire);
            @*/
            /*@
            produce_lemma_function_pointer_chunk atomic_load_counter_ghost_op(&lock->owner, pre_, post_, currentThread)() {
                open pre_();
                open_atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox));
                open ticketlock_inv(lock, level, inv, signalsBox)();
                assert is_atomic_load_counter_op(?op, &lock->owner, ?P, ?Q);
                assert [1/2]lock->owner |-> ?owner_;
                op();
                if (owner_ == ticket) {
                    lock->held = true;
                    open signals(?signals, level, owner_, 
                    set_signal(
                close ticketlock_inv(lock, level, inv, signalsBox)();
                close_atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox));
                close post_(owner_);
            };
            @*/
            //@ close pre_();
            owner = atomic_load_counter(&lock->owner);
            //@ open post_(_);
        }
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
        predicate pre_() =
            obs(p, obs) &*&
            [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox));
        predicate post_(int result) =
            has_at(_, signalsBox, result, ?signal) &*&
            obs(p, cons(pair(signal, append(level, {result})), obs)) &*&
            [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox));
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_fetch_and_increment_counter_ghost_op(&lock->next, pre_, post_, currentThread)() {
            open pre_();
            open_atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox));
            open ticketlock_inv(lock, level, inv, signalsBox)();
            assert growing_list(signalsBox, ?signals);
            assert is_atomic_fetch_and_increment_counter_op(?op, &lock->next, ?P, ?Q);
            assert lock->next |-> ?next;
            open ticketlock_next(lock, _);
            op();
            leak is_atomic_fetch_and_increment_counter_op(_, _, _, _);
            void *signal = create_signal();
            init_signal(signal, append(level, {next}));
            nth_append_r(signals, {signal}, 0);
            consuming_box_predicate growing_list(signalsBox, _)
            perform_action add(signal) {}
            producing_box_predicate growing_list(append(signals, {signal}))
            producing_fresh_handle_predicate has_at(next, signal);
            signals_append(signal);
            close ticketlock_inv(lock, level, inv, signalsBox)();
            close_atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox));
            close post_(next);
        };
        @*/
        //@ close pre_();
        ticket = atomic_fetch_and_increment_counter(&lock->next);
        //@ open post_(_);
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
