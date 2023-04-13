#include <stdlib.h>
#include "../busywaiting.h"
#include "atomics.h"
#include "ticketlock.h"
//@ #include <quantifiers.gh>

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

box_class incr_box(int i) {
  invariant true;
  action noop();
    requires true;
    ensures i == old_i;
  action incr();
    requires true;
    ensures i == old_i + 1;
  handle_predicate is_lower_bound(int j) {
    invariant j <= i;
    preserved_by noop() {}
    preserved_by incr() {}
  }
}

@*/

typedef struct ticketlock {
    //@ list<int> level;
    //@ predicate(int, bool) inv_;
    unsigned long long next;
    unsigned long long owner;
    //@ bool held_;
    //@ box signalsBox;
    //@ box incrBox;
} *ticketlock;

/*@

lemma_auto void ticketlock_nb_level_dims_nonneg()
    requires true;
    ensures 0 <= ticketlock_nb_level_dims();
{}

predicate signals(list<void *> signals, list<int> baseLevel, bool status, int start, int stop) =
    start == stop ?
        true
    :
        signal(nth(start, signals), append(baseLevel, {start}), status) &*& signals(signals, baseLevel, status, start + 1, stop);

lemma void signals_append(bool status, list<void *> signals2)
    requires signals(?signals, ?level, status, ?start, ?stop) &*& 0 <= start &*& start <= stop &*& stop <= length(signals);
    ensures signals(append(signals, signals2), level, status, start, stop);
{
    open signals(signals, level, status, start, stop);
    if (start == stop) {
    } else {
        nth_append(signals, signals2, start);
        signals_append(status, signals2);
    }
    close signals(append(signals, signals2), level, status, start, stop);
}

lemma void signals_stop_plus_1(bool status)
    requires signals(?signals, ?level, status, ?start, ?stop) &*& signal(nth(stop, signals), append(level, {stop}), status) &*& 0 <= start &*& start <= stop &*& stop < length(signals);
    ensures signals(signals, level, status, start, stop + 1);
{
    open signals(signals, level, status, start, stop);
    if (start == stop) {
        close signals(signals, level, status, start + 1, stop + 1);
    } else {
        signals_stop_plus_1(status);
    }
    close signals(signals, level, status, start, stop + 1);
}

predicate_ctor ticketlock_inv(ticketlock lock, list<int> level, predicate(int, bool) inv, box signalsBox, box incrBox)() =
    growing_list(signalsBox, ?signals) &*&
    counter(&lock->next, ?next) &*& length(signals) == next &*&
    [1/2]counter(&lock->owner, ?owner) &*& 0 <= owner &*& owner <= next &*& incr_box(incrBox, owner) &*&
    [1/2]lock->held_ |-> ?held &*&
    signals(signals, level, true, 0, owner) &*&
    signals(signals, level, false, held ? owner + 1 : owner, length(signals)) &*&
    inv(owner, held) &*&
    held ?
        signal(nth(owner, signals), append(level, {owner}), true) &*& owner < next
    :
        [1/2]counter(&lock->owner, owner) &*& [1/2]lock->held_ |-> held;

predicate ticketlock(ticketlock lock; list<int> level, predicate(int, bool) inv) =
    lock->level |-> level &*& lock->inv_ |-> inv &*& lock->signalsBox |-> ?signalsBox &*& lock->incrBox |-> ?incrBox &*& malloc_block_ticketlock(lock) &*&
    level == cons(?level_max_length, ?level0) &*& length(level0) + ticketlock_nb_level_dims <= level_max_length &*&
    pointer_within_limits(&lock->owner) == true &*&
    atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox));

predicate ticketlock_held(ticketlock lock, list<int> level, predicate(int, bool) inv, real f) =
    [f]lock->level |-> level &*& [f]lock->inv_ |-> inv &*& [f]lock->signalsBox |-> ?signalsBox &*& [f]lock->incrBox |-> ?incrBox &*& [f]malloc_block_ticketlock(lock) &*&
    level == cons(?level_max_length, ?level0) &*& length(level0) + ticketlock_nb_level_dims <= level_max_length &*&
    pointer_within_limits(&lock->owner) == true &*&
    [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox)) &*&
    [1/2]lock->held_ |-> true &*& [1/2]counter(&lock->owner, _);

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
    //@ create_box incrBox = incr_box(0);
    //@ result->incrBox = incrBox;
    //@ result->held_ = false;
    //@ close signals({}, level, true, 0, 0);
    //@ close signals({}, level, false, 0, 0);
    //@ create_counter(&result->next);
    //@ create_counter(&result->owner);
    //@ close ticketlock_inv(result, level, inv, signalsBox, incrBox)();
    //@ create_atomic_space(create_ticketlock, ticketlock_inv(result, level, inv, signalsBox, incrBox));
    return result;
}

void ticketlock_acquire_helper(ticketlock lock, unsigned long long ticket)
/*@
requires
    [?f]lock->level |-> ?level &*& [f]lock->inv_ |-> ?inv &*& [f]lock->signalsBox |-> ?signalsBox &*& [f]lock->incrBox |-> ?incrBox &*& [f]malloc_block_ticketlock(lock) &*&
    level == cons(?level_max_length, ?level0) &*& length(level0) + ticketlock_nb_level_dims <= level_max_length &*&
    [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox)) &*&
    has_at(?hasAtHandle, signalsBox, ticket, ?signal) &*&
    is_ticketlock_wait_ghost_op(?wop, ?p, level, inv, ?wait_inv, currentThread) &*&
    is_ticketlock_acquire_ghost_op(?aop, p, level, inv, wait_inv, ?post, currentThread) &*&
    wait_inv(-1, _) &*& call_below_perms(ticket + 1, p, ticketlock_acquire) &*& is_lower_bound(_, incrBox, -1) &*&
    pointer_within_limits(&lock->owner) == true &*&
    obs(p, cons(pair(signal, append(level, {ticket})), ?obs)) &*&
    forall(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, level)) == true &*&
    call_below_perm_(currentThread, ticketlock_acquire);
@*/
//@ ensures ticketlock_held(lock, level, inv, f) &*& post();
//@ terminates;
{
    //@ close exists(false);
    for (;;)
    /*@
    invariant
        [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox)) &*&
        has_at(hasAtHandle, signalsBox, ticket, signal) &*&
        is_ticketlock_wait_ghost_op(wop, p, level, inv, wait_inv, currentThread) &*&
        is_ticketlock_acquire_ghost_op(aop, p, level, inv, wait_inv, post, currentThread) &*&
        obs(p, cons(pair(signal, append(level, {ticket})), obs)) &*&
        exists<bool>(?startedWaiting) &*&
        wait_inv(?owner0, ?f0) &*& call_below_perms(ticket - owner0, p, ticketlock_acquire) &*& is_lower_bound(?lbHandle, incrBox, owner0) &*& (owner0 == -1 || f0 == ticketlock_acquire_helper) &*&
        startedWaiting ?
            1 <= ticket &*& has_at(_, signalsBox, ticket - 1, ?predecessorSignal) &*& wait_perm(p, predecessorSignal, append(level, {ticket - 1}), ticketlock_acquire_helper)
        :
            call_below_perm_(currentThread, ticketlock_acquire);
    @*/
    {
        //@ open exists(startedWaiting);
        unsigned long long owner;
        {
            /*@
            predicate pre_() =
                [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox)) &*&
                has_at(hasAtHandle, signalsBox, ticket, signal) &*&
		is_ticketlock_wait_ghost_op(wop, p, level, inv, wait_inv, currentThread) &*&
		is_ticketlock_acquire_ghost_op(aop, p, level, inv, wait_inv, post, currentThread) &*&
		obs(p, cons(pair(signal, append(level, {ticket})), obs)) &*&
		wait_inv(owner0, f0) &*& call_below_perms(ticket - owner0, p, ticketlock_acquire) &*& is_lower_bound(lbHandle, incrBox, owner0) &*& (owner0 == -1 || f0 == ticketlock_acquire_helper) &*&            
		startedWaiting ?
		    1 <= ticket &*& has_at(_, signalsBox, ticket - 1, ?predecessorSignal) &*& wait_perm(p, predecessorSignal, append(level, {ticket - 1}), ticketlock_acquire_helper)
		:
		    call_below_perm_(currentThread, ticketlock_acquire);
            predicate post_(int result) =
                [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox)) &*&
                result == ticket ?
                    post() &*&
                    [1/2]lock->held_ |-> true &*&
                    [1/2]counter(&lock->owner, ticket)
                :
                    call_perm_(currentThread, ticketlock_acquire_helper) &*&
                    has_at(hasAtHandle, signalsBox, ticket, signal) &*&
		    is_ticketlock_wait_ghost_op(wop, p, level, inv, wait_inv, currentThread) &*&
		    is_ticketlock_acquire_ghost_op(aop, p, level, inv, wait_inv, post, currentThread) &*&
		    obs(p, cons(pair(signal, append(level, {ticket})), obs)) &*&
		    exists<bool>(?startedWaiting1) &*&
		    wait_inv(?owner1, ?f1) &*& call_below_perms(ticket - owner1, p, ticketlock_acquire) &*& is_lower_bound(?lbHandle1, incrBox, owner1) &*& (owner1 == -1 || f1 == ticketlock_acquire_helper) &*&            
		    startedWaiting1 ?
		        1 <= ticket &*& has_at(_, signalsBox, ticket - 1, ?predecessorSignal) &*& wait_perm(p, predecessorSignal, append(level, {ticket - 1}), ticketlock_acquire_helper)
		    :
		        call_below_perm_(currentThread, ticketlock_acquire);
            @*/
            /*@
            produce_lemma_function_pointer_chunk atomic_load_counter_ghost_op(&lock->owner, pre_, post_, currentThread)() {
                open pre_();
                open_atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox));
                open ticketlock_inv(lock, level, inv, signalsBox, incrBox)();
                consuming_box_predicate growing_list(signalsBox, ?signals)
                consuming_handle_predicate has_at(hasAtHandle, ticket, signal)
                perform_action noop() {}
                producing_box_predicate growing_list(signals)
                producing_handle_predicate has_at(hasAtHandle, ticket, signal);
                assert is_atomic_load_counter_op(?op, &lock->owner, ?P, ?Q);
                assert [1/2]counter(&lock->owner, ?owner_);
                op();
                if (owner_ == ticket) {
                    if (lock->held_) {
                        ob_signal_not_set(signal);
                        assert false;
                    }
                    lock->held_ = true;
                    open signals(signals, level, false, owner_, length(signals));
                    set_signal(signal);
                    leak has_at(hasAtHandle, signalsBox, ticket, signal);
                    is_ancestor_of_refl(p);
                    aop();
                    leak is_ticketlock_acquire_ghost_op(aop, p, level, inv, wait_inv, post, currentThread);
                    leak is_ticketlock_wait_ghost_op(wop, p, level, inv, wait_inv, currentThread);
                    leak call_below_perms(ticket - owner0, p, ticketlock_acquire);
                    leak is_lower_bound(_, _, _);
                    if (startedWaiting) {
                        leak has_at(_, signalsBox, ticket - 1, ?predecessorSignal) &*& wait_perm(p, predecessorSignal, append(level, {ticket - 1}), ticketlock_acquire_helper);
                    } else {
                        leak call_below_perm_(currentThread, ticketlock_acquire);
                    }
                } else {
                    if (ticket < owner_) {
                        lemma void iter(int i)
                            requires
                                signals(signals, level, true, i, owner_) &*& 0 <= i &*& i <= ticket &*&
                                obs(p, cons(pair(signal, append(level, {ticket})), obs));
                            ensures false;
                        {
                            open signals(signals, level, true, i, owner_);
                            if (i == ticket) {
                                ob_signal_not_set(signal);
                                assert false;
                            } else {
                                iter(i + 1);
                            }
                        }
                        iter(0);
                        assert false;
                    }
                    if (lock->held_) {
                        is_ancestor_of_refl(p);
                        if (!forall(map(snd, obs), (level_lt)(level))) {
                            list<int> badLevel = not_forall(map(snd, obs), (level_lt)(level));
                            forall_elim(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, level), badLevel);
                            assert badLevel == cons(level_max_length, ?badLevel0);
                            all_sublevel0s_lt_append(level_max_length, level0, {}, badLevel0);
                            assert false;
                        }
                        level0_lt_append(level_max_length, level0, {}, {ticket});
                        consuming_box_predicate incr_box(incrBox, owner_)
                        consuming_handle_predicate is_lower_bound(lbHandle, owner0)
                        perform_action noop() {}
                        producing_box_predicate incr_box(owner_)
                        producing_handle_predicate is_lower_bound(lbHandle, owner_);
                        if (owner0 != owner_)
                            open call_below_perms(ticket - owner0, _, _);
                        wop(ticketlock_acquire_helper);
                        call_below_perms_weaken(ticket - owner_);
                        close exists(startedWaiting);
                    } else {
                        if (startedWaiting) {
                            assert has_at(?h, signalsBox, ticket - 1, ?predecessorSignal);
		            consuming_box_predicate growing_list(signalsBox, signals)
		            consuming_handle_predicate has_at(h, ticket - 1, predecessorSignal)
		            perform_action noop() {}
		            producing_box_predicate growing_list(signals)
		            producing_handle_predicate has_at(h, ticket - 1, predecessorSignal);
                        } else {
		            consuming_box_predicate growing_list(signalsBox, signals)
		            perform_action noop() {}
		            producing_box_predicate growing_list(signals)
		            producing_fresh_handle_predicate has_at(ticket - 1, nth(ticket - 1, signals));
                            pathize_call_below_perm_();
                            create_wait_perm(nth(ticket - 1, signals), append(level, {ticket - 1}), ticketlock_acquire_helper);
                        }
                        {
                            lemma void iter(int i)
                            requires
                                signals(signals, level, false, i, length(signals)) &*&
                                obs(p, cons(pair(signal, append(level, {ticket})), obs)) &*&
                                wait_perm(p, nth(ticket - 1, signals), append(level, {ticket - 1}), ticketlock_acquire_helper) &*&
                                owner_ <= i &*& i <= ticket - 1;
                            ensures
                                obs(p, cons(pair(signal, append(level, {ticket})), obs)) &*&
                                wait_perm(p, nth(ticket - 1, signals), append(level, {ticket - 1}), ticketlock_acquire_helper) &*&
                                signals(signals, level, false, i, length(signals)) &*&
                                call_perm_(currentThread, ticketlock_acquire_helper);
                            {
                                open signals(signals, level, false, i, length(signals));
                                if (i == ticket - 1) {
                                    is_ancestor_of_refl(p);
                                    level0_lt_append(level_max_length, level0, {ticket - 1}, {ticket});
                                    if (!forall(map(snd, obs), (level_lt)(append(level, {ticket - 1})))) {
                                        list<int> badLevel = not_forall(map(snd, obs), (level_lt)(append(level, {ticket - 1})));
                                        forall_elim(map(snd, obs), (all_sublevels_lt)(ticketlock_nb_level_dims, level), badLevel);
                                        assert badLevel == cons(level_max_length, ?badLevel0);
                                        all_sublevel0s_lt_append(level_max_length, level0, {ticket - 1}, badLevel0);
                                        assert false;
                                    }
                                    wait(nth(ticket - 1, signals));
                                } else {
                                    iter(i + 1);
                                }
                                close signals(signals, level, false, i, length(signals));
                            }
                            iter(owner_);
                        }
                        close exists(true);
                    }
                }
                close ticketlock_inv(lock, level, inv, signalsBox, incrBox)();
                close_atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox));
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
    //@ close ticketlock_held(lock, level, inv, f);
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
//@ ensures ticketlock_held(lock, level, inv, f) &*& post();
//@ terminates;
{
    //@ box signalsBox = lock->signalsBox;
    //@ box incrBox = lock->incrBox;
    unsigned long long ticket;
    {
        /*@
        predicate pre_() =
            obs(p, obs) &*&
            [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox));
        predicate post_(int result) =
            has_at(_, signalsBox, result, ?signal) &*&
            obs(p, cons(pair(signal, append(level, {result})), obs)) &*&
            is_lower_bound(_, incrBox, -1) &*&
            [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox));
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_fetch_and_increment_counter_ghost_op(&lock->next, pre_, post_, currentThread)() {
            open pre_();
            open_atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox));
            open ticketlock_inv(lock, level, inv, signalsBox, incrBox)();
            assert growing_list(signalsBox, ?signals);
            assert is_atomic_fetch_and_increment_counter_op(?op, &lock->next, ?P, ?Q);
            assert [_]counter(&lock->owner, ?owner);
            assert counter(&lock->next, ?next);
            op();
            leak is_atomic_fetch_and_increment_counter_op(_, _, _, _);
            void *signal = create_signal();
            init_signal(signal, append(level, {next}));
            nth_append_r(signals, {signal}, 0);
            consuming_box_predicate growing_list(signalsBox, _)
            perform_action add(signal) {}
            producing_box_predicate growing_list(append(signals, {signal}))
            producing_fresh_handle_predicate has_at(next, signal);
            signals_append(true, {signal});
            signals_append(false, {signal});
            signals_stop_plus_1(false);
            consuming_box_predicate incr_box(incrBox, owner)
            perform_action noop() {}
            producing_box_predicate incr_box(owner)
            producing_fresh_handle_predicate is_lower_bound(-1);
            if (lock->held_)
                nth_append(signals, {signal}, owner);
            close ticketlock_inv(lock, level, inv, signalsBox, incrBox)();
            close_atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox));
            close post_(next);
        };
        @*/
        //@ close pre_();
        ticket = atomic_fetch_and_increment_counter(&lock->next);
        //@ open post_(_);
    }
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm__multi(ticket + 1);
    //@ produce_call_below_perm_();
    ticketlock_acquire_helper(lock, ticket);
}

void ticketlock_release(ticketlock lock)
//@ requires ticketlock_held(lock, ?level, ?inv, ?f) &*& is_ticketlock_release_ghost_op(?ghop, inv, ?pre, ?post, currentThread) &*& pre();
//@ ensures [f]ticketlock(lock, level, inv) &*& post();
//@ terminates;
{
    //@ open ticketlock_held(lock, level, inv, f);
    //@ box signalsBox = lock->signalsBox;
    //@ box incrBox = lock->incrBox;
    unsigned long long ownerPlusOne = get_counter_plus_one(&lock->owner);
    {
        /*@
        predicate pre_() =
	    [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox)) &*&
	    is_ticketlock_release_ghost_op(ghop, inv, pre, post, currentThread) &*& pre() &*&
	    [1/2]lock->held_ |-> true &*& [1/2]counter(&lock->owner, ownerPlusOne - 1);
        predicate post_() =
            post() &*&
            [f]atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox));
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_counter_ghost_op(&lock->owner, ownerPlusOne, pre_, post_, currentThread)() {
            open pre_();
            open_atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox));
            open ticketlock_inv(lock, level, inv, signalsBox, incrBox)();
            
            assert counter(&lock->owner, ?owner);
            
            assert is_atomic_store_counter_op(?op, &lock->owner, ownerPlusOne, ?P, ?Q);
            op();
            
            consuming_box_predicate incr_box(incrBox, owner)
            perform_action incr() {}
            producing_box_predicate incr_box(owner + 1);
            
            signals_stop_plus_1(true);
            lock->held_ = false;
            
            ghop();
            leak is_ticketlock_release_ghost_op(ghop, inv, pre, post, currentThread);
            
            close ticketlock_inv(lock, level, inv, signalsBox, incrBox)();
            close_atomic_space(create_ticketlock, ticketlock_inv(lock, level, inv, signalsBox, incrBox));
            close post_();
        };
        @*/
        //@ close pre_();
        atomic_store_counter(&lock->owner, ownerPlusOne);
        //@ open post_();
    }
}
