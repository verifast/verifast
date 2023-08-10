// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#ifndef CLHLOCK_AS_TICKETLOCK_H
#define CLHLOCK_AS_TICKETLOCK_H

#include "../busywaiting.h"

struct clhlock_as_ticketlock;
struct clhlock_as_ticketlock_thread;

/*@

predicate clhlock_as_ticketlock(struct clhlock_as_ticketlock *lock; predicate(int, int, bool) inv);
predicate clhlock_as_ticketlock_thread(struct clhlock_as_ticketlock_thread *thread);
predicate clhlock_as_ticketlock_locked(struct clhlock_as_ticketlock_thread *thread, struct clhlock_as_ticketlock *lock, predicate(int, int, bool) inv, real frac, int ticket);

@*/

struct clhlock_as_ticketlock *create_clhlock_as_ticketlock();
    //@ requires exists<predicate(int, int, bool)>(?inv) &*& inv(0, 0, false);
    //@ ensures clhlock_as_ticketlock(result, inv);
    //@ terminates;

struct clhlock_as_ticketlock_thread *create_clhlock_as_ticketlock_thread();
    //@ requires true;
    //@ ensures clhlock_as_ticketlock_thread(result);
    //@ terminates;

/*@

typedef lemma void clhlock_as_ticketlock_get_ticket_ghost_op(predicate(int, int, bool) inv, predicate() pre, predicate(int, void *) wait_inv, int acquireThread)(void *f);
    requires inv(?owner, ?nextTicket, ?held) &*& pre() &*& currentThread == acquireThread &*& func_lt(f, clhlock_as_ticketlock_acquire) == true;
    ensures inv(owner, nextTicket + 1, held) &*& wait_inv(nextTicket, f);

typedef lemma void clhlock_as_ticketlock_wait_ghost_op(predicate(int, int, bool) inv, predicate(int, void *) wait_inv, int acquireThread)();
    requires inv(?owner, ?nextTicket, ?held) &*& wait_inv(?ticket, ?f) &*& owner < ticket &*& ticket < nextTicket &*& currentThread == acquireThread;
    ensures inv(owner, nextTicket, held) &*& wait_inv(ticket, f) &*& call_perm_(currentThread, f);

typedef lemma void clhlock_as_ticketlock_acquire_ghost_op(predicate(int, int, bool) inv, predicate(int, void *) wait_inv, predicate(int) post, int acquireThread)();
    requires inv(?owner, ?nextTicket, false) &*& wait_inv(owner, _) &*& owner < nextTicket &*& currentThread == acquireThread;
    ensures inv(owner, nextTicket, true) &*& post(owner);

@*/

void clhlock_as_ticketlock_acquire(struct clhlock_as_ticketlock_thread *thread, struct clhlock_as_ticketlock *lock);
    /*@
    requires
        clhlock_as_ticketlock_thread(thread) &*& [?frac]clhlock_as_ticketlock(lock, ?inv) &*&
        is_clhlock_as_ticketlock_get_ticket_ghost_op(?getTicket, inv, ?pre, ?wait_inv, currentThread) &*&
        is_clhlock_as_ticketlock_wait_ghost_op(?wait, inv, wait_inv, currentThread) &*&
        is_clhlock_as_ticketlock_acquire_ghost_op(?acq, inv, wait_inv, ?post, currentThread) &*&
        pre();
    @*/
    //@ ensures clhlock_as_ticketlock_locked(thread, lock, inv, frac, ?ticket) &*& post(ticket);
    //@ terminates;

/*@

typedef lemma void clhlock_as_ticketlock_release_ghost_op(predicate(int, int, bool) inv, int ticket, predicate() pre, predicate() post, int releaseThread)();
    requires inv(ticket, ?nextTicket, true) &*& pre() &*& currentThread == releaseThread;
    ensures inv(ticket + 1, nextTicket, false) &*& post();

@*/

void clhlock_as_ticketlock_release(struct clhlock_as_ticketlock_thread *thread);
    //@ requires clhlock_as_ticketlock_locked(thread, ?lock, ?inv, ?frac, ?ticket) &*& is_clhlock_as_ticketlock_release_ghost_op(?rel, inv, ticket, ?pre, ?post, currentThread) &*& pre();
    //@ ensures clhlock_as_ticketlock_thread(thread) &*& [frac]clhlock_as_ticketlock(lock, inv) &*& post();
    //@ terminates;

void dispose_clhlock_as_ticketlock_thread(struct clhlock_as_ticketlock_thread *thread);
    //@ requires clhlock_as_ticketlock_thread(thread);
    //@ ensures true;
    //@ terminates;

void dispose_clhlock_as_ticketlock(struct clhlock_as_ticketlock *lock);
    //@ requires clhlock_as_ticketlock(lock, ?inv);
    //@ ensures inv(?owner, owner, false);
    //@ terminates;

#endif
