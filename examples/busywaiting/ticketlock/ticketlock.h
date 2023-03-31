#ifndef TICKETLOCK_H
#define TICKETLOCK_H

struct ticketlock;
typedef struct ticketlock *ticketlock;

//@ predicate ticketlock(ticketlock lock; predicate(int, int) inv);

ticketlock create_ticketlock();
//@ requires exists<predicate(int, int)>(?inv) &*& inv(0, 0);
//@ ensures ticketlock(result, inv);

/*@

typedef lemma void ticketlock_take_ticket_ghost_op(predicate(int, int) inv, predicate() pre, predicate(int) wait_inv, int callerThread)();
    requires inv(?next, ?owner) &*& pre() &*& currentThread == callerThread;
    ensures inv(next + 1, owner) &*& wait_inv(next);

typedef lemma void ticketlock_wait_ghost_op(predicate(int, int) inv, predicate(int) wait_inv, int callerThread)();
    requires inv(?next, ?owner) &*& wait_inv(?ticket) &*& owner < ticket &*& currentThread == callerThread;
    ensures inv(next, owner) &*& wait_inv(ticket) &*& call_perm_(currentThread, ticketlock_acquire);

typedef lemma void ticketlock_acquire_ghost_op(predicate(int, int) inv, predicate(int) wait_inv, predicate() post, int callerThread)();
    requires inv(?next, ?owner) &*& wait_inv(owner) &*& currentThread == callerThread;
    ensures inv(next, owner) &*& post();

@*/

void ticketlock_acquire(ticketlock lock);
/*@
requires
    [?f]ticketlock(lock, ?inv) &*&
    is_ticketlock_take_ticket_ghost_op(?top, inv, ?pre, ?wait_inv, currentThread) &*&
    is_ticketlock_wait_ghost_op(?wop, inv, wait_inv, currentThread) &*&
    is_ticketlock_acquire_ghost_op(?aop, inv, wait_inv, ?post, currentThread) &*&
    pre();
@*/
//@ ensures [f]ticketlock(lock, inv) &*& post();

/*@

typedef lemma void ticketlock_release_ghost_op(predicate(int, int) inv, predicate() pre, predicate() post, int callerThread)();
    requires inv(?next, ?owner) &*& pre() &*& currentThread == callerThread;
    ensures inv(next, owner + 1) &*& post();

@*/

void ticketlock_release(ticketlock lock);
//@ requires [?f]ticketlock(lock, ?inv) &*& is_ticketlock_release_ghost_op(?ghop, inv, ?pre, ?post, currentThread) &*& pre();
//@ ensures [f]ticketlock(lock, inv) &*& post();

#endif
