#include <stdlib.h>
#include "../busywaiting.h"
#include "atomics.h"
#include "ticketlock.h"

typedef struct ticketlock {
    unsigned long long next;
    unsigned long long owner;
} *ticketlock;

/*@

//predicate ticketlock(ticketlock lock; predicate(int, int) inv);

@*/

ticketlock create_ticketlock()
//@ requires exists<predicate(int, int)>(?inv) &*& inv(0, 0);
//@ ensures ticketlock(result, inv);
{
    ticketlock result = malloc(sizeof(struct ticketlock));
    if (result == 0) abort();
    result->next = 0;
    result->owner = 0;
    return result;
}

void ticketlock_acquire(ticketlock lock)
/*@
requires
    [?f]ticketlock(lock, ?inv) &*&
    is_ticketlock_take_ticket_ghost_op(?top, inv, ?pre, ?wait_inv, currentThread) &*&
    is_ticketlock_wait_ghost_op(?wop, inv, wait_inv, currentThread) &*&
    is_ticketlock_acquire_ghost_op(?aop, inv, wait_inv, ?post, currentThread) &*&
    pre();
@*/
//@ ensures [f]ticketlock(lock, inv) &*& post();
{
    unsigned long long ticket;
    ticket = atomic_fetch_and_increment_counter(&lock->next);
    for (;;)
    {
        unsigned long long owner;
        owner = atomic_load_counter(&lock->owner);
        if (owner == ticket)
            break;
    }
}

void ticketlock_release(ticketlock lock)
//@ requires [?f]ticketlock(lock, ?inv) &*& is_ticketlock_release_ghost_op(?ghop, inv, ?pre, ?post, currentThread) &*& pre();
//@ ensures [f]ticketlock(lock, inv) &*& post();
{
    unsigned long long owner = load_counter(&lock->owner);
    atomic_store_counter(&lock->owner, owner + 1);
}
