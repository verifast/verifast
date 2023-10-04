#ifndef CLHLOCK_H
#define CLHLOCK_H

#include "../busywaiting.h"

struct lock;
struct lock_thread;

/*@

predicate lock(struct lock *lock, level level, predicate() inv;);
predicate lock_thread(struct lock_thread *thread);
predicate locked(struct lock_thread *thread, struct lock *lock, level level, predicate() inv, real frac, pair<void *, level> ob);

@*/

struct lock *create_lock();
    //@ requires exists<level>(?level) &*& exists<predicate()>(?inv) &*& inv();
    //@ ensures lock(result, level, inv);
    //@ terminates;

struct lock_thread *create_lock_thread();
    //@ requires true;
    //@ ensures lock_thread(result);
    //@ terminates;

void acquire(struct lock_thread *thread, struct lock *lock);
    //@ requires obs(?p, ?obs) &*& lock_thread(thread) &*& [?frac]lock(lock, ?level, ?inv) &*& forall(map(snd, obs), (level_lt)(level)) == true;
    //@ ensures locked(thread, lock, level, inv, frac, ?ob) &*& inv() &*& obs(?p1, cons(ob, obs)) &*& is_ancestor_of(p, p1) == true &*& level_of(ob) == level;
    //@ terminates;

void release(struct lock_thread *thread);
    //@ requires locked(thread, ?lock, ?level, ?inv, ?frac, ?ob) &*& inv() &*& obs(?p, ?obs) &*& mem(ob, obs) == true;
    //@ ensures obs(?p1, remove(ob, obs)) &*& lock_thread(thread) &*& [frac]lock(lock, level, inv) &*& is_ancestor_of(p, p1) == true;
    //@ terminates;

/*@

typedef lemma void release_ghost_op(int threadId, predicate() inv, list<pathcomp> p, list<pair<void *, level> > obs, predicate() pre, predicate(list<pathcomp>) post)();
    requires obs(?p1, obs) &*& pre() &*& currentThread == threadId &*& is_ancestor_of(p, p1) == true;
    ensures obs(p1, obs) &*& inv() &*& post(p1);

@*/

void release_with_ghost_op(struct lock_thread *thread);
    //@ requires locked(thread, ?lock, ?level, ?inv, ?frac, ?ob) &*& obs(?p, ?obs) &*& mem(ob, obs) == true &*& is_release_ghost_op(_, currentThread, inv, p, remove(ob, obs), ?pre, ?post) &*& pre();
    //@ ensures post(?p1) &*& obs(?p2, remove(ob, obs)) &*& lock_thread(thread) &*& [frac]lock(lock, level, inv) &*& is_ancestor_of(p1, p2) == true;
    //@ terminates;

void dispose_lock_thread(struct lock_thread *thread);
    //@ requires lock_thread(thread);
    //@ ensures true;
    //@ terminates;

void dispose_lock(struct lock *lock);
    //@ requires lock(lock, ?level, ?inv);
    //@ ensures inv();
    //@ terminates;

#endif
