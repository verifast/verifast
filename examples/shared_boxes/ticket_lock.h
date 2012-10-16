#ifndef TICKET_LOCK_H
#define TICKET_LOCK_H

struct ticket_lock;

//@ predicate ticket_lock(struct ticket_lock* l, predicate() I);
//@ predicate is_locked(struct ticket_lock* l, real f, predicate() I);

struct ticket_lock* create_ticket_lock();
  //@ requires exists<predicate()>(?I) &*& I();
  //@ ensures result == 0 ? I() : ticket_lock(result, I);

void ticket_lock_acquire(struct ticket_lock* l);
  //@ requires [?f]ticket_lock(l, ?I);
  //@ ensures is_locked(l, f, I) &*& I();

void ticket_lock_release(struct ticket_lock* l);
  //@ requires is_locked(l, ?f, ?I) &*& I();
  //@ ensures [f]ticket_lock(l, I);

void ticket_lock_dispose(struct ticket_lock* l);
  //@ requires ticket_lock(l, ?I);
  //@ ensures I();

#endif
