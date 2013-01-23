#ifndef TICKETLOCK_CAP_H
#define TICKETLOCK_CAP_H

struct ticketlock;

//@ predicate ticketlock(struct ticketlock* l);
//@ predicate is_locked(struct ticketlock* l, real f);

struct ticketlock* create_ticketlock();
  //@ requires true;
  //@ ensures result == 0 ? true : ticketlock(result);

void ticket_lock_lock(struct ticketlock* l);
  //@ requires [?f]ticketlock(l);
  //@ ensures is_locked(l, f);

void ticket_lock_unlock(struct ticketlock* l);
  //@ requires is_locked(l, ?f);
  //@ ensures [f]ticketlock(l);

/*@
lemma void not_locked_twice(struct ticketlock* l);
  requires is_locked(l, _) &*& is_locked(l, _);
  ensures false;
@*/

#endif
