#ifndef SIMPLELOCK_H
#define SIMPLELOCK_H

struct lock;

//@ predicate is_lock(struct lock* l, predicate() I);
//@ predicate locked(struct lock* l, predicate() I, real f);

struct lock* create_lock();
  //@ requires exists<predicate()>(?I) &*& I();
  //@ ensures result == 0 ? I() : is_lock(result, I);
  
void lock_acquire(struct lock* l);
  //@ requires [?f]is_lock(l, ?I);
  //@ ensures locked(l, I, f) &*& I();
  
void lock_release(struct lock* l);
  //@ requires locked(l, ?I, ?f) &*& I();
  //@ ensures [f]is_lock(l, I);

void lock_dispose(struct lock* l);
  //@ requires is_lock(l, ?I);
  //@ ensures I();
  
#endif
