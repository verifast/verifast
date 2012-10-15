#ifndef SPINLOCK_H
#define SPINLOCK_H

struct spinlock;

//@ predicate spinlock(struct spinlock* l, predicate() I);
//@ predicate locked(struct spinlock* l, predicate() I, real f);

struct spinlock* create_spinlock();
  //@ requires exists<predicate()>(?I) &*& I();
  //@ ensures result == 0 ? I() : spinlock(result, I);
  
void spinlock_acquire(struct spinlock* l);
  //@ requires [?f]spinlock(l, ?I);
  //@ ensures locked(l, I, f) &*& I();
  
void spinlock_release(struct spinlock* l);
  //@ requires locked(l, ?I, ?f) &*& I();
  //@ ensures [f]spinlock(l, I);

void spinlock_dispose(struct spinlock* l);
  //@ requires spinlock(l, ?I);
  //@ ensures I();

/*@
lemma void change_invariant(struct spinlock* l, predicate() J);
  requires spinlock(l, ?I) &*& J();
  ensures spinlock(l, J) &*& I();
@*/
  
#endif
