#ifndef GOTSMANLOCK_H
#define GOTSMANLOCK_H

/*@
predicate lock(int* l, predicate() I); 
predicate locked(int* l, predicate() I);  
@*/

void init(int* l);
  //@ requires *l |-> _ &*& exists<predicate()>(?I);
  //@ ensures lock(l, I) &*& locked(l, I);
  
void acquire(int* l);
  //@ requires [?f]lock(l, ?I);
  //@ ensures [f]lock(l, I) &*& locked(l, I) &*& I();
  
void release(int* l);
  //@ requires locked(l, ?I) &*& I();
  //@ ensures true;

void finalize(int* l);
  //@ requires lock(l, ?I) &*& locked(l, I);
  //@ ensures integer(l, _);


/*lemma*/ void merge_locks(int* l); // todo: change to lemma
  //@ requires [?f1]lock(l, ?I) &*& [?f2]lock(l, I) &*& locked(l, I);
  //@ ensures [f1 + f2]lock(l, I) &*& locked(l, I);
#endif