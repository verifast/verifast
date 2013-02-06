#ifndef GOTSMANLOCK_H
#define GOTSMANLOCK_H

/*@
predicate lock(int* l, predicate() I;); 
predicate locked(int* l, predicate() I);  
@*/

void init(int* l);
  //@ requires integer(l, _) &*& exists<predicate()>(?I);
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

#endif