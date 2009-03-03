#ifndef ATOMICS_H
#define ATOMICS_H

void *atomic_load_pointer(void **pp); //@ atomic
    //@ requires pointer(pp, ?p);
    //@ ensures pointer(pp, p) &*& result == p;

bool atomic_compare_and_store_pointer(void **pp, void *old, void *new); //@ atomic
    //@ requires pointer(pp, ?p0);
    //@ ensures pointer(pp, ?p1) &*& (result ? p0 == old && p1 == new : p1 == p0);

#endif