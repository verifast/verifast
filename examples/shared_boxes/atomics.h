#ifndef ATOMICS_H
#define ATOMICS_H

void *atomic_load_pointer(void **pp); // atomic
    //@ requires pointer(pp, ?p);
    //@ ensures pointer(pp, p) &*& result == p;

int atomic_load_int(int *i); // atomic
    //@ requires integer(i, ?v);
    //@ ensures integer(i, v) &*& result == v;

void* atomic_compare_and_set_pointer(void **pp, void *old, void *new); // atomic
    //@ requires pointer(pp, ?p0);
    //@ ensures pointer(pp, ?p1) &*& (p0 == old ? p1 == new : p1 == p0) &*& result == p0;

#endif
