/*

Authors: Marko Doko and Viktor Vafeiadis, MPI-SWS; Bart Jacobs, KU Leuven

Based on:
- Viktor Vafeiadis and Chinmay Narayan. Relaxed separation logic: a program logic for C11 concurrency. OOPSLA 2013. http://www.mpi-sws.org/~viktor/papers/oopsla2013-rsl.pdf
- Marko Doko and Viktor Vafeiadis. A program logic for C11 memory fences. VMCAI 2016. http://www.mpi-sws.org/~viktor/papers/vmcai2016-fsl.pdf

*/

//@ predicate Lock(int *loc, predicate() J);

void release_lock(int *lock);
    //@ requires Lock(lock, ?J) &*& J();
    //@ ensures Lock(lock, J);

void acquire_lock(int *lock);
    //@ requires Lock(lock, ?J);
    //@ ensures Lock(lock, J) &*& J();

void new_lock(int *lock);
    //@ requires exists<predicate()>(?J) &*& *lock |-> ?v &*& J();
    //@ ensures Lock(lock, J);

/*@

lemma void dup_lock(int *lock);
    requires Lock(lock, ?J);
    ensures Lock(lock, J) &*& Lock(lock, J);

@*/

