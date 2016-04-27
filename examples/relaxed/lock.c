/*

Authors: Marko Doko and Viktor Vafeiadis, MPI-SWS; Bart Jacobs, KU Leuven

Based on:
- Viktor Vafeiadis and Chinmay Narayan. Relaxed separation logic: a program logic for C11 concurrency. OOPSLA 2013. http://www.mpi-sws.org/~viktor/papers/oopsla2013-rsl.pdf
- Marko Doko and Viktor Vafeiadis. A program logic for C11 memory fences. VMCAI 2016. http://www.mpi-sws.org/~viktor/papers/vmcai2016-fsl.pdf

*/

#include <assert.h>
#include "relaxed.h"
#include "lock.h"

//@ predicate_ctor lock_internal_inv(predicate() Inv)(int value) = value == 1 ? true : Inv() ;

//@ predicate Lock(int *loc, predicate() J) = Write(loc, lock_internal_inv(J)) &*& RMW(loc, lock_internal_inv(J)) ;

//@ lemma void empty_fun0() requires true; ensures true; {}

void release_lock(int *lock)
    //@ requires Lock(lock, ?J) &*& J();
    //@ ensures Lock(lock, J);
{
    //@ open Lock(lock,J);
    //@ close lock_internal_inv(J)(0);
    atomic_store_explicit(lock,0,memory_order_release);
    //@ close Lock(lock,J);
}

void acquire_lock(int *lock)
    //@ requires Lock(lock, ?J);
    //@ ensures Lock(lock, J) &*& J();
{
    bool b;
    for (;;) 
        //@ invariant Lock(lock, J); 
    { 
        //@ open Lock(_,_);
        /*@ 
            produce_lemma_function_pointer_chunk(empty_fun0) : CAS_premise(0, 1, True, lock_internal_inv(J), J)() { 
                open lock_internal_inv(J)(0); 
                open True(); 
                close lock_internal_inv(J)(1); 
                call();
            };
        @*/
        //@ close True();
        b = atomic_compare_exchange_acquire_release(lock, 0, 1);
        if (b) {
            break;
        }
        //@ close Lock (lock, J);
        //@ open True();
    }
    //@ close Lock (lock, J);
}

void new_lock(int *lock)
    //@ requires exists<predicate()>(?J) &*& *lock |-> ?v &*& J();
    //@ ensures Lock(lock, J);
{
    //@ open exists(_);
    *lock = 0;
    //@ close lock_internal_inv(J)(0); 
    //@ convert_to_atomic_rmw(lock, lock_internal_inv(J));
    //@ close Lock(lock, J);
}

/*@

lemma void dup_lock(int *lock)
    requires Lock(lock, ?J);
    ensures Lock(lock, J) &*& Lock(lock, J);
{
    open Lock(lock, J);
    dup_Write(lock);
    dup_RMW(lock);
    close Lock(lock, J);
    close Lock(lock, J);
}

@*/

