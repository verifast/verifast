/*

Authors: Marko Doko and Viktor Vafeiadis, MPI-SWS; Bart Jacobs, KU Leuven

Based on:
- Viktor Vafeiadis and Chinmay Narayan. Relaxed separation logic: a program logic for C11 concurrency. OOPSLA 2013. http://www.mpi-sws.org/~viktor/papers/oopsla2013-rsl.pdf
- Marko Doko and Viktor Vafeiadis. A program logic for C11 memory fences. VMCAI 2016. http://www.mpi-sws.org/~viktor/papers/vmcai2016-fsl.pdf

*/

#include <assert.h>
#include "relaxed.h"
#include "lock.h"

// A simple client of the lock specification

int a;
int b = 0;
int l;

//@ predicate myInv() = b |-> ?vb &*& (vb == 0 ? true : a |-> 7);

void sender()
    //@ requires Lock(&l, myInv) &*& a|->_;
    //@ ensures Lock(&l, myInv);
{
    a = 7;
    acquire_lock(&l);
    //@ open myInv();
    //@ if (b != 0) { integer_distinct(&a,&a); }
    b = 1;
    //@ close myInv();
    release_lock(&l);
}

void receiver()
    //@ requires Lock(&l, myInv);
    //@ ensures Lock(&l, myInv) &*& a|->8;
{
    for(;;) 
    	//@ invariant Lock(&l, myInv);
    { 
        acquire_lock(&l);
        //@ open myInv();
        if (b) break;
        //@ close myInv();
        release_lock(&l);
    }
    b = 0;
    //@ close myInv();
    release_lock(&l);
    a++;
}


int main() //@ : main_full(lock_client)
    //@ requires module(lock_client, true);
    //@ ensures true;
{
    //@ open_module();
    //@ close exists(myInv);
    //@ close myInv();
    new_lock(&l);
    //@ dup_lock(&l);
    sender();
    receiver();
    assert(a == 8);
    //@ leak Lock(&l, _) &*& Lock(&l, _) &*& a |-> 8;
    return 0;
}
