/*

Authors: Marko Doko and Viktor Vafeiadis, MPI-SWS; Bart Jacobs, KU Leuven

Based on:
- Viktor Vafeiadis and Chinmay Narayan. Relaxed separation logic: a program logic for C11 concurrency. OOPSLA 2013. http://www.mpi-sws.org/~viktor/papers/oopsla2013-rsl.pdf
- Marko Doko and Viktor Vafeiadis. A program logic for C11 memory fences. VMCAI 2016. http://www.mpi-sws.org/~viktor/papers/vmcai2016-fsl.pdf

*/

#include <assert.h>
#include "relaxed.h"

int a;
int b;
int c = 0;

//@ fixpoint predicate(int) Q() { return sep1(Qa, Qb); }
//@ predicate Qa(int value) = value == 0 ? true : a |-> 7;
//@ predicate Qb(int value) = value == 0 ? true : b |-> 8;

void sender()
    //@ requires a |-> _ &*& b |-> _ &*& Write(&c, Q);
    //@ ensures Write(&c, Q);
{
    a = 7;
    b = 8;
    //@ close Qa(1);
    //@ close Qb(1);
    //@ close sep1(Qa, Qb)(1);
    //@ close apply(Q,1)();
    //@ close exists(apply(Q,1));
    atomic_thread_fence(memory_order_release);
    atomic_store_explicit(&c, 1, memory_order_relaxed);
}

//@ fixpoint bool neq<t>(t x, t y) { return x != y; }

void receiver_a()
    //@ requires Read(&c, Qa);
    //@ ensures Read(&c, _) &*& a |-> 8;
{
    int result;
    for (;;)
        //@ invariant Read(&c, Qa);
    {
        //@ close exists<fixpoint(int, bool)>((neq)(0));
        result = atomic_load_explicit(&c, memory_order_relaxed);
        if (result) {
            break;
        }
    }
    //@ close exists(apply(Qa,result));
    atomic_thread_fence(memory_order_acquire);
    //@ open apply(Qa, result)();
    //@ open Qa(result);
    a++;
}

void receiver_b()
    //@ requires Read(&c, Qb);
    //@ ensures Read(&c, _) &*& b |-> 9;
{
    for (;;)
        //@ invariant Read(&c, Qb);
    {
        //@ close exists<fixpoint(int, bool)>((neq)(0));
        int result = atomic_load_explicit(&c, memory_order_acquire);
        if (result) {
            //@ open Qb(result);
            break;
        }
    }
    b++;
}


int main() //@ : main_full(message_passing)
    //@ requires module(message_passing, true);
    //@ ensures true;
{
    //@ open_module();
    //@ close Qa(0);
    //@ close Qb(0);
    //@ close sep1(Qa, Qb)(0);
    //@ convert_to_atomic(&c, Q);
    //@ split_Read(&c, Qa, Qb);
    sender();
    receiver_a();
    receiver_b();
    assert(a == 8);
    assert(b == 9);
    //@ leak Write(&c, _) &*& Read(&c, _) &*& Read(&c, _) &*& a |-> 8 &*& b |-> 9;
    return 0;
}
