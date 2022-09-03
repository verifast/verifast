//@ #include "arrays.gh"
//@ #include "counting.gh"
#include "malloc.h"
#include "stdlib.h"
#include "threading.h"

static int cell;

/*@

predicate_family_instance thread_run_pre(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& [frac]integer(&cell, _);
predicate_family_instance thread_run_post(m)(void *data, any info) = ticket(integer, &cell, ?frac) &*& [frac]integer(&cell, _);

predicate thread_info(struct thread *t) = thread(t, m, _, _);

@*/

void m(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(m)(data, ?info);
    //@ ensures thread_run_post(m)(data, info);
{
    //@ open thread_run_pre(m)(_, _);
    int x = cell;
    //@ close thread_run_post(m)(data, info);
}

void process(int n)
    //@ requires integer(&cell, ?v) &*& 0 <= n &*& n * sizeof(struct thread *) <= INT_MAX;
    //@ ensures integer(&cell, v);
{
    //@ start_counting(integer, &cell);
    struct thread **threads = malloc(n * sizeof(struct thread *));
    if (threads == 0) abort();
    //@ close foreach(nil, thread_info);
    for (int i = 0; i < n; i++)
        /*@
        invariant
            threads[0..i] |-> ?ts
            &*& foreach(ts, thread_info)
            &*& threads[i..n] |-> _
            &*& counting(integer, &cell, i, v);
        @*/
    {
        //@ create_ticket(integer, &cell);
        //@ close thread_run_pre(m)(0, unit);
        struct thread *t = thread_start_joinable(m, 0);
        *(threads + i) = t;
        //@ close foreach(nil, thread_info);
        //@ close thread_info(t);
        //@ close foreach(cons(t, nil), thread_info);
        //@ close pointers(threads + i, 1, _);
        //@ foreach_append(ts, cons(t, nil));
        //@ pointers_join(threads);
    }
    
    for (int i = 0; i < n; i++)
        /*@
        invariant
            threads[0..i] |-> _ &*&
            threads[i..n] |-> ?ts
            &*& foreach(ts, thread_info)
            &*& counting(integer, &cell, n - i, v);
        @*/
    {
        //@ pointer_limits(threads + i);
        struct thread *t = *(threads + i);
        //@ open foreach(_, _);
        //@ open thread_info(t);
        thread_join(t);
        //@ open thread_run_post(m)(_, _);
        //@ destroy_ticket(integer, &cell);
        //@ close pointers_(threads + i, 1, _);
        //@ pointers__join(threads);
    }
    //@ open foreach(_, _);
    
    //@ stop_counting(integer, &cell);
    free(threads);
}