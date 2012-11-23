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
            array<struct thread *>(threads, i, sizeof(struct thread *), pointer, ?ts)
            &*& foreach(ts, thread_info)
            &*& chars((void *)(threads + i), (n - i) * sizeof(struct thread *), _)
            &*& counting(integer, &cell, i, v);
        @*/
    {
        //@ chars_split((void *)(threads + i), 4);
        //@ chars_limits((void *)(threads + i));
        //@ chars_to_pointer(threads + i);
        //@ create_ticket(integer, &cell);
        //@ close thread_run_pre(m)(0, unit);
        struct thread *t = thread_start_joinable(m, 0);
        *(threads + i) = t;
        //@ close array<struct thread *>(threads + i + 1, 0, sizeof(struct thread *), pointer, nil);
        //@ close foreach(nil, thread_info);
        //@ close thread_info(t);
        //@ close foreach(cons(t, nil), thread_info);
        //@ close array<struct thread *>(threads + i, 1, sizeof(struct thread *), pointer, cons(t, nil));
        //@ foreach_append(ts, cons(t, nil));
        //@ array_merge(threads);
    }
    //@ open chars(_, _, _);
    
    //@ close chars((void *)threads, 0, nil);
    for (int i = 0; i < n; i++)
        /*@
        invariant
            chars((void *)threads, i * sizeof(struct thread *), _) &*&
            array<struct thread *>(threads + i, n - i, sizeof(struct thread *), pointer, ?ts)
            &*& foreach(ts, thread_info)
            &*& counting(integer, &cell, n - i, v);
        @*/
    {
        //@ open array(threads + i, _, _, _, _);
        //@ pointer_limits(threads + i);
        struct thread *t = *(threads + i);
        //@ open foreach(_, _);
        //@ open thread_info(t);
        thread_join(t);
        //@ open thread_run_post(m)(_, _);
        //@ destroy_ticket(integer, &cell);
        //@ pointer_to_chars(threads + i);
        //@ chars_join((void *)threads);
    }
    //@ open array(_, _, _, _, _);
    //@ open foreach(_, _);
    
    //@ stop_counting(integer, &cell);
    free((void *)threads);
}