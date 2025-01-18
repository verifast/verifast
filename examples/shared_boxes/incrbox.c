#include <threading.h>
#include "atomics.h"

/*@

box_class incr_box(int *x) {
    invariant *x |-> ?value;
    
    action increase();
        requires true;
        ensures old_value <= value;
    
    handle_predicate observed(int v) {
        invariant v <= value;
    
        preserved_by increase() {}
    }
}

@*/

//@ predicate_family_instance thread_run_data(inc)(int* x) = [_]incr_box(_, x);

void inc(int *x) //@ : thread_run
    //@ requires thread_run_data(inc)(x);
    //@ ensures true;
{
    //@ open thread_run_data(inc)(x);
    while(true)
        //@ invariant [_]incr_box(_, x);
    {
        ;
        /*@
        consuming_box_predicate incr_box(_, x)
        perform_action increase()
        {
            @*/ atomic_increment(x); /*@
        };
        @*/
    }
}

void reader(int *x)
    //@ requires [_]incr_box(_, x);
    //@ ensures false;
{
    for (;;)
        //@ invariant [_]incr_box(_, x);
    {
        ;
        /*@
        consuming_box_predicate incr_box(_, x)
        perform_action increase()
        {
            @*/ int m0 = atomic_load_int(x); /*@
        }
        producing_fresh_handle_predicate observed(m0);
        @*/
        /*@
        consuming_box_predicate incr_box(_, x)
        consuming_handle_predicate observed(_, m0)
        perform_action increase()
        {
            @*/ int m1 = atomic_load_int(x); /*@
        };
        @*/
        assert(m0 <= m1);
    }
}

int main()
    //@ requires true;
    //@ ensures true;
{
    int x = 0;
    //@ create_box id = incr_box(&x);
    //@ leak incr_box(id, &x);
    //@ close thread_run_data(inc)(&x);
    thread_start(inc, &x);
    reader(&x);
}