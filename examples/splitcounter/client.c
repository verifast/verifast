// A minimal client for splitcounter.c, only intended to show that the specs are minimally usable.

#include <assert.h>
#include "splitcounter.h"

struct gvar {
  //@ int x;
};

int main() //@ : main
//@ requires true;
//@ ensures true;
{
    struct gvar g;
    //@ g.x = 0;
    {
        /*@
        predicate inv(; int x) = [1/2]g.x |-> x;
        @*/
        //@ close inv(0);
        //@ close exists<predicate(int)>(inv);
        struct counter *c = create_counter();
        {
            /*@
            predicate pre(;) = [1/2]g.x |-> 0;
            predicate post(;) = [1/2]g.x |-> 1;
            @*/
            //@ produce_lemma_function_pointer_chunk incr_ghop(inv, pre, post)() { open inv(_); open pre(); g.x++; close post(); close inv(1); };
            //@ close pre();
            incr_left(c);
            //@ open post();
            //@ leak is_incr_ghop(_, _, _, _);
        }
        {
            /*@
            predicate pre(;) = [1/2]g.x |-> 1;
            predicate post(;) = [1/2]g.x |-> 2;
            @*/
            //@ produce_lemma_function_pointer_chunk incr_ghop(inv, pre, post)() { open inv(_); open pre(); g.x++; close post(); close inv(2); };
            //@ close pre();
            incr_right(c);
            //@ open post();
            //@ leak is_incr_ghop(_, _, _, _);
        }
        long long v;
        {
            /*@
            predicate pre(;) = [1/2]g.x |-> 2;
            predicate post(; int value) = [1/2]g.x |-> 2 &*& value == 2;
            @*/
            //@ produce_lemma_function_pointer_chunk read_ghop(inv, pre, post)() { open inv(_); open pre(); close post(2); close inv(2); };
            //@ close pre();
            v = read(c);
            //@ open post(v);
        }
        assert(v == 2);
        dispose_counter(c);
        //@ open inv(_);
        return 0;
    }
}
