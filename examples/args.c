#include "stdio.h"

/*@

lemma void pointer_is_in_range(void **p);
    requires [?f]pointer(p, ?v);
    ensures [f]pointer(p, v) &*& (void **)0 <= p &*& p <= (void **)4294967295;
@*/

int main0(int argc, char **argv)
    //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
    //@ ensures true;
{
    for (int i = 0; i<argc; i++)
        //@ invariant 0 <= i &*& i <= argc &*& [_]argv(argv + i, argc - i, _);
    {
        //@ open argv(argv + i, argc - i, _);
        //@ pointer_is_in_range(argv + i);
        puts(*(argv + i));
    }
    //@ open argv(_, 0, _);
    return 0;
}