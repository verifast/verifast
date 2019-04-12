#include "stdio.h"

int main(int argc, char **argv) //@ : main
    //@ requires 0 <= argc &*& [_]argv(argv, argc, _);
    //@ ensures true;
{
    for (int i = 0; i < argc; i++)
        //@ invariant 0 <= i &*& i <= argc &*& [_]argv(argv + i, argc - i, _);
    {
        //@ open argv(argv + i, argc - i, _);
        //@ pointer_limits(argv + i);
        puts(*(argv + i));
    }
    //@ open argv(_, 0, _);
    return 0;
}