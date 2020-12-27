#include "stdlib.h"

struct foo {
    int x;
    //@ int y;
};

int main()
    //@ requires true;
    //@ ensures true;
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0) abort();
    f->x = 5;
    //@ f->y = 6;
    //@ assert f->x |-> 5 &*& f->y |-> 6;
    free(f);
    //@ f->y = 7; //~ should fail
    //return 0;
}

int foo()
    //@ requires true;
    //@ ensures true;
{
    struct foo *f = malloc(sizeof(struct foo));
    if (f == 0) abort();
    f->x = 5;
    //@ f->y = 6;
    //@ assert f->x |-> 5 &*& f->y |-> 6;
    //@ f->x = 10; //~ should fail
    //free(f);
    //return 0;
}