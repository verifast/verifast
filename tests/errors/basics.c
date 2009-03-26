#include "stdlib.h"

void foo1()
    //@ requires true;
    //@ ensures false; //~ should fail
{
}

void foo2()
    //@ requires true;
    //@ ensures true;
{
    int *test = 0;
    *test = 5;  //~ should fail
}

struct cell {
    int value;
};

void foo3()
    //@ requires true;
    //@ ensures true;
{
    struct cell *c = 0;
    c->value = 42; //~ should fail
}

struct cell *foo4()
    //@ requires true;
    //@ ensures result->value |-> _; //~ should fail
{
    return 0;
}

void foo5()
    //@ requires true;
    //@ ensures true;
{
    struct cell *c = malloc(sizeof(struct cell));
    if (c == 0) { abort(); }
    free(c);
    c->value = 52; //~ should fail
}

void foo6(struct cell *c)
    //@ requires c->value |-> _;
    //@ ensures true;
{
    c = 0;
    c->value = 99; //~ should fail
}

void foo7(struct cell *c)
    //@ requires c->value |-> _;
    /*@
    ensures
        c->value |-> _
        &*&
        c->value |-> _;  //~ should fail
    @*/
{
}

void foo8(struct cell *c)
    //@ requires c == 0 ? true : c->value |-> _;
    //@ ensures c->value |-> _; //~ should fail
{
}

int foo9(struct cell *c)
    //@ requires true;
    //@ ensures true;
{
    return c->value;  //~ should fail
}

struct node {
    struct node *next;
};

struct node *foo10(struct node *n)
    //@ requires n->next |-> _;
    //@ ensures true;
{
    return n->next->next;  //~ should fail
}
