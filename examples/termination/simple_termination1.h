#ifndef SIMPLE_TERMINATION1
#define SIMPLE_TERMINATION1

void foo();
    //@ requires true;
    //@ ensures true;
    //@ terminates;

void bar();
    //@ requires true;
    //@ ensures true;
    //@ terminates;

#endif