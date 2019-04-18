#ifndef STDLIB_H
#define STDLIB_H

#include <stdbool.h>
#include <malloc.h>

void abort();
    //@ requires true;
    //@ ensures false;
    //@ terminates;

void exit(int status);
    //@ requires true;
    //@ ensures false;
    //@ terminates;

int abs(int x);
    //@ requires INT_MIN < x;
    //@ ensures result == abs(x);
    //@ terminates;

long labs(long x);
    //@ requires LONG_MIN < x;
    //@ ensures result == abs(x);
    //@ terminates;

long long llabs(long long x);
    //@ requires LLONG_MIN < x;
    //@ ensures result == abs(x);
    //@ terminates;

#endif
