#ifndef LIB_H
#define LIB_H

#include <stdint.h>

void foo();
    /*~ should_fail */ //@ requires PRE;
    //@ ensures true;

#endif LIB_H
