#ifndef FOO_H
#define FOO_H

#include "subdir/bar.h"
#include "../headertest/subdir/bar.h"

void foo();
    //@ requires true;
    //@ ensures true;

#endif