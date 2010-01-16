#include "assert.h"

void test(int i)
    //@ requires true;
    //@ ensures true;
{
    int j = 0;
    switch (i) {
    }
    assert(false); //~ should_fail
}

void break_test(int *i1, int *i2)
    //@ requires integer(i1, _) &*& integer(i2, _);
    //@ ensures integer(i1, _) &*& integer(i2, _);
{
    while (true)
        //@ invariant integer(i1, _);
    {
        break;
    }
    assert(false); //~ should_fail
}

void fall_through_test(int i)
    //@ requires true;
    //@ ensures true;
{
    int j = 0;
    switch (i) {
        case 1:
            j = 1;
        case 2:
            assert j == 0; //~ should_fail
    }
}