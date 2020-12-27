#include "stdlib.h"

int int_add(int x, int y)
    //@ requires true;
    //@ ensures result == x + y;
{
    //@ produce_limits(x);
    //@ produce_limits(y);
    if (0 <= x) {
        if (INT_MAX - x < y) abort();
    } else {
        if (y < INT_MIN - x) abort();
    }
    return x + y;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    int x = int_add(2000000000, 2000000000);
    assert false;
}
