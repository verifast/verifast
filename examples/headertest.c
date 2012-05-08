#include "headertest/foo.h"

int main()
    //@ requires true;
    //@ ensures true;
{
    foo();
    bar();
    return 0;
}