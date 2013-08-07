#include "headertest/foo.h"
#include "baz.h"

int main()
    //@ requires true;
    //@ ensures true;
{
    foo();
    bar();
    baz();
    return 0;
}
