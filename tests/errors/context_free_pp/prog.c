#define PRE true
#include "lib.h"

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    foo();
    return 0;
}
