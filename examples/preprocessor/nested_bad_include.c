// Test that the result of a nested inclusion cannot depend upon the 
// current environment of defined macros.

/*~*/ /*@#define FOO false@*/
#include "nested_bad_include2.h"

void foo()
    //@ requires false;
    //@ ensures true; 
{
    void **p;
    *p = 0;
}