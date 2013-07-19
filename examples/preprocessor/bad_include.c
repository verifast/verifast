// Test that the result of an inclusion cannot depend upon the 
// current environment of defined macros.

/*~*/ /*@#define FOO false @*/

#include "bad_include.h"

void foo()
    //@ requires false;
    //@ ensures true; 
{
    void **p;
    *p = 0;
}
