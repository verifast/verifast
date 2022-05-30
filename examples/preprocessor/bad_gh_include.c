// Test that the result of an inclusion cannot depend upon the 
// current environment of defined macros.

/*@
#define BAR true
@*/

/*@
#define FOO true
#include "bad_include.gh"
@*/

int bar()
//@ requires BAR;
//@ ensures foo();
{
    return 0;
}