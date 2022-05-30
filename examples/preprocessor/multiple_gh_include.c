//@ #include "prelude_core.gh"
//@ #include "list.gh"
//@ #include "listex.gh"

/*@
#include "prelude_core.gh"
#include "list.gh"
#include "listex.gh"
@*/

int foo()
//@ requires true;
//@ ensures result == 42;
{
    return 42;
}