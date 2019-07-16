#include <stdnoreturn.h>
#include <stdlib.h>

noreturn void fail()
{
    abort();
}

noreturn void fail2()
    //@ requires true;
    //@ ensures false;
{
    abort();
}

noreturn void fail3()
    //@ requires false;
    //@ ensures true;
{
}

noreturn void fail4() //~ should_fail
    //@ requires true;
    //@ ensures true;
{
}
