
#include "b.h"

#include "a.h"

//@ import_module a;

void b_init()
//@ requires module(b, true);
//@ ensures module(a, true);
{
  //@ open_module();
}