#include "a.h"

#include "b.h"

//@ import_module b;

static int x;

void a_init()
//@ requires module(a, true);
//@ ensures true;
{
  //@ open_module();
  b_init();
  //@ open_module();
  b_init();
  //Fail: we obtain multiple chunks for the same variable x!
  
  //@ leak module(a, _);
  //@ leak integer(&x, _);
  //@ leak integer(&x, _);
}


int main() //@ : main_full(a)
//@ requires module(a, true);
//@ ensures true;
{
  a_init();
  return 0;
}
