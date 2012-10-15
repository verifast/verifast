#include "stdlib.h"

#include "mymodule.h"

//@ import_module mymodule;

int main() //@ : main_full(client)
//@ requires module(client, true);
//@ ensures true;
{
  //@ open_module();
  mymodule_init();
  mymodule_set(50);
  int x = mymodule_get();
  //@ assert x == 50;
  mymodule_destroy();
  //@ close_module();
  //@ leak module(client, _);
  return 0;
}

