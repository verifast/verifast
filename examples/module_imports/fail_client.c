#include "stdlib.h"

#include "mymodule.h"

#include "mysubmodule.h"

//@ import_module mymodule;
//@ import_module mysubmodule;

int main() //@ : main_full(fail_client)
//@ requires module(fail_client, true);
//@ ensures true;
{
  //@ open_module();
  mymodule_init();
  mysubmodule_init();
  mymodule_set(50);
  int x = mymodule_get();
  //@ assert x == 50;
  mysubmodule_destroy();
  mymodule_destroy();
  //@ close_module();
  //@ leak module(fail_client, _);
  return 0;
}

