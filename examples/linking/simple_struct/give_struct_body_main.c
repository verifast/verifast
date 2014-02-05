#include "struct_nobody.h"

struct test
{
  int body;
};

int main() //@ : main
  //@ requires true;
  //@ ensures  true;
{
  struct test s;
  s.body = 0;
  return s.body;
}