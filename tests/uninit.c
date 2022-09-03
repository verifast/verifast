#include <stdlib.h>

int main()
//@ requires true;
//@ ensures true;
{
  char *p = malloc(1);
  if (p == 0) abort();
  char v = *p; //~ should_fail
}
