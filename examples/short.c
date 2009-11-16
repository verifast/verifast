#include "stdlib.h"

struct myStruct {
  int i;
  short s;
  char c;
};

void m(int i, short s, char c)
  //@ requires 0 <= i && i < 10000;
  //@ ensures true;
{
  short r = 354;
  int j = s;
  r = (short) i;
  struct myStruct* ms = malloc(sizeof(struct myStruct));
  if(ms == 0) abort();
  ms->i = i;
  ms->s = ms->c;
  free(ms);
}