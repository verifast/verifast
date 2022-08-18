#include <stdlib.h>

void foo(long count, unsigned long foo, size_t mySize)
  //@requires true;
  //@ensures true;
{
  long *ptr = &count;
  unsigned long *pfoo = &foo;
  size_t *pmySize = &mySize;
}
