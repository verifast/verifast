#include "zeroize.h"

void zeroize(char *buffer, int size)
{
  volatile unsigned char *p = (void*) buffer; 
  while(size--) *p++ = 0;
}