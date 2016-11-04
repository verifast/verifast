#include "../annotated_api/general_definitions/zeroize.h"

void zeroize(char *buffer, int size)
{
  volatile unsigned char *p = (void*) buffer; 
  while(size--) *p++ = 0;
}