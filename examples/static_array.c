
#include "stdlib.h"
#include <stdio.h>

int main(int argc, char **argv)
//@ requires 0 <= argc &*& [_]char_array(argv, argc);
//@ ensures result == 0;
 {
  int   i = 1;
  int   ar1 [55];
  int   t;

  ar1[ 0] = 1;
  ar1[ 1] = 5;
  ar1[ 2] = 0;
  ar1[26] = 2;
  ar1[ 1] = ar1[ 1] + ar1[26];

  if (ar1[i] == 7)
   { printf ("%i", i); t = ar1[2]; }
   else
   { printf ("%i", i); t = ar1[0]; }

  return (t);
 }

