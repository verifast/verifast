
#include "stdlib.h"
#include <stdio.h>

struct struct_with_array
 {
  int x;
  int ar [55];
  int y;
 };

int main(int argc, char **argv)
//@ requires 0 <= argc &*& [_]char_array(argv, argc);
//@ ensures result == 0;
 {
  struct struct_with_array *s;
  int    i = 1;
  int    ar1 [55];
  int    t;

  /* normal array */
  ar1[ 0] = 1;
  ar1[ 1] = 5;
  ar1[ 2] = 0;
  ar1[26] = 2;
  ar1[ 1] = ar1[ 1] + ar1[26];

  if (ar1[i] == 7)
   { t = ar1[2]; }
   else
   { t = ar1[0]; }


  /* array inside a struct */
  s = malloc (sizeof (struct struct_with_array));
  if (s == 0) { abort(); }

  s->ar[ 0] = 1;
  s->ar[ 1] = 5;
  s->ar[ 2] = 0;
  s->ar[26] = 2;
  s->ar[ 1] = s->ar[ 1] + s->ar[26];

  if (s->ar[i] == 7)
   { t += s->ar[2]; }
   else
   { t += s->ar[0]; }

  free (s);


  return (t);
 }

