
#include "stdlib.h"
#include <stdio.h>

struct struct_with_array
 {
  int x;
  int ar [55];
  int y;
 };

static int ar2 [55];

void mod_ar2 (void)
/*@ requires array<int>(&ar2, 55, 4, integer, ?elems)
    &*& nth (1, elems) >= 0 &*& nth (1, elems) <= 50
    &*& nth (26, elems) >= 0 &*& nth (26, elems) <= 50;
  @*/
/*@ ensures array<int>(&ar2, 55, 4, integer,
      update (1, nth (1, elems) + nth (26, elems), elems));
  @*/
 {
  ar2[ 1] = ar2[ 1] + ar2[26];
  return;
 }


int main(int argc, char **argv) //@ : main_full(static_array)
//@ requires module(static_array, true);
//@ ensures result == 0;
 {
//@ open_module();
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


  /* global array */
  ar2[ 0] = 1;
  ar2[ 1] = 5;
  ar2[ 2] = 0;
  ar2[26] = 2;
  mod_ar2 ();

  if (ar2[i] == 7)
   { t += ar2[2]; }
   else
   { t += ar2[0]; }

//@ leak array(&ar2, 55, 4, _, _);


  return (t);
 }

