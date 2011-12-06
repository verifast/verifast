#include "stdlib.h"
#include <stdio.h>

struct struct_with_array
 {
  int x;
  int ar [7];
  int y;
 };

//@ predicate struct_with_array(struct struct_with_array *s;) = s->x |-> _ &*& array<int>(&s->ar, 7, sizeof(int), integer, _) &*& s->y |-> _;

struct mystruct {
  struct struct_with_array s1;
  int s2;
};

//@ predicate mystruct(struct mystruct *s;) = struct_with_array(&s->s1) &*& s->s2 |-> _;

static struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

void foo()
  //@ requires mystruct(&my_global_nested_struct);
  //@ ensures mystruct(&my_global_nested_struct);
{
  struct mystruct my_local_nested_struct;
  //@ open mystruct(_);
  //@ open struct_with_array(_);
  assert(&my_global_nested_struct != &my_local_nested_struct);
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0) abort();
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;
  (&sh->s1)->ar[5] = 300;
  free(sh);
}

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

void check (bool b)
  //@ requires b;
  //@ ensures true;
{
  assert(b);
}

int main(int argc, char **argv) //@ : main_full(static_array)
//@ requires module(static_array, true);
//@ ensures result == 0;
 {
  //@ open_module();
  check((&(&my_global_nested_struct)->s1)->x == 42);
  check((&(&my_global_nested_struct)->s1)->ar[0] == 420);
  check((&(&my_global_nested_struct)->s1)->ar[6] == 426);
  check((&(&my_global_nested_struct)->s1)->y == -3);
  check((&my_global_nested_struct)->s2 == -99);
  
  foo();

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
  s->ar[ 6] = 2;
  s->ar[ 1] = s->ar[ 1] + s->ar[ 6];

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

  //@ close_module();
  //@ leak module(static_array, _);

  return (t);
 }

