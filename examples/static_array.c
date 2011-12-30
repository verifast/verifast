#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#include "bool.h"

//@ #include "arrays.h"

void check (bool b)
  //@ requires b;
  //@ ensures true;
{
  assert(b);
}

struct struct_with_array
 {
  int x;
  int ar [7];
  int y;
 };

void check_local_inits()
  //@ requires true;
  //@ ensures true;
{
  struct struct_with_array foo = {123, {2, 3, 5, 7, 11, 13, 17}, 456};
  char buf[3] = {1, 2, 3};
  
  check((&foo)->x == 123);
  check((&foo)->ar[6] == 17);
  check(buf[1] == 2);
}

//@ predicate struct_with_array(struct struct_with_array *s;) = s->x |-> _ &*& array<int>(&s->ar, 7, sizeof(int), integer, _) &*& s->y |-> _;

struct mystruct {
  struct struct_with_array s1;
  int s2;
};

//@ predicate mystruct(struct mystruct *s;) = struct_with_array(&s->s1) &*& s->s2 |-> _;

struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

static void foo()
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

static struct struct_with_array bigArray[10] = {{100, {1,2,3,4}, 200}, {300, {5,6,7}, 400}}; // Incomplete initializer lists; remaining elements get default value.

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
  
  struct struct_with_array *bigArrayPtr = bigArray;
  //@ open [1/2]struct_with_array_x(bigArrayPtr + 1, 300);
  //@ integer_to_chars((void *)(bigArrayPtr + 1));
  //@ chars_limits((void *)(bigArrayPtr + 1));
  //@ chars_to_integer((void *)(bigArrayPtr + 1));
  //@ close [1/2]struct_with_array_x(bigArrayPtr + 1, _);
  check((bigArrayPtr + 1)->x == 300);
  check((bigArrayPtr + 1)->ar[2] == 7);
  
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

  assert (ar1[26] == 2);

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

  assert (s->ar[0] == 1);

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

  assert (ar2[1] == 7);

  //@ open_struct(bigArrayPtr);
  //@ assert chars((void *)bigArrayPtr, ?cs) &*& length(cs) == sizeof(struct struct_with_array);
  //@ chars_to_char_array(bigArrayPtr);
  //@ open_struct(bigArrayPtr + 1);
  //@ assert chars((void *)(bigArrayPtr + 1), ?cs2) &*& length(cs2) == sizeof(struct struct_with_array);
  //@ chars_to_char_array(bigArrayPtr + 1);
  //@ array_merge(bigArrayPtr + 1);
  //@ array_merge(bigArrayPtr);
  //@ assert array<char>((void *)bigArrayPtr, sizeof(struct struct_with_array) * 10, 1, character, _);
  //@ close_module();
  //@ leak module(static_array, _);

  return (t);
 }

