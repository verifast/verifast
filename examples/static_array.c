#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include <stdbool.h>

//@ #include "arrays.gh"

void check (bool b)
  //@ requires b;
  //@ ensures true;
{
  assert(b);
}

typedef struct
 {
  int x;
  int ar [7];
  int y;
 } struct_with_array;

void check_local_inits(int x, int y)
  //@ requires y == 17;
  //@ ensures true;
{
  struct_with_array foo = {123, {2, x, 5, 7, 11, 13, y}, 456};
  struct_with_array bar = foo;
  char buf[3] = {1, 2, 3};
  
  check((&foo)->x == 123);
  check((&foo)->ar[6] == 17);
  check(buf[1] == 2);
}

//@ predicate struct_with_array(struct_with_array *s;) = s->x |-> _ &*& ints(s->ar, 7, _) &*& s->y |-> _;

struct mystruct {
  struct_with_array s1;
  int s2;
};

//@ predicate mystruct(struct mystruct *s;) = struct_with_array(&s->s1) &*& s->s2 |-> _;

struct mystruct my_global_nested_struct = {{42, {420, 421, 422, 423, 424, 425, 426}, -3}, -99};

static void foo()
  //@ requires mystruct(&my_global_nested_struct);
  //@ ensures mystruct(&my_global_nested_struct);
{
  struct mystruct my_local_nested_struct;
  //@ open_struct(&my_local_nested_struct);
  memset(&my_local_nested_struct, 0, sizeof(struct mystruct));
  //@ close_struct_zero(&my_local_nested_struct);
  
  //@ open_struct(&(&my_local_nested_struct)->s1);
  memset(&(&my_local_nested_struct)->s1, 0, sizeof(struct_with_array));
  //@ close_struct_zero(&(&my_local_nested_struct)->s1);
  
  //@ open mystruct(_);
  //@ open struct_with_array(_);
  assert(&my_global_nested_struct != &my_local_nested_struct);
  struct mystruct *sh = malloc(sizeof(struct mystruct));
  if (sh == 0) abort();
  assert(sh != &my_global_nested_struct);
  assert(sh != &my_local_nested_struct);
  (&(&my_global_nested_struct)->s1)->ar[5] = 100;
  (&(&my_local_nested_struct)->s1)->ar[5] = 200;
  //@ ints__split((&sh->s1)->ar, 5);
  (&sh->s1)->ar[5] = 300;
  //@ close ints_((&sh->s1)->ar + 5, 2, _);
  //@ ints__join((&sh->s1)->ar);
  free(sh);
}

static int ar2 [55];

void mod_ar2 (void)
/*@ requires ar2[0..55] |-> ?elems
    &*& nth (1, elems) >= 0 &*& nth (1, elems) <= 50
    &*& nth (26, elems) >= 0 &*& nth (26, elems) <= 50;
  @*/
/*@ ensures ar2[0..55] |-> update (1, nth (1, elems) + nth (26, elems), elems);
  @*/
 {
  ar2[ 1] = ar2[ 1] + ar2[26];
  return;
 }

static struct_with_array bigArray[10] = {{100, {1,2,3,4}, 200}, {300, {5,6,7}, 400}}; // Incomplete initializer lists; remaining elements get default value.

struct point { int x; int y; };

struct point points[] = { { 10, 20 }, { 30, 40 } };

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
  
  struct_with_array *bigArrayPtr = bigArray;
  check((bigArrayPtr + 1)->x == 300);
  check((bigArrayPtr + 1)->ar[2] == 7);
  
  foo();

  struct_with_array *s;
  int    i = 1;
  int    ar1 [55];
  int    t;

  /* normal array */
  //@ open ints_(ar1, _, _);
  ar1[ 0] = 1;
  //@ open ints_(ar1 + 1, _, _);
  ar1[ 1] = 5;
  //@ open ints_(ar1 + 2, _, _);
  ar1[ 2] = 0;
  //@ ints__split(ar1 + 3, 23);
  ar1[26] = 2;
  ar1[ 1] = ar1[ 1] + ar1[26];

  if (ar1[i] == 7)
   { t = ar1[2]; }
   else
   { assert false; }

  assert (ar1[26] == 2);
  
  //@ close ints_(ar1 + 26, 29, _);
  //@ ints__join(ar1 + 3);
  //@ close ints_(ar1 + 2, 53, _);
  //@ close ints_(ar1 + 1, 54, _);
  //@ close ints_(ar1, 55, _);

  /* array inside a struct */
  s = malloc (sizeof (struct_with_array));
  if (s == 0) { abort(); }

  //@ open ints_(s->ar, _, _);
  s->ar[ 0] = 1;
  //@ open ints_(s->ar + 1, _, _);
  s->ar[ 1] = 5;
  //@ open ints_(s->ar + 2, _, _);
  s->ar[ 2] = 0;
  //@ ints__split(s->ar + 3, 3);
  s->ar[ 6] = 2;
  s->ar[ 1] = s->ar[ 1] + s->ar[ 6];

  if (s->ar[i] == 7)
   { t += s->ar[2]; }
   else
   { assert false; }

  assert (s->ar[0] == 1);

  //@ close ints_(s->ar + 6, 1, _);
  //@ ints__join(s->ar + 3);
  //@ close ints_(s->ar + 2, 5, _);
  //@ close ints_(s->ar + 1, 6, _);
  //@ close ints_(s->ar, 7, _);
  free (s);


  /* global array */
  //@ assert ar2[0.._] |-> ?ar2Elems;
  //@ all_eq_nth(ar2Elems, 0, 0);
  check(ar2[0] == 0);
  ar2[ 0] = 1;
  ar2[ 1] = 5;
  ar2[ 2] = 0;
  ar2[26] = 2;
  mod_ar2 ();

  if (ar2[i] == 7)
   { t += ar2[2]; }
   else
   { assert false; }

  assert (ar2[1] == 7);

  assert (points[1].y == 40);
  
  //@ open_struct(points + 1);
  //@ chars__join((void *)(points + 1));
  //@ open_struct(points);
  //@ chars__join((void *)points);

  //@ open_struct(bigArrayPtr);
  //@ assert ((char *)(void *)bigArrayPtr)[..sizeof(struct_with_array)] |-> _;
  //@ open_struct(bigArrayPtr + 1);
  //@ assert chars_((void *)(bigArrayPtr + 1), sizeof(struct_with_array), _);
  //@ chars__join((void *)(bigArrayPtr + 1));
  //@ chars__join((void *)bigArrayPtr);
  //@ assert chars_((void *)bigArrayPtr, sizeof(struct_with_array) * 10, _);
  //@ close_module();
  //@ leak module(static_array, _);
  
  int xs[] = {1, 2, 3}, ys[] = {4, 5, 6, 7};
  xs[1] = xs[2];
  assert (xs[1] == 3);
  ys[2] = ys[3];
  assert (ys[2] == 7);

  return (t);
 }

