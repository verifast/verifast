#include <stdlib.h>

struct foo {
  int x;
  int y;
};

void calloc_test()
//@ requires true;
//@ ensures true;
{
  struct foo *f = calloc(1, sizeof(struct foo));
  if (f == 0) abort();
  assert(f->x == 0 && f->y == 0);
  free(f);
}

void uninit_raw()
//@ requires true;
//@ ensures true;
{
  char *p = malloc(1);
  if (p == 0) abort();
  char v = *p; //~ should_fail
}

void uninit_malloc_array()
//@ requires true;
//@ ensures true;
{
  int *xs = malloc(3 * sizeof(int));
  if (xs == 0) abort();
  int x0 = *xs; //~ should_fail
}

void uninit_local_array()
//@ requires true;
//@ ensures true;
{
  char buf[100];
  char c = *buf; //~ should_fail
}

void uninit_malloc_primitive()
//@ requires true;
//@ ensures true;
{
  int *px = malloc(sizeof(int));
  if (px == 0) abort();
  int x = *px; //~ should_fail
}
