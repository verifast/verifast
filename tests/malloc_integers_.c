#include <stdlib.h>
#include <stdint.h>

int32_t *calloc_int32_t_wrapper(size_t n)
//@ requires true;
//@ ensures result == 0 ? true : result[..n] |-> ?_ &*& malloc_block_integers_(result, 4, true, n);
{
  return calloc(n, sizeof(int32_t));
}

int32_t *malloc_int32_t_wrapper(size_t n)
//@ requires n * 4 <= UINTPTR_MAX;
//@ ensures result == 0 ? true : result[..n] |-> _ &*& malloc_block_integers_(result, 4, true, n);
{
  return malloc(n * sizeof(int32_t));
}