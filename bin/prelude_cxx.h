#ifndef PRELUDE_CXX_H
#define PRELUDE_CXX_H

#include "prelude.h"
#include "typeinfo.h"

/*@

predicate new_block(void *p; int size);
predicate new_block_chars(char *p; int count) = new_block(p, count);
predicate new_block_uchars(unsigned char *p; int count) = new_block(p, count);
predicate new_block_ints(int *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(int), count, 0);
predicate new_block_uints(unsigned int *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(unsigned int), count, 0);
predicate new_block_shorts(short *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(short), count, 0);
predicate new_block_ushorts(unsigned short *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(unsigned short), count, 0);
predicate new_block_pointers(void **p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(void *), count, 0);
predicate new_block_intptrs(intptr_t *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(intptr_t), count, 0);
predicate new_block_uintptrs(uintptr_t *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(uintptr_t), count, 0);
predicate new_block_longs(long *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(long), count, 0);
predicate new_block_ulongs(unsigned long *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(unsigned long), count, 0);
predicate new_block_llongs(long long *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(long long), count, 0);
predicate new_block_ullongs(unsigned long long *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(unsigned long long), count, 0);
predicate new_block_bools(bool *p; int count) =  new_block(p, ?size) &*& [_]divrem(size, sizeof(bool), count, 0);
predicate new_block_floats(float *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(float), count, 0);
predicate new_block_doubles(double *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(double), count, 0);
predicate new_block_long_doubles(long double *p; int count) = new_block(p, ?size) &*& [_]divrem(size, sizeof(long double), count, 0);

@*/

#endif
