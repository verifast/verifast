#ifndef MALLOC_H
#define MALLOC_H

/*@
predicate malloc_block(void *array; int size);

// In Standard C, freeing a null pointer is allowed and is a no-op.
lemma void malloc_block_null();
    requires emp;
    ensures malloc_block(0, 0);

// Notice that the value 4294967295 below should really be 4294967296.
// But we assume here that malloc never allocates the last byte of the address space.
lemma void malloc_block_limits(void *array);
    requires [?f]malloc_block(array, ?size);
    ensures [f]malloc_block(array, size) &*& true == ((void *)0 <= array) &*& 0 <= size &*& array + size <= (void *)4294967295;
@*/

void *malloc(int size);
    //@ requires 0 <= size;
    //@ ensures result == 0 ? emp : chars(result, ?cs) &*& malloc_block(result, size) &*& length(cs) == size;

void free(void *array);
    //@ requires malloc_block(array, ?size) &*& chars(array, ?cs) &*& length(cs) == size;
    //@ ensures emp;

#endif