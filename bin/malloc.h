#ifndef MALLOC_H
#define MALLOC_H

#include <stddef.h>

/*@

// In Standard C, freeing a null pointer is allowed and is a no-op.
lemma_auto void malloc_block_null();
    requires emp;
    ensures malloc_block(0, 0);

lemma void malloc_block_limits(void *array);
    requires [?f]malloc_block(array, ?size);
    ensures [f]malloc_block(array, size) &*& (void *)0 <= array &*& 0 <= size &*& array + size <= (void *)UINTPTR_MAX;

@*/

void *malloc(size_t size);
    //@ requires true;
    /*@
    ensures
        result == 0 ?
            emp
        :
            chars(result, size, ?cs) &*& malloc_block(result, size) &*&
            (char *)0 < result && result + size <= (char *)UINTPTR_MAX; // one-past-end does not overflow
    @*/

void free(void *array);
    //@ requires malloc_block(array, ?size) &*& chars(array, size, ?cs);
    //@ ensures emp;

#endif
