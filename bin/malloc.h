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
    ensures [f]malloc_block(array, size) &*& 0 <= size &*& pointer_within_limits(array) && pointer_within_limits(array + size);

@*/

void *malloc(size_t size);
    //@ requires true;
    /*@
    ensures
        result == 0 ?
            emp
        :
            chars_(result, size, _) &*& malloc_block(result, size) &*&
            object_pointer_within_limits(result, size) == true; // one-past-end does not overflow
    @*/
    //@ terminates;

void *calloc(size_t nmemb, size_t size);
    //@ requires true;
    /*@
    ensures
        result == 0 ?
            emp
        :
            chars(result, nmemb * size, ?cs) &*& malloc_block(result, nmemb * size) &*& all_eq(cs, 0) == true &*&
            (char *)0 < result && result + nmemb * size <= (char *)UINTPTR_MAX; // one-past-end does not overflow
    @*/
    //@ terminates;

void free(void *array);
    //@ requires malloc_block(array, ?size) &*& chars_(array, size, ?cs);
    //@ ensures emp;
    //@ terminates;

void *realloc(void *array, size_t newSize);
    //@ requires malloc_block(array, ?size) &*& chars(array, size, ?cs);
    /*@
    ensures
        result == 0 ?
            malloc_block(array, size) &*& chars(array, size, cs)
        :
            malloc_block(result, newSize) &*&
            newSize <= size ?
                chars(result, _, take(newSize, cs))
            :
                chars(result, _, cs) &*& chars(result + size, newSize - size, _);
    @*/
    //@ terminates;

#endif
