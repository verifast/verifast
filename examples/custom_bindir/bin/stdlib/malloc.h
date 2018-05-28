#ifndef MALLOC_H
#define MALLOC_H

void *malloc(int size);
    //@ requires 0 <= size;
    /*@
    ensures
        result == 0 ?
            emp
        :
            custom_chars(result, size, ?cs) &*& malloc_block(result, size) &*&
            true == ((char *)0 < result && result + size <= (char *)UINTPTR_MAX); // one-past-end does not overflow
    @*/

void free(void *arr);
    //@ requires malloc_block(arr, ?size) &*& custom_chars(arr, size, ?cs);
    //@ ensures emp;

#endif
