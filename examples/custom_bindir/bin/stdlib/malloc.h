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

void free(void *array);
    //@ requires malloc_block(array, ?size) &*& custom_chars(array, size, ?cs);
    //@ ensures emp;

#endif
