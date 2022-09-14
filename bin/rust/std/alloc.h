#include "../../stddef.h"

unsigned char *std_alloc_alloc(size_t size);
    //@ requires true;
    /*@
    ensures
        result == 0 ?
            emp
        :
            malloc_block(result, size) &*& uchars(result, size, ?cs) &*&
            (unsigned char *)0 < result && result + size <= (unsigned char *)UINTPTR_MAX; // one-past-end does not overflow
    @*/
    //@ terminates;

struct std_tuple_0_ std_alloc_dealloc(unsigned char *p, size_t size);
    //@ requires malloc_block(p, size) &*& uchars(p, size, _);
    //@ ensures true;
    //@ terminates;
