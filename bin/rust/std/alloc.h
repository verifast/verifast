#include "../../stddef.h"
#include "../../stdint.h"

uint8_t *std_alloc_alloc(size_t size);
    //@ requires true;
    /*@
    ensures
        result == 0 ?
            emp
        :
            integers__(result, 1, false, size, _) &*& malloc_block(result, size) &*&
            object_pointer_within_limits(result, size) == true; // one-past-end does not overflow
    @*/
    //@ terminates;

struct std_tuple_0_ std_alloc_dealloc(uint8_t *p, size_t size);
    //@ requires malloc_block(p, size) &*& integers__(p, 1, false, size, _);
    //@ ensures true;
    //@ terminates;

union std_empty_ std_alloc_handle_alloc_error(size_t layout);
    //@ requires true;
    //@ ensures false;
    //@ terminates;
