#include "stdlib.h"
#include "stdint.h"

/* ========================================================================== */
/* Positive Verified Memory & Pointer Functions                               */
/* ========================================================================== */

int safe_pointer_read(int *p)
//@ requires integer(p, ?v);
//@ ensures integer(p, v) &*& result == v;
{
    return *p;
}

void safe_pointer_write(int *p, int new_val)
//@ requires integer(p, _);
//@ ensures integer(p, new_val);
{
    *p = new_val;
}

void safe_heap_alloc_free()
//@ requires true;
//@ ensures true;
{
    int *p = malloc(sizeof(int));
    if (p == 0) abort();
    *p = 42;
    free(p);
}

int safe_array_read(int *arr, int i, int n)
//@ requires ints(arr, n, ?vs) &*& 0 <= i && i < n;
//@ ensures ints(arr, n, vs);
{
    return arr[i];
}

void safe_stack_address()
//@ requires true;
//@ ensures true;
{
    int x = 10;
    int *p = &x;
    *p = 20;
    //@ assert x == 20;
}

/* ========================================================================== */
/* Negative Soundness Tests (14 Should-Fail Cases)                            */
/* ========================================================================== */

/* 1. Dereferencing NULL pointer for write */
void neg_null_deref_write()
//@ requires true;
//@ ensures true;
{
    int *p = 0;
    *p = 42; //~ should_fail
}

/* 2. Dereferencing NULL pointer for read */
int neg_null_deref_read()
//@ requires true;
//@ ensures true;
{
    int *p = 0;
    return *p; //~ should_fail
}

/* 3. Dereferencing arbitrary unallocated pointer */
void neg_unallocated_deref(int *p)
//@ requires true;
//@ ensures true;
{
    *p = 99; //~ should_fail
}

/* 4. Array out-of-bounds write (index == length) */
void neg_oob_array_write(int *arr, int n)
//@ requires ints(arr, n, ?vs) &*& 0 <= n;
//@ ensures ints(arr, n, vs);
{
    arr[n] = 42; //~ should_fail
}

/* 5. Array out-of-bounds read (index == length) */
int neg_oob_array_read(int *arr, int n)
//@ requires ints(arr, n, ?vs) &*& 0 <= n;
//@ ensures ints(arr, n, vs);
{
    return arr[n]; //~ should_fail
}

/* 6. Array negative index read */
int neg_array_negative_index(int *arr, int n)
//@ requires ints(arr, n, ?vs) &*& 0 < n;
//@ ensures ints(arr, n, vs);
{
    return arr[-1]; //~ should_fail
}

/* 7. Use-after-free */
void neg_use_after_free()
//@ requires true;
//@ ensures true;
{
    int *p = malloc(sizeof(int));
    if (p == 0) abort();
    *p = 10;
    free(p);
    *p = 20; //~ should_fail
}

/* 8. Double free */
void neg_double_free()
//@ requires true;
//@ ensures true;
{
    int *p = malloc(sizeof(int));
    if (p == 0) abort();
    free(p);
    free(p); //~ should_fail
}

/* 9. Free non-heap (stack) address */
void neg_free_stack_address()
//@ requires true;
//@ ensures true;
{
    int x = 42;
    free(&x); //~ should_fail
}

/* 10. Memory leak when postcondition specifies emp */
void neg_memory_leak()
//@ requires true;
//@ ensures emp;
{
    int *p = malloc(sizeof(int));
    if (p == 0) abort();
    *p = 42;
} //~ should_fail

/* 11. Reading uninitialized stack variable whose address was taken */
int neg_uninit_stack_read()
//@ requires true;
//@ ensures true;
{
    int x;
    int *p = &x;
    return *p; //~ should_fail
}

/* 12. Pointer arithmetic underflow past array allocation */
void neg_pointer_arith_underflow()
//@ requires true;
//@ ensures true;
{
    char foo[2];
    char *pfoo = foo;
    char *bad_null = pfoo - (uintptr_t)pfoo; //~ should_fail
}

/* 13. Subscript address arithmetic overflow past UINTPTR_MAX */
void neg_pointer_subscript_overflow()
//@ requires true;
//@ ensures true;
{
    char foo[2];
    char *pfoo = foo;
    char *bad_ptr = &pfoo[UINTPTR_MAX]; //~ should_fail
}

/* 14. Pointer aliasing violation: fabricating second chunk for same location */
void neg_aliasing_fabrication(int *p)
//@ requires integer(p, 10);
//@ ensures integer(p, 10) &*& integer(p, 20); //~ should_fail
{
}
