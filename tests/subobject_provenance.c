#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

bool do_alias(int *x, int *y)
//@ requires true;
//@ ensures result == (x == y);
{
    if ((uintptr_t)x <= (uintptr_t)y)
        return (uintptr_t)y - (uintptr_t)x == 0;
    else
        return (uintptr_t)x - (uintptr_t)y == 0;
}

struct foo {
  int x[2];
  int y[2];
};

int main()
//@ requires true;
//@ ensures !result;
{
    struct foo f;
    //@ ints__to_chars_(&f.x[0]);
    if (fread(f.x, sizeof(int), 2, stdin) != 2) abort();
    //@ ints__to_chars_(&f.y[0]);
    if (fread(f.y, sizeof(int), 2, stdin) != 2) abort();
    bool b1 = do_alias(&f.x[2], &f.y[0]);
    bool b2 = &f.x[2] != &f.y[0];
    printf("%p %p %d %d\n", &f.x[2], &f.y[0], b1 ? 1 : 0, b2 ? 1 : 0);
    fwrite(f.x, sizeof(int), 2, stdout);
    fwrite(f.y, sizeof(int), 2, stdout);
    return b1 && b2 ? 1 : 0;
    //@ chars_to_ints(&f.x[0], 2);
    //@ chars_to_ints(&f.y[0], 2);
}

/*

This returns 0 on all platforms I tried. Current compilers
do not appear to exploit subobject provenance.

*/
