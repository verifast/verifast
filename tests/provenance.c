#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

bool do_alias(int *x, int *y)
//@ requires true;
//@ ensures result == (x == y); //~should_fail
{
    if ((uintptr_t)x <= (uintptr_t)y)
        return (uintptr_t)y - (uintptr_t)x == 0;
    else
        return (uintptr_t)x - (uintptr_t)y == 0; //~allow_dead_code
}

int main()
//@ requires true;
//@ ensures !result;
{
    int y[2];
    int x[2];
    //@ ints__to_chars_(&x[0]);
    if (fread(x, sizeof(int), 2, stdin) != 2) abort();
    //@ ints__to_chars_(&y[0]);
    if (fread(y, sizeof(int), 2, stdin) != 2) abort();
    bool b1 = do_alias(&x[2], &y[0]);
    bool b2 = &x[2] != &y[0];
    printf("%p %p %d %d\n", &x[2], &y[0], b1 ? 1 : 0, b2 ? 1 : 0);
    fwrite(x, sizeof(int), 2, stdout);
    fwrite(y, sizeof(int), 2, stdout);
    return b1 && b2 ? 1 : 0;
    //@ chars_to_ints(&x[0], 2);
    //@ chars_to_ints(&y[0], 2);
}

/*

# gcc --version
gcc (GCC) 12.2.0
# gcc -o provenance -O0 provenance.c
# echo 0123456789abcdef | ./provenance
0x7ffdc2207f44 0x7ffdc2207f44 1 1
# echo $?
1

*/
