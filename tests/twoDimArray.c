#include <stdio.h>
//@ #include <arrays.gh>

void printMatrix(int m[2][3])
//@ requires m[0..2][0..3] |-> ?elems;
//@ ensures m[0..2][0..3] |-> elems;
{
    for(unsigned int r = 0; r < 2; r++)
    //@ invariant m[0..2][0..3] |-> elems;
    {
        for(unsigned int c = 0; c < 3; c++)
        //@ invariant m[0..2][0..3] |-> elems;
        {
            //@ ints_split(m, r * 3);
            //@ ints_split(m + r, 3);
            //@ integer_limits(m + r);
            //@ close ints(m + r, 3, _);
            printf("%i ", m[r][c]);
            //@ ints_join(m + r);
            //@ ints_join(m);
        }
        printf("\n");
    }
    printf("\n");
}

int main()
//@ requires true;
//@ ensures true;
{
    int m[2][3] =
    {
        { 1, 2, 3 },
        { 4, 5, 6 }
    };
    
    //@ ints_join(m);
    
    printMatrix(m);
    
    //@ ints_to_chars(m);

    return 0;
}
