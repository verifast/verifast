/*@
#define SOME_MACRO
@*/

void main()
//@ requires true;
//@ ensures true;
{
        int *ptr;
        #ifndef SOME_MACRO
                *ptr = 0; //~
        #endif
}