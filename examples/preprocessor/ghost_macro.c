/*@
#define SOME_MACRO
@*/

int main()
//@ requires true;
//@ ensures true;
{
        int *ptr;
        #ifndef SOME_MACRO
                *ptr = 0; //~
        #endif
        return 0;
}
