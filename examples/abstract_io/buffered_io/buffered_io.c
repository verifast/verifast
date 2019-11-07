#include "buffered_io.h"

int main() //@ : custom_main_spec
    //@ requires token(?P0) &*& beep_(P0, ?P1) &*& putchar_(P1, 'h', ?P2) &*& putchar_(P2, 'i', ?P3) &*& flush_(P3, ?P4);
    //@ ensures token(P4);
{
    beep();
    putchar('h');
    putchar('i');
    flush();
    return 0;
}
