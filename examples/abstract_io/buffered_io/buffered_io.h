#ifndef BUFFERED_IO_H
#define BUFFERED_IO_H

#include "beep.h"
#include "stdio.h"

int main();
    //@ requires token(?P0) &*& beep_(P0, ?P1) &*& putchar_(P1, 'h', ?P2) &*& putchar_(P2, 'i', ?P3) &*& flush_(P3, ?P4);
    //@ ensures token(P4);

#endif
