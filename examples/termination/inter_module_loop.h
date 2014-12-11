#ifndef INTER_MODULE_LOOP_H
#define INTER_MODULE_LOOP_H

int sqrt1(int x);
    //@ requires 0 <= x;
    //@ ensures result * result <= x && x < (result + 1) * (result + 1);
    //@ terminates;

int sqrt2(int x);
    //@ requires 0 <= x;
    //@ ensures result * result <= x && x < (result + 1) * (result + 1);
    //@ terminates;

#endif