#ifndef TERMINATION_ERRORS_H
#define TERMINATION_ERRORS_H

void should_terminate();
    //@ requires true;
    //@ ensures true;
    //@ terminates;

#endif