#ifndef A_H
#define A_H

//@ require_module a;

void a_init();
//@ requires module(a, true);
//@ ensures true;

#endif