#ifndef B_H
#define B_H

//@ require_module b;
//@ require_module a;

void b_init();
//@ requires module(b, true);
//@ ensures module(a, true);

#endif