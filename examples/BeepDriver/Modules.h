#ifndef MODULES_H
#define MODULES_H

#include "BeepKernel.h"

struct module;

//@ predicate kernel_module(struct module *m);

struct module *load_module(char *name);
    //@ requires kernel_state() &*& [?f]chars(name, ?n, ?cs) &*& mem('\0', cs) == true;
    //@ ensures kernel_state() &*& [f]chars(name, n, cs) &*& kernel_module(result);

void unload_module(struct module *m);
    //@ requires kernel_state() &*& kernel_module(m);
    //@ ensures kernel_state();

#endif