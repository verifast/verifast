#ifndef MOCKKERNELMODULE_PROXY_H
#define MOCKKERNELMODULE_PROXY_H

#include "libraries.h"
#include "MockKernel.h"

module_init_ *library_lookup_symbol_module_init(struct library *library);
    //@ requires [_]library(library, ?mainModule);
    //@ ensures [_]is_module_init_(result, mainModule);

#endif