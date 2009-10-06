#include "libraries.h"
#include "MockKernel.h"
#include "MockKernelModule_proxy.h"

module_init_ *library_lookup_symbol_module_init(struct library *library)
{
    return library_lookup_symbol(library, "module_init");
}