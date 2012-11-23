#include "stdlib.h"
#include "Modules.h"
#include "libraries.h"
#include "BeepDriver_proxy.h"

struct module {
    struct library *library;
    module_dispose *dispose;
};

/*@

predicate kernel_module(struct module *m) =
    malloc_block_module(m) &*&
    m->library |-> ?library &*& library(library, ?mod) &*&
    m->dispose |-> ?dispose &*& [_]is_module_dispose(dispose, mod, ?p) &*& p();

@*/

struct module *load_module(char *name)
    //@ requires kernel_state() &*& [?f]string(name, ?cs);
    //@ ensures kernel_state() &*& [f]string(name, cs) &*& kernel_module(result);
{
    struct library *lib = load_library(name);
    module_init *init = 0;
    module_dispose *dispose = 0;
    struct module *m;
    if (lib == 0) abort();
    init = library_lookup_symbol_module_init_func(lib);
    if (init == 0) abort();
    dispose = init();
    m = malloc(sizeof(struct module));
    if (m == 0) abort();
    m->library = lib;
    m->dispose = dispose;
    //@ close kernel_module(m);
    return m;
}

void unload_module(struct module *m)
    //@ requires kernel_state() &*& kernel_module(m);
    //@ ensures kernel_state();
{
    //@ open kernel_module(m);
    module_dispose *dispose = m->dispose;
    dispose();
    library_free(m->library);
    free(m);
}
