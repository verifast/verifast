#include "BeepKernel.h"

//@ unloadable_module;

//@ predicate my_beep_state() = [1/2]module_code(BeepDriver);

void my_beep_func()
    //@ requires my_beep_state();
    //@ ensures my_beep_state();
{
    //@ open my_beep_state();
    pcspeaker_play(500, 250);
    return;
    //@ close my_beep_state();
}

//@ predicate beep_driver_state() = [1/2]module_code(BeepDriver) &*& beep_func_registration(my_beep_state);

void module_dispose_func()
    //@ requires kernel_state() &*& beep_driver_state();
    //@ ensures kernel_state() &*& module(BeepDriver, false);
{
    //@ open beep_driver_state();
    unregister_beep_func();
    //@ open my_beep_state();
    return;
    //@ close_module();
}

module_dispose *module_init_func() //@ : module_init(BeepDriver)
    //@ requires kernel_state() &*& module(BeepDriver, true);
    //@ ensures kernel_state() &*& [_]is_module_dispose(result, BeepDriver, ?p) &*& p();
{
    //@ open_module();
    //@ produce_function_pointer_chunk beep_func(my_beep_func)(my_beep_state)() { call(); }
    //@ close my_beep_state();
    register_beep_func(my_beep_func);
    //@ produce_function_pointer_chunk module_dispose(module_dispose_func)(BeepDriver, beep_driver_state)() { call(); }
    return module_dispose_func;
    //@ close beep_driver_state();
}

