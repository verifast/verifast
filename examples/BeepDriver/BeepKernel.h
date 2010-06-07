#ifndef BEEPKERNEL_H
#define BEEPKERNEL_H

void pcspeaker_play(int freq, int millis);
    //@ requires 0 <= freq &*& 0 <= millis;
    //@ ensures true;

typedef void beep_func/*@(predicate() beepState)@*/();
    //@ requires beepState();
    //@ ensures beepState();

//@ predicate kernel_state();

//@ predicate beep_func_registration(predicate() state);

void register_beep_func(beep_func *f);
    //@ requires kernel_state() &*& [_]is_beep_func(f, ?p) &*& p();
    //@ ensures kernel_state() &*& beep_func_registration(p);

void unregister_beep_func();
    //@ requires kernel_state() &*& beep_func_registration(?p);
    //@ ensures kernel_state() &*& p();

typedef void module_dispose/*@(int m, predicate() p)@*/();
    //@ requires kernel_state() &*& p();
    //@ ensures kernel_state() &*& module(m, false);

typedef module_dispose *module_init/*@(int m)@*/();
    //@ requires kernel_state() &*& module(m, true);
    //@ ensures kernel_state() &*& [_]is_module_dispose(result, m, ?p) &*& p();

#endif