#include "stdlib.h"
#include "stdio.h"
#include "BeepKernel.h"
#include "Modules.h"

void pcspeaker_play(int freq, int millis)
    //@ requires 0 <= freq &*& 0 <= millis;
    //@ ensures true;
{
    puts("Beep!");
}

struct beep_info { // Using a struct because we don't support ghost globals yet.
    beep_func *beepFunc;
    //@ predicate() beepState;
};

static struct beep_info *beepInfo;

/*@

predicate kernel_state() =
    [1/2]beepInfo |-> ?info &*&
    info == 0 ?
        [1/2]beepInfo |-> 0
    :
        beep_info_beepFunc(info, ?f) &*&
        [1/2]beep_info_beepState(info, ?s) &*&
        s() &*&
        [_]is_beep_func(f, s) &*&
        malloc_block_beep_info(info);

predicate beep_func_registration(predicate() beepState) =
    [1/2]beepInfo |-> ?info &*&
    [1/2]beep_info_beepState(info, beepState);

@*/

void register_beep_func(beep_func *f)
    //@ requires kernel_state() &*& [_]is_beep_func(f, ?p) &*& p();
    //@ ensures kernel_state() &*& beep_func_registration(p);
{
    //@ open kernel_state();
    struct beep_info *info;
    if (beepInfo != 0) abort();
    info = malloc(sizeof(struct beep_info));
    if (info == 0) abort();
    info->beepFunc = f;
    beepInfo = info;
    //@ info->beepState = p;
    //@ close beep_func_registration(p);
    //@ close kernel_state();
}

void unregister_beep_func()
    //@ requires kernel_state() &*& beep_func_registration(?p);
    //@ ensures kernel_state() &*& p();
{
    //@ open kernel_state();
    //@ open beep_func_registration(p);
    //@ pointer_unique(&beepInfo);
    free(beepInfo);
    beepInfo = 0;
    //@ close kernel_state();
}

void do_beep()
    //@ requires kernel_state();
    //@ ensures kernel_state();
{
    //@ open kernel_state();
    if (beepInfo != 0) {
        beep_func *f = beepInfo->beepFunc;
        f();
    }
    //@ close kernel_state();
}

int main() //@ : main_full(BeepKernel)
    //@ requires module(BeepKernel, true);
    //@ ensures true;
{
    //@ open_module();
    struct module *m;
    beepInfo = 0;
    //@ close kernel_state();
    m = load_module("BeepDriver.dll");
    do_beep();
    unload_module(m);
    //@ leak kernel_state();
    return 0;
}