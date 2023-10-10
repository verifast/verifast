// Justus Fasse and Bart Jacobs. Expressive modular deadlock-freedom verification. 2023.

#include "mutex_classic.h"
//@ #include <quantifiers.gh>

int x;
mutex_classic mutex;

/*@

predicate inv() = x |-> ?v &*& v == 0 || v == 1;
predicate pre(;) = [1/2]mutex |-> ?mutex_ &*& [1/2]mutex_classic(mutex_, L(0), inv);

fixpoint level L(int level) { return level(main, {1, level}); }

@*/

void invert()
//@ requires obs(?obs) &*& forall(obs, (level_lt)(L(0))) == true &*& pre();
//@ ensures obs(obs) &*& pre();
//@ terminates;
{
    //@ open pre();
    //@ produce_func_lt(mutex_classic_acquire);
    /*@
    if (!forall(obs, (func_lt_level)(mutex_classic_acquire))) {
        level badLevel = not_forall(obs, (func_lt_level)(mutex_classic_acquire));
        forall_elim(obs, (level_lt)(L(0)), badLevel);
        assert false;
    }
    @*/
    mutex_classic_acquire(mutex);
    //@ open inv();
    x = 1 - x;
    //@ close inv();
    mutex_classic_release(mutex);
    //@ close pre();
}

int main() //@ : custom_main_spec
//@ requires obs({}) &*& module(simple_classic_client, true);
//@ ensures obs({}) &*& module(simple_classic_client, false);
//@ terminates;
{
    //@ open_module();
    //@ close inv();
    //@ close exists(pair(L(0), inv));
    mutex = create_mutex_classic();

    /*@
    produce_function_pointer_chunk thread_run_joinable(invert)(L(1), {}, pre, pre)() { call(); }
    @*/
    //@ close pre();
    thread t = fork_joinable(invert);
    
    //@ close pre();
    invert();
    //@ open pre();

    join(t);
    //@ open pre();

    mutex_classic_dispose(mutex);
    //@ open inv();
    //@ close_module();

    return 0;
}
