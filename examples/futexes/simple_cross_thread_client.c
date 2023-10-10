// Justus Fasse and Bart Jacobs. Expressive modular deadlock-freedom verification. 2023.

#include <stdlib.h>
#include "mutex.h"
#include "mutex_classic.h"

struct g {
    //@ bool held;
    //@ bool mainThreadSawFlag;
};
struct g g;
mutex m1;
bool flag;
mutex_classic m0;

/*@

fixpoint level L(int level) { return level(main, {1, level}); }

predicate m1_inv(bool held) = [1/2]g.held |-> held &*& held ? [1/2]g.held |-> held : true;
predicate m0_inv() =
    [1/2]flag |-> ?f &*& [1/2]g.mainThreadSawFlag |-> ?s &*&
    f ? s ? true : m1 |-> ?m1_ &*& mutex_held(m1_, m1_inv, 1) : !s;

predicate pre() = [1/2]flag |-> false &*& m1 |-> _ &*& g.held |-> _ &*& [1/2]m0 |-> ?m0_ &*& [1/2]mutex_classic(m0_, L(0), m0_inv);
predicate post() = [1/2]flag |-> true &*& [1/2]m0 |-> ?m0_ &*& [1/2]mutex_classic(m0_, L(0), m0_inv);

@*/

void acquirer()
//@ requires obs({L(1)})  &*& pre();
//@ ensures obs({L(1)}) &*& post();
//@ terminates;
{
    //@ open pre();
    //@ g.held = false;
    //@ close m1_inv(false);
    //@ close exists(m1_inv);
    m1 = create_mutex();
    //@ produce_func_lt(mutex_release);
    {
        /*@
        predicate waitInv() = [1/2]g.held |-> false;
        predicate post_() = obs({L(1)});
        @*/
        /*@
        produce_lemma_function_pointer_chunk mutex_acquire_wait_ghost_op(m1_inv, {L(1)}, waitInv)() {
            open m1_inv(true);
            open waitInv();
            assert false;
        };
        @*/
        /*@
        produce_lemma_function_pointer_chunk mutex_acquire_ghost_op(m1_inv, {L(1)}, waitInv, post_)() {
            open m1_inv(false);
            open waitInv();
            g.held = true;
            close m1_inv(true);
            close post_();
        };
        @*/
        //@ close waitInv();
        mutex_acquire(m1);
        //@ open post_();
    }

    mutex_classic_acquire(m0);
    //@ open m0_inv();
    flag = true;
    //@ close m0_inv();
    mutex_classic_release(m0);
    //@ close post();
}

int main() //@ : custom_main_spec
//@ requires obs({}) &*& module(simple_cross_thread_client, true);
//@ ensures obs({}) &*& module(simple_cross_thread_client, false);
//@ terminates;
{
    //@ open_module();
    //@ g.mainThreadSawFlag = false;
    //@ close m0_inv();
    //@ close exists(pair(L(0), m0_inv));
    m0 = create_mutex_classic();

    /*@
    produce_function_pointer_chunk thread_run_joinable(acquirer)(L(1), {}, pre, post)() {
        call();
    }
    @*/
    //@ close pre();
    thread t = fork_joinable(acquirer);

    mutex_classic_acquire(m0);
    //@ open m0_inv();
    if (!flag)
        abort();
    //@ g.mainThreadSawFlag = true;
    //@ close m0_inv();
    mutex_classic_release(m0);

    {
        /*@
        predicate pre_() = obs({});
        predicate post_(list<level> obs) = [1/2]g.held |-> false &*& obs == {};
        @*/
        /*@
        produce_lemma_function_pointer_chunk mutex_release_ghost_op(m1_inv, pre_, post_)() {
            open m1_inv(true);
            open pre_();
            g.held = false;
            close m1_inv(false);
            close post_({});
        };
        @*/
        //@ close pre_();
        mutex_release(m1);
        //@ open post_(_);
    }
    mutex_dispose(m1);
    //@ open m1_inv(false);

    join(t);
    //@ open post();
    
    mutex_classic_dispose(m0);
    //@ open m0_inv();
    
    //@ close_module();

    return 0;
}
