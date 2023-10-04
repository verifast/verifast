// Justus Fasse and Bart Jacobs. Expressive modular verification of termination for busy-waiting programs. 2023.

#include <stdlib.h>
#include "atomics.h"
#include "spinlock.h"

struct globals {
    struct spinlock *spinlock;
    int done;
    //@ bool thread1_holds_spinlock;
    //@ void *thread1_signal;
    //@ bool thread2_holds_spinlock;
    //@ void *thread2_signal;
    //@ bool thread2_knows_done;
    //@ bool main_set_done;
    //@ void *main_signal;
};

struct globals g;

/*@

fixpoint level L(int level) { return level(main, {1, level}); }

predicate signal_if(void *signal, level level, bool cond) =
    cond ? signal(signal, level, false) : true;

predicate atomic_space_inv() =
    [1/4]g.thread1_holds_spinlock |-> ?h1 &*&
    [1/4]g.thread2_holds_spinlock |-> ?h2 &*&
    [1/3]g.thread1_signal |-> ?thread1_signal &*&
    [1/3]g.thread2_signal |-> ?thread2_signal &*&
    [1/2]g.thread2_knows_done |-> ?t2d &*&
    [1/3]g.main_signal |-> ?main_signal &*&
    g.done |-> ?done &*&
    [1/2]g.main_set_done |-> ?main_set_done &*& !main_set_done || done &*&
    signal_if(thread1_signal, L(0), h1) &*&
    signal_if(thread2_signal, L(1), h2 || !t2d) &*&
    signal_if(main_signal, L(0), !main_set_done);

predicate spinlock_inv(bool held) =
    [1/4]g.thread1_holds_spinlock |-> ?h1 &*&
    [1/4]g.thread2_holds_spinlock |-> ?h2 &*&
    !(h1 && h2) &*&
    held == (h1 || h2);

@*/

void thread1()
/*@
requires
    obs({Forkee}, cons(pair(?terminationSignal, L(2)), nil)) &*& call_below_perm({}, main) &*&
    [1/3]g.spinlock |-> ?spinlock &*& [1/2]spinlock(spinlock, spinlock_inv) &*&
    pointer_within_limits(&g.done) == true &*&
    [1/3]g.thread1_signal |-> ?thread1_signal &*&
    signal_uninit(thread1_signal) &*&
    [1/3]g.thread2_signal |-> ?thread2_signal &*&
    [1/2]g.thread1_holds_spinlock |-> false &*&
    [1/3]atomic_space(main, atomic_space_inv);
@*/
/*@
ensures obs(_, {pair(terminationSignal, L(2))}) &*&
    [1/3]g.spinlock |-> spinlock &*& [1/2]spinlock(spinlock, spinlock_inv) &*&
    [1/3]g.thread1_signal |-> thread1_signal &*&
    [1/3]g.thread2_signal |-> thread2_signal &*&
    [1/2]g.thread1_holds_spinlock |-> false &*&
    [1/3]atomic_space(main, atomic_space_inv);
@*/
//@ terminates;
{
    //@ produce_func_lt(spinlock_acquire);
    //@ create_wait_perm(thread2_signal, L(1), spinlock_acquire);
    {
        /*@
        predicate pre() =
            obs({Forkee}, {pair(terminationSignal, L(2))}) &*&
            [1/3]atomic_space(main, atomic_space_inv) &*&
            [1/3]g.thread1_signal |-> thread1_signal &*&
            signal_uninit(thread1_signal) &*&
            [1/2]g.thread1_holds_spinlock |-> false &*&
            [1/3]g.thread2_signal |-> thread2_signal &*&
            wait_perm({}, thread2_signal, L(1), spinlock_acquire);
        predicate post() =
            obs({Forkee}, {pair(thread1_signal, L(0)), pair(terminationSignal, L(2))}) &*&
            [1/3]atomic_space(main, atomic_space_inv) &*&
            [1/3]g.thread1_signal |-> thread1_signal &*&
            [1/2]g.thread1_holds_spinlock |-> true &*&
            [1/3]g.thread2_signal |-> thread2_signal;
        @*/
        /*@
        produce_lemma_function_pointer_chunk spinlock_acquire_ghost_op(spinlock_inv, pre, post, currentThread)() {
            open spinlock_inv(?held);
            open pre();
            assert atomic_spaces(?spaces);
            if (mem(pair(main, atomic_space_inv), spaces)) {
                produce_func_lt(spinlock_acquire);
                forall_mem(pair(main, atomic_space_inv), spaces, (space_name_lt)(spinlock_acquire));
                assert false;
            }
            open_atomic_space(main, atomic_space_inv);
            open atomic_space_inv();
            if (held) {
                open signal_if(g.thread2_signal, L(1), true);
                wait(g.thread2_signal);
                close signal_if(g.thread2_signal, L(1), true);
                close pre();
            } else {
                leak wait_perm({}, thread2_signal, L(1), spinlock_acquire);
                g.thread1_holds_spinlock = true;
                init_signal(g.thread1_signal, L(0));
                close post();
                open signal_if(g.thread1_signal, L(0), false);
                close signal_if(g.thread1_signal, L(0), true);
            }
            close atomic_space_inv();
            close_atomic_space(main, atomic_space_inv);
            close spinlock_inv(true);
        };
        @*/
        //@ close pre();
        spinlock_acquire(g.spinlock);
        //@ open post();
    }
    {
        /*@
        predicate pre() = true;
        predicate post() = true;
        @*/
        /*@
        produce_lemma_function_pointer_chunk atomic_store_int_ghost_op(main, atomic_space_inv, &g.done, 1, pre, post, currentThread)() {
            open atomic_space_inv();
            open pre();
            assert is_atomic_store_int_op(?op, &g.done, 1, ?P, ?Q);
            op();
            close post();
            close atomic_space_inv();
        };
        @*/
        //@ close pre();
        atomic_store_int(&g.done, 1);
        //@ leak is_atomic_store_int_ghost_op(_, _, _, _, _, _, _, _);
        //@ open post();
    }
    {
        /*@
        predicate pre() =
            [1/3]atomic_space(main, atomic_space_inv) &*&
            [1/2]g.thread1_holds_spinlock |-> true &*&
            [1/3]g.thread1_signal |-> thread1_signal &*& obs({Forkee}, {pair(thread1_signal, L(0)), pair(terminationSignal, L(2))});
        predicate post() =
            [1/3]atomic_space(main, atomic_space_inv) &*&
            [1/2]g.thread1_holds_spinlock |-> false &*&
            [1/3]g.thread1_signal |-> thread1_signal &*& obs({Forkee}, {pair(terminationSignal, L(2))});
        @*/
        /*@
        produce_lemma_function_pointer_chunk spinlock_release_ghost_op(spinlock_inv, pre, post)() {
            open spinlock_inv(_);
            open pre();
            assert atomic_spaces(?spaces);
            if (mem(pair(main, atomic_space_inv), spaces)) {
                produce_func_lt(spinlock_acquire);
                forall_mem(pair(main, atomic_space_inv), spaces, (space_name_lt)(spinlock_acquire));
                assert false;
            }
            open_atomic_space(main, atomic_space_inv);
            open atomic_space_inv();
            
            g.thread1_holds_spinlock = false;
            open signal_if(g.thread1_signal, L(0), true);
            set_signal(g.thread1_signal);
            leak signal(_, _, true);
            close signal_if(g.thread1_signal, L(0), false);
            
            close atomic_space_inv();
            close_atomic_space(main, atomic_space_inv);
            close spinlock_inv(false);
            close post();
        };
        @*/
        //@ close pre();
        spinlock_release(g.spinlock);
        //@ open post();
    }
}

void thread2()
/*@
requires
    [1/3]g.thread2_signal |-> ?thread2_signal &*&
    obs({Forkee, Forker}, cons(pair(?terminationSignal, L(3)), {pair(thread2_signal, L(1))})) &*&
    pointer_within_limits(&g.done) == true &*&
    [1/3]g.spinlock |-> ?spinlock &*& [1/3]spinlock(spinlock, spinlock_inv) &*&
    [1/3]g.thread1_signal |-> ?thread1_signal &*&
    [1/3]g.main_signal |-> ?main_signal &*&
    call_below_perm({}, main) &*&
    call_below_perm({}, main) &*&
    [1/2]g.thread2_holds_spinlock |-> false &*&
    [1/2]g.thread2_knows_done |-> false &*&
    [1/3]atomic_space(main, atomic_space_inv);
@*/
/*@
ensures
    [1/3]g.thread2_signal |-> thread2_signal &*&
    obs({Forkee, Forker}, {pair(terminationSignal, L(3))}) &*&
    [1/3]g.spinlock |-> spinlock &*& [1/3]spinlock(spinlock, spinlock_inv) &*&
    [1/3]g.thread1_signal |-> thread1_signal &*&
    [1/3]g.main_signal |-> main_signal &*&
    [1/2]g.thread2_holds_spinlock |-> false &*&
    [1/2]g.thread2_knows_done |-> true &*&
    [1/3]atomic_space(main, atomic_space_inv);
@*/
//@ terminates;
{
    //@ produce_func_lt(spinlock_acquire);
    //@ create_wait_perm(thread1_signal, L(0), spinlock_acquire);
    //@ create_wait_perm(main_signal, L(0), thread2);
    for (;;)
    /*@
    invariant
        [1/3]g.spinlock |-> spinlock &*& [1/3]spinlock(spinlock, spinlock_inv) &*&
        [1/3]g.thread1_signal |-> thread1_signal &*&
        wait_perm({}, thread1_signal, L(0), spinlock_acquire) &*&
        wait_perm({}, main_signal, L(0), thread2) &*&
        [1/3]g.thread2_signal |-> thread2_signal &*&
        [1/3]g.main_signal |-> main_signal &*&
        obs({Forkee, Forker}, {pair(terminationSignal, L(3)), pair(thread2_signal, L(1))}) &*&
        [1/2]g.thread2_holds_spinlock |-> false &*&
        [1/2]g.thread2_knows_done |-> false &*&
        [1/3]atomic_space(main, atomic_space_inv);
    @*/
    {
        {
            /*@
            predicate pre() =
                obs({Forkee, Forker}, {pair(terminationSignal, L(3)), pair(thread2_signal, L(1))}) &*&
                [1/3]g.thread1_signal |-> thread1_signal &*&
                wait_perm({}, thread1_signal, L(0), spinlock_acquire) &*&
                [1/3]g.thread2_signal |-> thread2_signal &*&
                [1/2]g.thread2_holds_spinlock |-> false &*&
                [1/2]g.thread2_knows_done |-> false &*&
                [1/3]atomic_space(main, atomic_space_inv);
            predicate post() =
                [1/3]g.thread1_signal |-> thread1_signal &*&
                wait_perm({}, thread1_signal, L(0), spinlock_acquire) &*&
                [1/3]g.thread2_signal |-> thread2_signal &*& 
                obs({Forkee, Forker}, {pair(terminationSignal, L(3)), pair(thread2_signal, L(1))}) &*&
                [1/2]g.thread2_holds_spinlock |-> true &*&
                [1/2]g.thread2_knows_done |-> false &*&
                [1/3]atomic_space(main, atomic_space_inv);
            @*/
            /*@
            produce_lemma_function_pointer_chunk spinlock_acquire_ghost_op(spinlock_inv, pre, post, currentThread)() {
                open spinlock_inv(?held);
                open pre();
                assert atomic_spaces(?spaces);
                if (mem(pair(main, atomic_space_inv), spaces)) {
                    produce_func_lt(spinlock_acquire);
                    forall_mem(pair(main, atomic_space_inv), spaces, (space_name_lt)(spinlock_acquire));
                    assert false;
                }
                open_atomic_space(main, atomic_space_inv);
                open atomic_space_inv();
                
                if (held) {
                    open signal_if(g.thread1_signal, L(0), true);
                    wait(g.thread1_signal);
                    close signal_if(g.thread1_signal, L(0), true);
                    close pre();
                } else {
                    g.thread2_holds_spinlock = true;
                    close post();
                }
                
                close atomic_space_inv();
                close_atomic_space(main, atomic_space_inv);
                close spinlock_inv(true);
            };
            @*/
            //@ close pre();
            spinlock_acquire(g.spinlock);
            //@ open post();
        }
        //@ bool t1d = g.thread2_knows_done;
        int d;
        {
            /*@
            predicate pre() =
                [1/3]g.main_signal |-> main_signal &*&
                wait_perm({}, main_signal, L(0), thread2) &*&
                obs({Forkee, Forker}, {pair(terminationSignal, L(3)), pair(thread2_signal, L(1))}) &*&
                [1/2]g.thread2_holds_spinlock |-> true &*& [1/2]g.thread2_knows_done |-> false;
            predicate post(int result) =
                [1/3]g.main_signal |-> main_signal &*&
                wait_perm({}, main_signal, L(0), thread2) &*&
                obs({Forkee, Forker}, {pair(terminationSignal, L(3)), pair(thread2_signal, L(1))}) &*&
                [1/2]g.thread2_holds_spinlock |-> true &*& [1/2]g.thread2_knows_done |-> result != 0 &*&
                result == 0 ? call_perm_(currentThread, thread2) : true;
            @*/
            /*@
            produce_lemma_function_pointer_chunk atomic_load_int_ghost_op(main, atomic_space_inv, &g.done, pre, post, currentThread)() {
                open atomic_space_inv();
                open pre();
                
                assert is_atomic_load_int_op(?op, &g.done, ?P, ?Q);
                op();
                close globals_done(&g, ?done);
                
                if (g.done) {
                    g.thread2_knows_done = true;
                } else {
                    open signal_if(g.main_signal, L(0), true);
                    wait(g.main_signal);
                    close signal_if(g.main_signal, L(0), true);
                }
                
                close post(done);
                close atomic_space_inv();
            };
            @*/
            //@ close pre();
            d = atomic_load_int(&g.done);
            //@ leak is_atomic_load_int_ghost_op(_, _, _, _, _, _, _);
            //@ open post(d);
        }
        {
            /*@
            predicate pre() =
                [1/3]g.thread2_signal |-> thread2_signal &*&
                [1/2]g.thread2_holds_spinlock |-> true &*&
                [1/2]g.thread2_knows_done |-> d != 0 &*&
                obs({Forkee, Forker}, {pair(terminationSignal, L(3)), pair(thread2_signal, L(1))}) &*&
                [1/3]atomic_space(main, atomic_space_inv);
            predicate post() =
                [1/3]g.thread2_signal |-> thread2_signal &*&
                [1/2]g.thread2_holds_spinlock |-> false &*&
                [1/2]g.thread2_knows_done |-> d != 0 &*&
                obs({Forkee, Forker}, cons(pair(terminationSignal, L(3)), d != 0 ? nil : {pair(thread2_signal, L(1))})) &*&
                [1/3]atomic_space(main, atomic_space_inv);
            @*/
            /*@
            produce_lemma_function_pointer_chunk spinlock_release_ghost_op(spinlock_inv, pre, post)() {
                open spinlock_inv(_);
                open pre();
                assert atomic_spaces(?spaces);
                if (mem(pair(main, atomic_space_inv), spaces)) {
                    produce_func_lt(spinlock_acquire);
                    forall_mem(pair(main, atomic_space_inv), spaces, (space_name_lt)(spinlock_acquire));
                    assert false;
                }
                open_atomic_space(main, atomic_space_inv);
                open atomic_space_inv();
                
                g.thread2_holds_spinlock = false;
                if (d != 0) {
                    open signal_if(g.thread2_signal, L(1), true);
                    set_signal(g.thread2_signal);
                    leak signal(thread2_signal, L(1), true);
                    close signal_if(g.thread2_signal, L(1), false);
                }
                
                close atomic_space_inv();
                close_atomic_space(main, atomic_space_inv);
                close post();
                close spinlock_inv(false);
            };
            @*/
            //@ close pre();
            spinlock_release(g.spinlock);
            //@ open post();
        }
        if (d)
            break;
    }
    //@ leak wait_perm({}, thread1_signal, L(0), spinlock_acquire);
    //@ leak wait_perm({}, main_signal, L(0), thread2);
}

int main() //@ : custom_main_spec
//@ requires module(tricky_client, true) &*& obs({}, {});
//@ ensures module(tricky_client, false) &*& obs(_, {});
//@ terminates;
{
    //@ open_module();

    //@ void *thread1_signal = g.thread1_signal = create_signal();
    //@ void *thread2_signal = g.thread2_signal = create_signal();
    //@ init_signal(g.thread2_signal, L(1));
    //@ void *main_signal = g.main_signal = create_signal();
    //@ init_signal(g.main_signal, L(0));
    //@ g.thread1_holds_spinlock = false;
    //@ g.thread2_holds_spinlock = false;
    //@ g.thread2_knows_done = false;
    //@ g.main_set_done = false;
    //@ close signal_if(g.thread1_signal, L(0), false);
    //@ close signal_if(g.thread2_signal, L(1), true);
    //@ close signal_if(g.main_signal, L(0), true);
    //@ close atomic_space_inv();
    //@ create_atomic_space(main, atomic_space_inv);
    //@ close spinlock_inv(false);
    //@ close exists(spinlock_inv);
    struct spinlock *spinlock = create_spinlock();
    g.spinlock = spinlock;
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();
    //@ produce_call_below_perm_();
    //@ pathize_call_below_perm_();

    {
        /*@
        predicate thread1_pre() =
            call_below_perm({}, main) &*&
            [1/3]g.spinlock |-> spinlock &*& [1/2]spinlock(spinlock, spinlock_inv) &*&
            pointer_within_limits(&g.done) == true &*&
            [1/3]g.thread1_signal |-> thread1_signal &*&
            signal_uninit(thread1_signal) &*&
            [1/3]g.thread2_signal |-> thread2_signal &*&
            [1/2]g.thread1_holds_spinlock |-> false &*&
            [1/3]atomic_space(main, atomic_space_inv);
        predicate thread1_post() =
            [1/3]g.spinlock |-> spinlock &*& [1/2]spinlock(spinlock, spinlock_inv) &*&
            [1/3]g.thread1_signal |-> thread1_signal &*&
            [1/3]g.thread2_signal |-> thread2_signal &*&
            [1/2]g.thread1_holds_spinlock |-> false &*&
            [1/3]atomic_space(main, atomic_space_inv);
        predicate thread2_pre() =
            [1/3]g.thread2_signal |-> thread2_signal &*&
            pointer_within_limits(&g.done) == true &*&
            [1/3]g.spinlock |-> spinlock &*& [1/3]spinlock(spinlock, spinlock_inv) &*&
            [1/3]g.thread1_signal |-> thread1_signal &*&
            [1/3]g.main_signal |-> main_signal &*&
            call_below_perm({}, main) &*&
            call_below_perm({}, main) &*&
            [1/2]g.thread2_holds_spinlock |-> false &*&
            [1/2]g.thread2_knows_done |-> false &*&
            [1/3]atomic_space(main, atomic_space_inv);
        predicate thread2_post() =
            [1/3]g.thread2_signal |-> thread2_signal &*&
            [1/3]g.spinlock |-> spinlock &*& [1/3]spinlock(spinlock, spinlock_inv) &*&
            [1/3]g.thread1_signal |-> thread1_signal &*&
            [1/3]g.main_signal |-> main_signal &*&
            [1/2]g.thread2_holds_spinlock |-> false &*&
            [1/2]g.thread2_knows_done |-> true &*&
            [1/3]atomic_space(main, atomic_space_inv);
        @*/
        
        /*@
        produce_function_pointer_chunk thread_run_joinable(thread1)({}, {}, thread1_pre, thread1_post, L(2))() {
            open thread1_pre();
            call();
            close thread1_post();
        }
        @*/
        //@ close thread1_pre();
        thread t1 = fork_joinable(thread1);
        
        /*@
        produce_function_pointer_chunk thread_run_joinable(thread2)({Forker}, {pair(thread2_signal, L(1))}, thread2_pre, thread2_post, L(3))() {
            open thread2_pre();
            call();
            close thread2_post();
        }
        @*/
        //@ close thread2_pre();
        thread t2 = fork_joinable(thread2);

        {
            /*@
            predicate pre() = [1/2]g.main_set_done |-> false &*& [1/3]g.main_signal |-> main_signal &*& obs({Forker, Forker}, {pair(main_signal, L(0))});
            predicate post() = [1/2]g.main_set_done |-> true &*& [1/3]g.main_signal |-> main_signal &*& obs({Forker, Forker}, {});
            @*/
            /*@
            produce_lemma_function_pointer_chunk atomic_store_int_ghost_op(main, atomic_space_inv, &g.done, 1, pre, post, currentThread)() {
                open atomic_space_inv();
                open pre();
                
                assert is_atomic_store_int_op(?op, &g.done, 1, ?P, ?Q);
                op();
                
                open signal_if(main_signal, L(0), true);
                set_signal(main_signal);
                leak signal(main_signal, L(0), true);
                close signal_if(main_signal, L(0), false);
                g.main_set_done = true;
                
                close atomic_space_inv();
                close post();
            };
            @*/
            //@ close pre();
            atomic_store_int(&g.done, 1);
            //@ leak is_atomic_store_int_ghost_op(_, _, _, _, _, _, _, _);
            //@ open post();
        }
    
        join(t1);
        //@ open thread1_post();
        join(t2);
        //@ open thread2_post();
    }
    
    //@ destroy_atomic_space();
    //@ open atomic_space_inv();
    spinlock_dispose(spinlock);
    //@ open spinlock_inv(_);
    
    //@ close_module();
    //@ open signal_if(thread1_signal, L(0), _);
    //@ open signal_if(thread2_signal, L(1), _);
    //@ open signal_if(main_signal, L(0), _);
    
    return 0;
}
