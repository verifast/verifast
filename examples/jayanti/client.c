// By Bart Jacobs
// Client program based on the example client in Delbianco, Sergey, Nanevski, and Banerjee, "Concurrent data structures linked in time", ECOOP 2017.

#include <threading.h>
#include <stdlib.h>
#include "jayanti.h"

array_t array;
int sx;
int sy;
struct mutex *x_mutex;
struct info {
    //@ int thread1_pc; // 0, 1, or 2
};
struct info info;

//@ predicate array_inv(int x, int y) = [1/2]info.thread1_pc |-> ?t1pc &*& t1pc == 0 || x != 0 &*& y != 1 || t1pc == 2;
//@ predicate x_mutex_inv() = [1/4]array |-> ?arr &*& array_x_writer(arr, array_inv);

/*@

predicate_family_instance thread_run_pre(thread1)(void *data, any info_) =
    [1/2]x_mutex |-> ?xMutex &*& [1/2]mutex(xMutex, x_mutex_inv) &*& [1/4]array |-> ?arr &*& array_y_writer(arr, array_inv) &*& [1/2]info.thread1_pc |-> 0;
predicate_family_instance thread_run_post(thread1)(void *data, any info_) =
    [1/2]x_mutex |-> ?xMutex &*& [1/2]mutex(xMutex, x_mutex_inv) &*& [1/4]array |-> ?arr &*& array_y_writer(arr, array_inv) &*& [1/2]info.thread1_pc |-> 2;

@*/

void thread1(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread1)(data, ?info_);
    //@ ensures thread_run_post(thread1)(data, info_);
{
    //@ open thread_run_pre(thread1)(data, info_);
    
    mutex_acquire(x_mutex);
    //@ open x_mutex_inv();
    {
        /*@
        predicate pre() = [1/2]info.thread1_pc |-> 0;
        predicate post() = [1/2]info.thread1_pc |-> 1;
        @*/
        /*@
        produce_lemma_function_pointer_chunk array_write_x_ghop(array_inv, 2, pre, post)() {
            open pre();
            open array_inv(?x, ?y);
            info.thread1_pc = 1;
            close array_inv(2, y);
            close post();
        };
        @*/
        //@ close pre();
        array_write_x(array, 2);
        //@ open post();
    }
    //@ close x_mutex_inv();
    mutex_release(x_mutex);
    {
        /*@
        predicate pre() = [1/2]info.thread1_pc |-> 1;
        predicate post() = [1/2]info.thread1_pc |-> 2;
        @*/
        /*@
        produce_lemma_function_pointer_chunk array_write_y_ghop(array_inv, 1, pre, post)() {
            open pre();
            open array_inv(?x, ?y);
            info.thread1_pc = 2;
            close array_inv(x, 1);
            close post();
        };
        @*/
        //@ close pre();
        array_write_y(array, 1);
        //@ open post();
    }
    
    //@ close thread_run_post(thread1)(data, info_);
}

/*@
predicate_family_instance thread_run_pre(thread2)(void *data, any info_) =
    [1/4]array |-> ?arr &*& array_scanner(arr, array_inv) &*& sx |-> _ &*& sy |-> _;
predicate_family_instance thread_run_post(thread2)(void *data, any info_) =
    [1/4]array |-> ?arr &*& array_scanner(arr, array_inv) &*& sx |-> ?sx_ &*& sy |-> ?sy_ &*& sy_ != 1 || sx_ != 0;
@*/

void thread2(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread2)(data, ?info_);
    //@ ensures thread_run_post(thread2)(data, info_);
{
    //@ open thread_run_pre(thread2)(data, info_);
    {
        /*@
        predicate pre() = true;
        predicate post(int x, int y) = y != 1 || x != 0;
        @*/
        /*@
        produce_lemma_function_pointer_chunk array_scan_ghop(array_inv, pre, post)() {
            open pre();
            open array_inv(?x, ?y);
            close post(x, y);
            close array_inv(x, y);
        };
        @*/
        //@ close pre();
        array_scan(array, &sx, &sy);
        //@ open post(_, _);
    }
    //@ close thread_run_post(thread2)(data, info_);
}

/*@
predicate_family_instance thread_run_pre(thread3)(void *data, any info_) =
    [1/2]x_mutex |-> ?xMutex &*& [1/2]mutex(xMutex, x_mutex_inv);
predicate_family_instance thread_run_post(thread3)(void *data, any info_) =
    [1/2]x_mutex |-> ?xMutex &*& [1/2]mutex(xMutex, x_mutex_inv);
@*/

void thread3(void *data) //@ : thread_run_joinable
    //@ requires thread_run_pre(thread3)(data, ?info_);
    //@ ensures thread_run_post(thread3)(data, info_);
{
    //@ open thread_run_pre(thread3)(data, info_);
    mutex_acquire(x_mutex);
    //@ open x_mutex_inv();
    {
        /*@
        predicate pre() = true;
        predicate post() = true;
        @*/
        /*@
        produce_lemma_function_pointer_chunk array_write_x_ghop(array_inv, 3, pre, post)() {
            open pre();
            open array_inv(?x, ?y);
            close array_inv(3, y);
            close post();
        };
        @*/
        //@ close pre();
        array_write_x(array, 3);
        //@ open post();
    }
    //@ close x_mutex_inv();
    mutex_release(x_mutex);
    //@ close thread_run_post(thread3)(data, info_);
}

int main()
    //@ requires module(client, true);
    //@ ensures true;
{
    //@ open_module();
    //@ info.thread1_pc = 0;
    //@ close array_inv(0, 0);
    //@ close exists(array_inv);
    array = create_array();
    //@ close x_mutex_inv();
    //@ close create_mutex_ghost_arg(x_mutex_inv);
    x_mutex = create_mutex();
    //@ close thread_run_pre(thread1)(0, unit);
    thread t1 = thread_start_joinable(thread1, 0);
    //@ close thread_run_pre(thread2)(0, unit);
    thread t2 = thread_start_joinable(thread2, 0);
    //@ close thread_run_pre(thread3)(0, unit);
    thread t3 = thread_start_joinable(thread3, 0);
    thread_join(t1);
    //@ open thread_run_post(thread1)(0, unit);
    thread_join(t2);
    //@ open thread_run_post(thread2)(0, unit);
    thread_join(t3);
    //@ open thread_run_post(thread3)(0, unit);
    assert sy != 1 || sx != 0;
    
    exit(0);
}
