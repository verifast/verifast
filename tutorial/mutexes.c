#include "stdlib.h"
#include "threading.h"

void wait_for_pulse(int source);
    //@ requires true;
    //@ ensures true;

void sleep(int millis);
    //@ requires true;
    //@ ensures true;

void print_int(int n);
    //@ requires true;
    //@ ensures true;

struct counter {
    int count;
    struct mutex *mutex;
};

//@ predicate_ctor counter(struct counter *counter)() = counter->count |-> _;

struct count_pulses_data {
    struct counter *counter;
    int source;
};

struct count_pulses_data *create_count_pulses_data(struct counter *counter, int source)
    //@ requires true;
    //@ ensures result->counter |-> counter &*& result->source |-> source &*& malloc_block_count_pulses_data(result);
{
    struct count_pulses_data *data = malloc(sizeof(struct count_pulses_data));
    if (data == 0) abort();
    data->counter = counter;
    data->source = source;
    return data;
}

/*@

predicate_family_instance thread_run_pre(count_pulses)(struct count_pulses_data *data, unit info) =
    data->counter |-> ?counter &*& data->source |-> _ &*&
    [1/2]counter->mutex |-> ?mutex &*& [1/3]mutex(mutex, counter(counter));
predicate_family_instance thread_run_post(count_pulses)(struct count_pulses_data *data, unit info) = false;

@*/

void count_pulses(struct count_pulses_data *data) //@ : thread_run
    //@ requires thread_run_pre(count_pulses)(data, ?info);
    //@ ensures thread_run_post(count_pulses)(data, info);
{
    //@ open thread_run_pre(count_pulses)(data, ?info_);
    struct counter *counter = data->counter;
    int source = data->source;
    
    struct mutex *mutex = counter->mutex;
    
    while (true)
        //@ invariant [1/3]mutex(mutex, counter(counter));
    {
        wait_for_pulse(source);
        mutex_acquire(mutex);
        //@ open counter(counter)();
        counter->count++;
        //@ close counter(counter)();
        mutex_release(mutex);
    }
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct counter *counter = malloc(sizeof(struct counter));
    if (counter == 0) abort();
    counter->count = 0;
    //@ close counter(counter)();
    //@ close create_mutex_ghost_arg(counter(counter));
    struct mutex *mutex = create_mutex();
    counter->mutex = mutex;
    
    struct count_pulses_data *data1 = create_count_pulses_data(counter, 1);
    //@ close thread_run_pre(count_pulses)(data1, unit);
    thread_start(count_pulses, data1);
    //@ leak thread(_, _, _, _);
    
    struct count_pulses_data *data2 = create_count_pulses_data(counter, 2);
    //@ close thread_run_pre(count_pulses)(data2, unit);
    thread_start(count_pulses, data2);
    //@ leak thread(_, _, _, _);
    
    while (true)
        //@ invariant [1/3]mutex(mutex, counter(counter));
    {
        sleep(1000);
        mutex_acquire(mutex);
        //@ open counter(counter)();
        print_int(counter->count);
        //@ close counter(counter)();
        mutex_release(mutex);
    }
}