#include "stdlib.h"
#include "threading.h"

int wait_for_source();
    //@ requires true;
    //@ ensures true;

bool wait_for_pulse(int source); // true means the sensor has been removed.
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

//@ predicate_ctor counter(struct counter *counter)() = counter->count |-> ?count;

struct count_pulses_data {
    struct counter *counter;
    int source;
};

/*@

predicate_family_instance thread_run_data(count_pulses)(struct count_pulses_data *data) =
    data->counter |-> ?counter &*& data->source |-> ?source &*& malloc_block_count_pulses_data(data) &*&
    [_]counter->mutex |-> ?mutex &*& [_]mutex(mutex, counter(counter));

@*/

void count_pulses(struct count_pulses_data *data) //@ : thread_run
    //@ requires thread_run_data(count_pulses)(data);
    //@ ensures true;
{
    //@ open thread_run_data(count_pulses)(data);
    struct counter *counter = data->counter;
    int source = data->source;
    free(data);
    
    struct mutex *mutex = counter->mutex;
    bool done = false;
    while (!done)
        //@ invariant [_]mutex(mutex, counter(counter));
    {
        done = wait_for_pulse(source);
        if (!done) {
            mutex_acquire(mutex);
            //@ open counter(counter)();
            counter->count++;
            //@ close counter(counter)();
            mutex_release(mutex);
        }
    }
}

void count_pulses_async(struct counter *counter, int source)
    //@ requires [_]counter->mutex |-> ?mutex &*& [_]mutex(mutex, counter(counter));
    //@ ensures true;
{
    struct count_pulses_data *data = malloc(sizeof(struct count_pulses_data));
    if (data == 0) abort();
    data->counter = counter;
    data->source = source;
    //@ close thread_run_data(count_pulses)(data);
    thread_start(count_pulses, data);
}

/*@

predicate_family_instance thread_run_data(print_count)(struct counter *counter) =
    [_]counter->mutex |-> ?mutex &*& [_]mutex(mutex, counter(counter));

@*/

void print_count(struct counter *counter) //@ : thread_run
    //@ requires thread_run_data(print_count)(counter);
    //@ ensures true;
{
    //@ open thread_run_data(print_count)(counter);
    struct mutex *mutex = counter->mutex;
    while (true)
        //@ invariant [_]mutex(mutex, counter(counter));
    {
        sleep(1000);
        mutex_acquire(mutex);
        //@ open counter(counter)();
        print_int(counter->count);
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
    //@ leak counter->mutex |-> mutex &*& mutex(mutex, _);
    
    //@ close thread_run_data(print_count)(counter);
    thread_start(print_count, counter);
    
    while (true)
        //@ invariant [_]counter->mutex |-> mutex &*& [_]mutex(mutex, counter(counter));
    {
        int source = wait_for_source();
        count_pulses_async(counter, source);
    }
}