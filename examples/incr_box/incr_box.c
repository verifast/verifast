#include "stdlib.h"
#include "threading.h"

struct counter {
    int count;
    struct lock *lock;
};

/*@

box_class counter_box(struct counter *counter, int count) {
    invariant counter->count |-> count;

    action increase();
        requires true;
        ensures old_count <= count;
    
    handle_predicate count_handle(int count0) {
        invariant count0 <= count;
        
        preserved_by increase() {
        }
    }
}

predicate_ctor counter(struct counter *counter, box boxId)() =
    counter_box(boxId, counter, _);

lemma real counter_lock_split_fractions(struct counter *counter);
    requires [?f]counter->lock |-> ?lock;
    ensures [result]counter->lock |-> lock &*& [f - result]counter->lock |-> lock;

predicate incrementor_session(struct counter *counter, box boxId) =
    [_]counter->lock |-> ?lock &*& [_]lock(lock, counter(counter, boxId));

predicate_family_instance thread_run_data(incrementor)(void *data) =
    incrementor_session(data, _);
@*/


void incrementor(void *data) //@ : thread_run
    //@ requires thread_run_data(incrementor)(data);
    //@ ensures true;
{
    //@ open thread_run_data(incrementor)(data);
    struct counter *counter = data;
    //@ open incrementor_session(counter, ?boxId);
    struct lock *lock = counter->lock;
    lock_acquire(lock);
    //@ open counter(counter, boxId)();
    //@ handle h = create_handle counter_box_handle(boxId);
    int count0 = 0;
    /*@
    consuming_box_predicate counter_box(boxId, _, _)
    consuming_handle_predicate counter_box_handle(h)
    perform_action increase() {
        @*/
        {
            count0 = counter->count;
            if (count0 == 2147483647) {
                abort();
            }
            counter->count = count0 + 1;
        }
        /*@
    }
    producing_box_predicate counter_box(counter, count0 + 1)
    producing_handle_predicate counter_box_handle(h);
    @*/
    //@ leak counter_box_handle(h, boxId);
    //@ close counter(counter, boxId)();
    lock_release(lock);
    //@ leak [_]lock(lock, _) &*& [_]counter->lock |-> _;
}

int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    struct counter *counter = malloc(sizeof(struct counter));
    if (counter == 0) {
        abort();
    }
    counter->count = 0;
    //@ create_box boxId = counter_box(counter, 0);
    //@ close counter(counter, boxId)();
    //@ close create_lock_ghost_arg(counter(counter, boxId));
    struct lock *lock = create_lock();
    //@ leak lock(lock, counter(counter, boxId));
    counter->lock = lock;
    //@ leak counter_lock(counter, lock);
    //@ close incrementor_session(counter, boxId);
    //@ close thread_run_data(incrementor)(counter);
    thread_start(incrementor, counter);
    
    lock_acquire(lock);
    //@ open counter(counter, boxId)();
    //@ handle h = create_handle counter_box_handle(boxId);
    /*@
    consuming_box_predicate counter_box(boxId, _, _)
    consuming_handle_predicate counter_box_handle(h)
    perform_action increase() {
        @*/ int count0 = counter->count; /*@
    }
    producing_box_predicate counter_box(counter, count0)
    producing_handle_predicate count_handle(h, count0);
    @*/
    //@ close counter(counter, boxId)();
    lock_release(lock);
    
    lock_acquire(lock);
    //@ open counter(counter, boxId)();
    /*@
    consuming_box_predicate counter_box(boxId, _, _)
    consuming_handle_predicate count_handle(h, count0)
    perform_action increase() {
        @*/ int count1 = counter->count; /*@
    }
    producing_box_predicate counter_box(counter, count1);
    @*/
    //@ close counter(counter, boxId)();
    lock_release(lock);
    
    assert(count0 <= count1);
    
    //@ leak [_]lock(lock, _) &*& [_]counter->lock |-> _ &*& malloc_block_counter(counter);
    return 0;
}