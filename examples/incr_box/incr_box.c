#include "stdlib.h"
#include "threading.h"

struct counter {
    int count;
    struct lock *lock;
};

/*@

box_class counter_box(int count) {

    action increase();
        requires true;
        ensures old_count <= count;
    
    handle_predicate count_handle(int count0) {
        invariant count0 <= count;
        
        preserved_by increase() {
        }
    }
}

predicate_ctor counter(struct counter *counter, box boxId)()
    requires counter->count |-> ?count &*& counter_box(boxId, count);

lemma real counter_lock_split_fractions(struct counter *counter);
    requires [?f]counter->lock |-> ?lock;
    ensures [result]counter->lock |-> lock &*& [f - result]counter->lock |-> lock;

predicate incrementor_session(struct counter *counter, box boxId)
    requires [?f]counter->lock |-> ?lock &*& lock_permission(lock, counter(counter, boxId));

predicate_family_instance thread_run_data(incrementor)(void *data)
    requires incrementor_session(data, _);
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
    //@ open_lock_invariant();
    //@ open counter(counter, boxId)();
    int count0 = counter->count;
    if (count0 == 2147483647) {
        abort();
    }
    //@ assume_is_int(count0);
    counter->count = count0 + 1;
    //@ handle h = create_counter_box_handle(boxId);
    /*@
    consuming_box_predicate counter_box(boxId, count0)
    consuming_handle_predicate counter_box_handle(h)
    perform_action increase() {
    }
    producing_box_predicate counter_box(count0 + 1)
    producing_handle_predicate counter_box_handle();
    @*/
    //@ leak counter_box_handle(h, boxId);
    //@ close counter(counter, boxId)();
    //@ close_lock_invariant(counter(counter, boxId));
    lock_release(lock);
    //@ leak lock_permission(lock, _) &*& [_]counter->lock |-> _;
}

int main()
    //@ requires true;
    //@ ensures true;
{
    struct counter *counter = malloc(sizeof(struct counter));
    if (counter == 0) {
        abort();
    }
    counter->count = 0;
    //@ box boxId = create_counter_box(0);
    //@ close counter(counter, boxId)();
    //@ close_lock_invariant(counter(counter, boxId));
    struct lock *lock = create_lock();
    //@ split_lock_permission(lock);
    counter->lock = lock;
    //@ real f = counter_lock_split_fractions(counter);
    //@ close incrementor_session(counter, boxId);
    //@ close thread_run_data(incrementor)(counter);
    thread_start(incrementor, counter);
    
    lock_acquire(lock);
    //@ open_lock_invariant();
    //@ open counter(counter, boxId)();
    //@ handle h = create_counter_box_handle(boxId);
    int count0 = counter->count;
    /*@
    consuming_box_predicate counter_box(boxId, count0)
    consuming_handle_predicate counter_box_handle(h)
    perform_action increase() {
    }
    producing_box_predicate counter_box(count0)
    producing_handle_predicate count_handle(count0);
    @*/
    //@ close counter(counter, boxId)();
    //@ close_lock_invariant(counter(counter, boxId));
    lock_release(lock);
    
    lock_acquire(lock);
    //@ open_lock_invariant();
    //@ open counter(counter, boxId)();
    int count1 = counter->count;
    /*@
    consuming_box_predicate counter_box(boxId, count1)
    consuming_handle_predicate count_handle(h, count0)
    perform_action increase() {
    }
    producing_box_predicate counter_box(count1)
    producing_handle_predicate counter_box_handle();
    @*/
    //@ leak counter_box_handle(h, boxId);
    //@ close counter(counter, boxId)();
    //@ close_lock_invariant(counter(counter, boxId));
    lock_release(lock);
    
    assert(count0 <= count1);
    
    //@ leak lock_permission(lock, _) &*& [_]counter->lock |-> _ &*& malloc_block_counter(counter);
    return 0;
}