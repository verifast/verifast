#include "stdlib.h"
#include "threading.h"

struct counter {
    struct mutex *mutex;
    int count;
    //@ box boxId;
};

/*@

box_class counter_box(struct counter *ctr, int c) {
    invariant ctr->count |-> c;

    action observe();
    	requires true;
    	ensures c == old_c;

    action increase(int v);
    	requires c <= v;
        ensures c == v;

    handle_predicate oldcount_handle(int v) {
        invariant v <= c; 
        
        preserved_by observe() {
        }
        preserved_by increase(v2) {
        }
    }    
}        
predicate_ctor lock_invariant(struct counter *counter, box boxId)() = counter_box(boxId, counter, ?count);

predicate_family_instance thread_run_data(incrementor)(struct counter *counter) =
    [_]counter->mutex |-> ?mutex &*& [_]counter->boxId |-> ?boxId &*& 
    [_]mutex(mutex, lock_invariant(counter, boxId));

predicate_family_instance thread_run_data(observer)(struct counter *counter) =
    [_]counter->mutex |-> ?mutex &*& [_]counter->boxId |-> ?boxId &*& 
    [_]mutex(mutex, lock_invariant(counter, boxId));

@*/

void incrementor(struct counter *counter) //@ : thread_run
    //@ requires thread_run_data(incrementor)(counter);
    //@ ensures true;
{
    //@ open thread_run_data(incrementor)(counter);
    //@ box boxId = counter->boxId;
    struct mutex *mutex = counter->mutex;
    for (;;)
        //@ invariant [?f]mutex(mutex, lock_invariant(counter, boxId));
    {
        mutex_acquire(mutex);
        //@ open lock_invariant(counter, boxId)();
        
        //@ handle h = create_handle counter_box_handle(boxId);
        /*@
            consuming_box_predicate counter_box(boxId, counter, ?c)
            consuming_handle_predicate counter_box_handle(h)
            perform_action increase(c+1) {
        @*/
        {
            if (counter->count == INT_MAX) abort();
            counter->count++;
	}
        /*@
            }
            producing_box_predicate counter_box(counter, c + 1)
            producing_handle_predicate counter_box_handle();
        @*/
        //@ leak counter_box_handle(h, boxId);
        
        //@ close lock_invariant(counter, boxId)();
        mutex_release(mutex);
    }
}

void observer(struct counter *counter) //@ : thread_run
    //@ requires thread_run_data(observer)(counter);
    //@ ensures true;
{
    //@ open thread_run_data(observer)(counter);
    //@ box boxId = counter->boxId;
    struct mutex *mutex = counter->mutex;

    int oldCount = 0;
    //note: loop unrolled + simplified => code duplication
    //reason: no consuming_handle_predicate does not allow conditional constructionss
    mutex_acquire(mutex);
    //@ open lock_invariant(counter, boxId)();
    //@ handle h = create_handle counter_box_handle(boxId);
    /*@
        consuming_box_predicate counter_box(boxId, counter, ?c)
        consuming_handle_predicate counter_box_handle(h)
        perform_action observe() {
    @*/
    {
        oldCount = counter->count;
    }
    /*@ }
        producing_box_predicate counter_box(counter, c)
        producing_handle_predicate oldcount_handle(c);
    @*/
    //@ close lock_invariant(counter, boxId)();
    mutex_release(mutex);
  
    for(;;) 
        /*@ invariant [?f]mutex(mutex, lock_invariant(counter, boxId)) &*& oldcount_handle(?h2, boxId, oldCount);
        @*/
    {
        mutex_acquire(mutex);
        //@ open lock_invariant(counter, boxId)();

        /*@
            consuming_box_predicate counter_box(boxId, counter, ?c2)
            consuming_handle_predicate oldcount_handle(h2, oldCount)
            perform_action observe() {
        @*/
        {
            int count = counter->count;
            assert(count >= oldCount);
            oldCount = count;
        }
        /*@
            }
            producing_box_predicate counter_box(counter, c2)
            producing_handle_predicate oldcount_handle(c2);
        @*/
        
        //@ close lock_invariant(counter, boxId)();
        mutex_release(mutex);
    }
}


int main() //@ : main
    //@ requires true;
    //@ ensures true;
{
    int ni = 1; //number of incrementors
    int no = 2; //number of observers

    struct counter *counter = malloc(sizeof(struct counter));
    if (counter == 0) abort();
    counter->count = 0;
    //@ create_box boxId = counter_box(counter, 0); 
    //@ close lock_invariant(counter, boxId)();
    //@ counter->boxId = boxId;
    //@ close create_mutex_ghost_arg(lock_invariant(counter, boxId));
    struct mutex *mutex = create_mutex();
    counter->mutex = mutex;
    //@ leak counter->boxId |-> boxId;
    //@ leak counter->mutex |-> mutex;
    //@ leak mutex(mutex, (lock_invariant(counter, boxId)));
    
    for(int i=0;i<ni;i++)
    /*@ invariant [_]counter->mutex |-> mutex &*& [_]counter->boxId |-> boxId &*& 
           [_]mutex(mutex, (lock_invariant(counter, boxId))); 
    @*/
    {
      //@ close thread_run_data(incrementor)(counter);
      thread_start(incrementor, counter);
    }
    for(int i=0;i<no;i++) 
    /*@ invariant [_]counter->mutex |-> mutex &*& [_]counter->boxId |-> boxId &*& 
           [_]mutex(mutex, (lock_invariant(counter, boxId))); @*/
    {
      //@ close thread_run_data(observer)(counter);
      thread_start(observer, counter);
    }
    for(;;)
    //@ invariant true;
    {
    }
}