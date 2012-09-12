#include "stdlib.h"
#include "threading.h"
//@ #include "list.gh"
//@ #include "raw_ghost_lists.gh"

struct counter {
    struct mutex *mutex;
    int count;
    //@ int oldCountsId;
};

/*@
predicate_ctor oldCountCondition(int count)(pair<int, int> p) =
    snd(p) <= count;
    
predicate_ctor lock_invariant(struct counter *counter)() =
    counter->count |-> ?count &*&
    [_]counter->oldCountsId |-> ?id &*& 
    raw_ghost_list(id, ?n, ?oldCounts) &*&
    foreach(oldCounts, oldCountCondition(count));

predicate_family_instance thread_run_data(incrementor)(struct counter *counter) =
    [_]counter->mutex |-> ?mutex &*& [_]mutex(mutex, lock_invariant(counter));

predicate_family_instance thread_run_data(observer)(struct counter *counter) =
    [_]counter->oldCountsId |-> ?oldCountsId &*& [_]counter->mutex |-> ?mutex &*& [_]mutex(mutex, lock_invariant(counter));

lemma void count_update(int c, list<pair<int,int> > l) 
    requires foreach(l, oldCountCondition(c));
    ensures foreach(l, oldCountCondition(c+1));
{
    open foreach(l, oldCountCondition(c));
    switch(l) {
        case nil: 
        case cons(hl,tl):
            open oldCountCondition(c)(hl);
            close oldCountCondition(c+1)(hl);
            count_update(c, tl);
    }
    close foreach(l, oldCountCondition(c+1));
}
@*/

void incrementor(struct counter *counter) //@ : thread_run
    //@ requires thread_run_data(incrementor)(counter);
    //@ ensures true;
{
    //@ open thread_run_data(incrementor)(counter);
    struct mutex *mutex = counter->mutex;
    for (;;)
        //@ invariant [?f]mutex(mutex, lock_invariant(counter));
    {
        mutex_acquire(mutex);
        //@ open lock_invariant(counter)();
        //@ int oldCount = counter->count;
        if (counter->count == INT_MAX) abort();
        counter->count++;
        //@ int oldCountsId = counter->oldCountsId;
        //@ assert raw_ghost_list(oldCountsId, ?n, ?oldCounts);
        //@ count_update(oldCount, oldCounts);
        //@ close lock_invariant(counter)();
        mutex_release(mutex);
    }
}

void observer(struct counter *counter) //@ : thread_run
    //@ requires thread_run_data(observer)(counter);
    //@ ensures true;
{
    //@ open thread_run_data(observer)(counter);
    struct mutex *mutex = counter->mutex;
    bool oldCountOk = false;
    int oldCount = 0;

    for(;;) 
        /*@ invariant [_]counter->oldCountsId |-> ?oldCountsId &*& [?f]mutex(mutex, lock_invariant(counter)) &*&
                      (oldCountOk ? raw_ghost_list_member_handle(oldCountsId, ?k, oldCount) : true);
        @*/
    {
        mutex_acquire(mutex);
        //@ open lock_invariant(counter)();
        //@ assert raw_ghost_list(oldCountsId, ?n, ?oldCounts);
        int count = counter->count;
        if(oldCountOk) {
            //@ assert raw_ghost_list_member_handle(oldCountsId, ?k, oldCount);
            //@ raw_ghost_list_match(oldCountsId, k);
            //@ foreach_remove(pair(k,oldCount), oldCounts);
            //@ open oldCountCondition(count)(pair(k,oldCount));
            assert(count >= oldCount);
            //@ raw_ghost_list_remove(oldCountsId, k);
        }
        oldCount = count;
        oldCountOk = true;
        //@ assert raw_ghost_list(oldCountsId, ?n2, ?oldCounts2); 
        //@ assert foreach(oldCounts2, oldCountCondition(count));
        //@ raw_ghost_list_add(oldCountsId, oldCount);
        //@ assert raw_ghost_list_member_handle(oldCountsId, ?k2, count);
        //@ close oldCountCondition(count)(pair(k2, count));
        //@ close foreach(nil, oldCountCondition(count));
        //@ close foreach(cons(pair(k2, count), nil), oldCountCondition(count));
        //@ foreach_append(oldCounts2, cons(pair(k2, count), nil));
        //@ close lock_invariant(counter)();
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
    //@ int oldCountsId = create_raw_ghost_list();
    //@ counter->oldCountsId = oldCountsId;
    //@ leak counter->oldCountsId |-> oldCountsId;
    //@ close foreach(nil, oldCountCondition(0));
    //@ close lock_invariant(counter)();
    //@ close create_mutex_ghost_arg(lock_invariant(counter));
    struct mutex *mutex = create_mutex();
    counter->mutex = mutex;

        
    //@ leak counter->mutex |-> mutex;
    //@ leak mutex(mutex, (lock_invariant(counter)));
    
    for(int i=0;i<ni;i++)
    //@ invariant [_]counter->mutex |-> mutex &*& [_]mutex(mutex, (lock_invariant(counter))); 
    {
      //@ close thread_run_data(incrementor)(counter);
      thread_start(incrementor, counter);
    }
    for(int i=0;i<no;i++) 
    /*@ invariant [_]counter->mutex |-> mutex &*& [_]counter->oldCountsId |-> oldCountsId &*&
           [_]mutex(mutex, (lock_invariant(counter))); @*/
    {
      //@ close thread_run_data(observer)(counter);
      thread_start(observer, counter);
    }
    for(;;)
    //@ invariant true;
    {
    }
}