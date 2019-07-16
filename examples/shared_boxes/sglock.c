#include "stdlib.h"
#include "threading.h"
#include "malloc.h"

struct mylock {
    bool is_locked;
    struct mutex *mutex;
    //@ bool ghost_locked;
    //@ real frac;
    //@ bool help;
};

/*@
predicate_ctor mylock_ctor(struct mylock *lock, predicate() p)() =
    lock->ghost_locked |-> ?isLocked &*& 
        (isLocked 
            ? 
            [1/2]lock->is_locked |-> isLocked &*& [1/2]lock->frac |-> ?frac &*& [frac]lock->help |-> ?v
            : 
            lock->is_locked |-> isLocked &*& lock->frac |-> ?frac &*& p());

predicate mylock(struct mylock *lock, predicate() p;) = 
  malloc_block_mylock(lock) &*& 
  lock->mutex |-> ?mutex &*&
  mutex (mutex, (mylock_ctor (lock, p))) &*&
  lock->help |-> ?v;
  
predicate mylock_locked(struct mylock *lock, real f, predicate() p) = 
  [f]malloc_block_mylock(lock) &*& 
  [f]lock->mutex |-> ?mutex &*&
  [f]mutex (mutex, (mylock_ctor (lock, p))) &*&
  [1/2]lock->is_locked |-> true &*&
  [1/2]lock->frac |-> f;

predicate create_mylock_ghost_arg(predicate() p) = true;

@*/

struct mylock * mylock_create() 
    //@ requires create_mylock_ghost_arg(?p) &*& p();
    //@ ensures mylock(result, p);
{
    struct mylock *result = malloc(sizeof(struct mylock));
    if (result == 0) {
        abort();
    }
    result->is_locked = false;
    //@ result->ghost_locked = false;
    //@ close mylock_ctor(result, p)();
    //@ close create_mutex_ghost_arg(mylock_ctor(result, p));
    struct mutex* l = create_mutex();
    result->mutex = l;
    return result;
    //@ close mylock(result, p);
    //@ open create_mylock_ghost_arg(p);
}

void mylock_dispose(struct mylock *lock) 
    //@ requires mylock(lock, ?p);
    //@ ensures p();
{
    //@ open mylock(lock, p);
    struct mutex *mutex = lock->mutex;
    mutex_dispose(mutex);
    //@ open mylock_ctor (lock, p)();
    free (lock);
}

void mylock_acquire(struct mylock *lock) 
    //@ requires [?f]mylock(lock, ?p) ;
    //@ ensures mylock_locked(lock, f, p) &*& p();
{
    //@ open mylock(lock, p);
    struct mutex *mutex = lock->mutex;
    bool locked = false;
    
    while(!locked) 
    /*@ invariant [f]mutex(mutex, mylock_ctor (lock, p)) &*& 
                  (locked ? 
                      [1/2]lock->is_locked |-> true &*& [1/2]lock->frac |-> f &*& p()
                      : 
                      [f]lock->help |-> ?v);
                  @*/
    {
        mutex_acquire(mutex);
        //@ open mylock_ctor (lock, p)();
        bool is_locked = lock->is_locked;
        if(!is_locked) {
            lock->is_locked = true;
            //@ lock->ghost_locked = true;
            //@ lock->frac = f;
            locked = true;
        }       
        //@ close mylock_ctor (lock, p)();
        mutex_release(mutex);
    }
    //@ close mylock_locked(lock, f, p);    
}

void mylock_release(struct mylock *lock) 
    //@ requires mylock_locked(lock, ?f, ?p) &*& p();
    //@ ensures [f]mylock(lock, p);
{
    //@ open mylock_locked(lock, f, p);
    struct mutex *mutex = lock->mutex;
    mutex_acquire(mutex);
    //@ open mylock_ctor (lock, p)();
    bool is_still_locked = lock->is_locked;
    //@ assert is_still_locked;
    lock->is_locked = false;
    //@ lock->ghost_locked = false;
    //@ close mylock_ctor (lock, p)();
    mutex_release(mutex);
    //@ close [f]mylock(lock, p);
}




struct session {
    struct mylock *lock;
    int* data;
};

/*@
predicate_ctor datainv(int* p)() = integer(p, ?v);

inductive myinfo = myinfo (struct mylock *lock, int *data);

predicate_family_instance thread_run_pre(run)(struct session *session, myinfo info) = 
  switch (info) {
    case myinfo(lock, data): 
      return session_lock(session, lock) &*& session_data(session, data) &*& [1/2]mylock(lock, datainv(data));
  };
  
predicate_family_instance thread_run_post(run)(struct session *session, myinfo info) =
  switch (info) {
    case myinfo(lock, data): 
      return session_lock(session, lock) &*& session_data(session, data) &*& [1/2]mylock(lock, datainv(data));
  };

@*/


void run(void *sessionv) //@ : thread_run_joinable
    //@ requires thread_run_pre(run)(sessionv, ?info) &*& lockset(currentThread, nil);
    //@ ensures thread_run_post(run)(sessionv, info) &*& lockset(currentThread, nil);
{
    struct session *session = sessionv;
    //@ open thread_run_pre(run)(session, _);
    struct mylock *mylock = session->lock;
    int *data = session->data;
  
    mylock_acquire(mylock);
  
    // do something with locked data
    //@ open datainv (data)();
    int tmp = *data;
    //@ produce_limits(tmp); 
    if(tmp < 100) tmp++; 
    *data = tmp;
    //@ close datainv (data)();

    mylock_release(mylock);
    //@ close thread_run_post(run)(session, myinfo(mylock,data));
}


int main()
    //@ requires true;
    //@ ensures true;
{
    struct session * s = malloc(sizeof(struct session));
    if (s == 0) { abort(); }

    int * d = malloc(sizeof(int));
    if(d == 0) { abort(); }
    s -> data = d;

    //@ close create_mylock_ghost_arg(datainv(d));
    //@ close datainv(d)();
    struct mylock * ml = mylock_create();
    s -> lock = ml;

    // start thread
    //@ close thread_run_pre(run)(s, myinfo(ml,d));
    struct thread * t = thread_start_joinable(run, s);
    
    mylock_acquire(ml);
    
    //@ open datainv (d)();
    // do something with locked data
    int tmp = *d;
    //@ produce_limits(tmp); 
    if(tmp < 100) tmp++; 
    *d = tmp;
    //@ close datainv (d)();

    mylock_release(ml);

    thread_join(t);
    //@ open thread_run_post(run)(s, myinfo(ml,d));
    free(s);
    mylock_dispose(ml);
    //@ open datainv (d)();
    free (d);
    return 0;
}
