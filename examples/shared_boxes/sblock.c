#include "stdlib.h"
#include "threading.h"
#include "malloc.h"

struct mylock {
    bool is_locked;
    struct mutex *mutex;
    //@ box mybox;
    //@ int help;
};

/*@

box_class mylock_box(struct mylock *mylock, bool is_locked, real myf, handle owner, predicate() p) {
    invariant mylock->is_locked |-> is_locked &*& 
              0 < myf &*&
              (is_locked ? 
                  [myf]mylock->help |-> ?v 
                  : p());

    action try_acquire(real f);
        requires true;
        ensures (old_is_locked ? 
                    is_locked && owner == old_owner && myf == old_myf : 
                    cons(owner, nil) == actionHandles && is_locked && myf == f) 
                && old_p == p;
        
    action release();
        requires cons(owner, nil) == actionHandles && is_locked;
        ensures !is_locked && old_p == p;
    
    handle_predicate mylock_handle(bool has_lock, real f) {
        invariant (has_lock ? owner == predicateHandle && is_locked && myf == f : true);
        
        preserved_by try_acquire(f0) {
        }
        preserved_by release() {
        }
    }
}

predicate_ctor mylock_ctor(struct mylock *mylock, box boxId, predicate() p)() =
  mylock_box(boxId, mylock, ?islocked, ?f, ?h, p);

predicate mylock(struct mylock *mylock, predicate() p;) = 
  mylock_mutex (mylock, ?mutex) &*&
  mylock_mybox (mylock,  ?boxId)  &*&
  mylock_help (mylock, ?help) &*&
  mutex (mutex, (mylock_ctor (mylock, boxId, p))) &*&
  malloc_block_mylock(mylock) ;
  
predicate mylock_locked(struct mylock *mylock, real f, predicate() p) = 
  [f]mylock_mutex (mylock, ?mutex) &*&
  [f]mylock_mybox (mylock,  ?boxId)  &*&
  mylock_handle(?h, boxId, true, f) &*&
  [f]mutex (mutex, (mylock_ctor (mylock, boxId, p))) &*&
  [f]malloc_block_mylock(mylock) ;

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
    //@ create_box boxId = mylock_box(result, false, 1, h, p) and_handle h = mylock_handle(false, 1); 
    //@ close mylock_ctor(result, boxId, p)();
    //@ result->mybox=boxId;
    //@ close create_mutex_ghost_arg(mylock_ctor(result, boxId, p));
    struct mutex* l = create_mutex();
    result->mutex = l;
    return result;
    //@ close mylock(result, p);
    //@ leak mylock_handle(_,_,_,_);
    //@ open create_mylock_ghost_arg(p);
}

void mylock_dispose(struct mylock *mylock) 
    //@ requires mylock(mylock, ?p);
    //@ ensures p();
{
    //@ open mylock(mylock, p);
    struct mutex *mutex = mylock->mutex;
    mutex_dispose(mutex);
    //@ box mybox = mylock -> mybox;
    //@ open mylock_ctor (mylock,mybox, p)();
    //@ dispose_box mylock_box(mybox,mylock, ?waslocked, ?f, ?h, p);
    free (mylock);
}

//@ predicate mylock_help_hidden (struct mylock *mylock, real f) = [f]mylock_help(mylock, _);

void mylock_acquire(struct mylock *mylock) 
    //@ requires [?f]mylock(mylock, ?p) &*& 0 < f;
    //@ ensures mylock_locked(mylock, f, p) &*& p();
{
    //@ open mylock(mylock, p);
    struct mutex *mutex = mylock->mutex;
    //@ box mybox = mylock -> mybox;
    bool locked = false;
    
    while(!locked) 
    /*@ invariant [f]mutex(mutex,mylock_ctor (mylock,mybox, p)) &*& 
         (locked ? mylock_handle(_,mybox,true,f) &*& p(): [f]mylock_help(mylock,_) &*& 0 < f);
         @*/
    {
        mutex_acquire(mutex);
        //@ open mylock_ctor (mylock, mybox, p)();
        //@ handle h = create_handle mylock_box_handle(mybox);
        
        /*@
            consuming_box_predicate mylock_box(mybox, mylock, ?a, ?oldf, ?b, p)
            consuming_handle_predicate mylock_box_handle(h)
            perform_action try_acquire(f) {
        @*/
        {
            bool is_locked = mylock->is_locked;
            if(!is_locked) {
                mylock->is_locked = true;
                locked = true;
            }
            //@ if(!locked) close mylock_help_hidden(mylock, f);
        }
        /*@
            }
            producing_box_predicate mylock_box(mylock, true, (locked ? f: oldf), (locked ? h : b),  p)
            producing_handle_predicate mylock_handle(h, locked, f);
        @*/
       
        //@ close mylock_ctor (mylock, mybox, p)();
       
       //@ if(!locked) open mylock_help_hidden(mylock, f);
       //@ if(!locked) leak mylock_handle(_,_,_,_);
       
       mutex_release(mutex);
    }
    //@ close mylock_locked(mylock, f, p);    
}

void mylock_release(struct mylock *mylock) 
    //@ requires mylock_locked(mylock, ?f, ?p) &*& p();
    //@ ensures [f]mylock(mylock, p);
{
    //@ open mylock_locked(mylock, f, p);
    struct mutex *mutex = mylock->mutex;
    //@ box mybox = mylock -> mybox;
    mutex_acquire(mutex);
    //@ open mylock_ctor (mylock, mybox, p)();

    //@ assert mylock_handle(?h,mybox,true,f);
    /*@
        consuming_box_predicate mylock_box(mybox, mylock, ?a, ?oldf, ?b, p)
        consuming_handle_predicate mylock_handle(h, true, f)
        perform_action release() {
    @*/
    {
        bool is_still_locked = mylock->is_locked;
        assert is_still_locked;
        mylock->is_locked = false;
    }
    /*@
        }
        producing_box_predicate mylock_box(mylock, false, oldf, h, p)
        producing_handle_predicate mylock_handle(h, false, oldf);
    @*/
    //@ close mylock_ctor (mylock, mybox, p)();
    mutex_release(mutex);
    //@ close [f]mylock(mylock, p);
    //@ leak mylock_handle(_,_,_,_);
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
