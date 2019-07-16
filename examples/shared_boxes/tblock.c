#include "stdlib.h"
#include "threading.h"
#include "malloc.h"
//@ #include "listex.gh"

struct tlock {
    int next;
    int owner;
    
    struct mutex *mutex;
    //@ box boxId;
    //@ real frac; //used to store the fraction of help which is in the box
    //@ bool help;
};

/*@

//Some lemma's about lists

lemma void nth_zero<t>(list<t> l) 
  requires length(l) > 0;
  ensures nth(0, l) == head(l);
{
  switch (l) {
    case nil: 
    case cons(x0, xs0): 
  }
}
 
lemma void nth_tail<t>(int i, list<t> l) 
  requires i > 0;
  ensures nth(i-1, tail(l)) == nth(i,l);
{
  switch (l) {
    case nil: 
    case cons(x0, xs0): 
  }
}
  
lemma void length_tail<t>(list<t> l) 
  requires length(l) > 0;
  ensures length(tail(l)) == length (l) - 1;
{
  switch (l) {
    case nil: 
    case cons(x0, xs0): 
  }
}

lemma void distinct_tail<t>(list<t> l) 
  requires distinct(l) == true;
  ensures distinct(tail(l)) == true;
{
  switch (l) {
    case nil: 
    case cons(x0, xs0): 
  }
}

fixpoint list<t> snoc<t>(list<t> l, t n) {
    return append(l, cons(n, nil));
}

lemma void distinct_snoc<t>(list<t> l, t el);
    requires mem(el, l) == false;
    ensures distinct(snoc(l, el)) == true;

lemma void nth_snoc_length<t>(list<t> l, t el);
    requires true;
    ensures nth(length(l), snoc(l, el)) == el;


@*/





/*@
box_class tlock_box(struct tlock *lock, int next, int owner, bool locked, list<handle> thandles, predicate() p) {
    invariant lock->next |-> next &*& 
              lock->owner |-> owner &*& 
              owner <= next &*&
              (next == owner ? !locked : true) &*&
              length (thandles) == next - owner &*&
              (locked ? [1/2]lock->frac |-> ?frac &*& [frac]lock->help |-> ?v : p() &*& lock->frac |-> ?frac);

    action get_ticket();
    	requires true;
    	ensures next == old_next + 1 && owner == old_owner && locked == old_locked && 
    		thandles == snoc(old_thandles, head(actionHandles)) && p == old_p;

    action try_acquire(int ticket);
    	requires owner <= ticket;
        ensures next == old_next && owner == old_owner && p == old_p && thandles == old_thandles &&
                ( owner == ticket && actionHandles == cons(nth (0, thandles), nil) ? locked : locked == old_locked );

    action release(int ticket);
        requires locked && owner == ticket && actionHandles == cons(nth (0, thandles), nil);
        ensures next == old_next && owner == old_owner + 1 && p == old_p && 
    		thandles == tail (old_thandles) && !locked;

    handle_predicate tlock_ticket(int ticket, bool isLocked) {
        invariant owner <= ticket && 
        	  ticket < next && 
                  length(thandles) >= ticket - owner + 1 &&  //TODO check if this is necessary
                  nth (ticket - owner, thandles) == predicateHandle &&
                  (ticket == owner ? isLocked == locked : !isLocked);
        
        preserved_by get_ticket() {
           nth_append(old_thandles, cons(head(actionHandles), nil), ticket - owner);
        }
        preserved_by try_acquire(t) {
        }
        preserved_by release(t) {
            if (t != ticket) {
                nth_tail(ticket-old_owner, old_thandles);
            }
        }
    }    
}

 
predicate_ctor tlock_ctor(struct tlock *lock, box boxId, predicate() p)() =
  tlock_box(boxId, lock, ?next, ?owner, ?locked, ?thandles, p);

predicate tlock(struct tlock *lock, predicate() p;) = 
  tlock_mutex (lock, ?mutex) &*& 
  tlock_boxId (lock, ?boxId)  &*&
  mutex (mutex, (tlock_ctor (lock, boxId, p))) &*&
  malloc_block_tlock(lock) &*&
  lock->help |-> ?v;

predicate tlock_locked(struct tlock *lock, real f, predicate() p) = 
  [f]tlock_mutex (lock, ?mutex) &*& 
  [f]tlock_boxId (lock,  ?boxId)  &*&
  [f]mutex (mutex, (tlock_ctor (lock, boxId, p))) &*&
  [f]malloc_block_tlock(lock) &*&
  tlock_ticket(?h, boxId, ?ticket, true) &*&
  [1/2]lock->frac |-> f;

predicate create_tlock_ghost_arg(predicate() p) = true;

@*/

struct tlock * mylock_create() 
    //@ requires create_tlock_ghost_arg(?p) &*& p();
    //@ ensures tlock(result, p);
{
    struct tlock *result = malloc(sizeof(struct tlock));
    if (result == 0) {
        abort();
    }
    result->owner = 0;
    result->next = 0;
    //@ create_box boxId = tlock_box(result, 0, 0, false, nil, p); 
    //@ close tlock_ctor(result, boxId, p)();
    //@ result->boxId = boxId;
    //@ close create_mutex_ghost_arg(tlock_ctor(result, boxId, p));
    struct mutex* l = create_mutex();
    result->mutex = l;
    return result;
    //@ close tlock(result, p);
    //@ open create_tlock_ghost_arg(p);
}

void mylock_dispose(struct tlock *lock) 
    //@ requires tlock(lock, ?p);
    //@ ensures p();
{
    //@ open tlock(lock, p);
    struct mutex *mutex = lock->mutex;
    mutex_dispose(mutex);
    //@ box boxId = lock->boxId; 
    //@ open tlock_ctor (lock, boxId, p)();
    //@ dispose_box tlock_box(boxId, lock, ?next, ?owner, ?locked, ?th, p);
    //@ assert (!locked);
    free (lock);
}

void tlock_acquire(struct tlock *lock) 
    //@ requires [?f]tlock(lock, ?p) &*& 0 < f;
    //@ ensures tlock_locked(lock, f, p) &*& p();
{
    //@ open tlock(lock, p);
    struct mutex *mutex = lock->mutex;
    //@ box boxId = lock->boxId;

    // reserve ticket
    int ticket = 0;
    mutex_acquire(mutex);
    //@ open tlock_ctor (lock, boxId, p)();
    //@ handle h = create_handle tlock_box_handle(boxId);
    /*@
        consuming_box_predicate tlock_box(boxId, lock, ?next, ?owner, ?b_locked, ?th, p)
        consuming_handle_predicate tlock_box_handle(h)
        perform_action get_ticket() {
    @*/
    {
        ticket = lock->next;
        if (ticket == INT_MAX) abort();
        lock->next = ticket + 1;
        //@ nth_snoc_length(th, h);
    }
    /*@
        }
        producing_box_predicate tlock_box(lock, next+1, owner, b_locked, snoc(th, h), p)
        producing_handle_predicate tlock_ticket(h, ticket, false);
    @*/
    //@ close tlock_ctor (lock, boxId, p)();
    mutex_release(mutex);
    
    
    // wait for ticket
    bool locked = false;
    while(!locked) 
    /*@ invariant [f]mutex(mutex, tlock_ctor(lock, boxId, p)) &*& tlock_ticket(h, boxId, ticket, locked) &*&
                  (locked ? [1/2]lock->frac |-> f &*& p(): [f]lock->help |-> ?v);
   
   @*/
    {
        mutex_acquire(mutex);
        //@ open tlock_ctor (lock, boxId, p)();
        /*@
            consuming_box_predicate tlock_box(boxId, lock, ?next2, ?owner2, ?b_locked2, ?th2, p)
            consuming_handle_predicate tlock_ticket(h, ticket, false)
            perform_action try_acquire(ticket) {
        @*/
        {
	    if(lock->owner == ticket) {
 	        locked = true;
 	        //@ lock->frac = f;
            }
        }
        /*@
            }
            producing_box_predicate tlock_box(lock, next2, owner2, (locked ? true : b_locked2), th2, p)
            producing_handle_predicate tlock_ticket(h, ticket, locked);
        @*/

        //@ close tlock_ctor (lock, boxId, p)();
        mutex_release(mutex);
    }
    //@ close tlock_locked(lock, f, p);    
}

void tlock_release(struct tlock *lock) 
    //@ requires tlock_locked(lock, ?f, ?p) &*& p();
    //@ ensures [f]tlock(lock, p);
{
    //@ open tlock_locked(lock, f, p);
    struct mutex *mutex = lock->mutex;
    //@ box boxId = lock->boxId;
    mutex_acquire(mutex);
    //@ open tlock_ctor (lock, boxId, p)();
    /*@
        consuming_box_predicate tlock_box(boxId, lock, ?next2, ?owner2, ?b_locked2, ?th, p)
        consuming_handle_predicate tlock_ticket(?h, ?ticket, true)
        perform_action release(ticket) {
    @*/
    {
	lock->owner++;
	
	// distinct_tail(th);
	//@ length_tail(th);
    }
    /*@
        }
        producing_box_predicate tlock_box(lock, next2, owner2+1, false, tail(th), p);
    @*/
    //@ close tlock_ctor (lock, boxId, p)();
    mutex_release(mutex);
    //@ close [f]tlock(lock, p);
}



struct session {
    struct tlock *lock;
    int* data;
};

/*@
predicate_ctor datainv(int* p)() = integer(p, ?v);

inductive myinfo = myinfo (struct tlock *lock, int *data);

predicate_family_instance thread_run_pre(run)(struct session *session, myinfo info) = 
  switch (info) {
    case myinfo(lock, data): 
      return session_lock(session, lock) &*& session_data(session, data) &*& [1/2]tlock(lock, datainv(data));
  };
  
predicate_family_instance thread_run_post(run)(struct session *session, myinfo info) =
  switch (info) {
    case myinfo(lock, data): 
      return session_lock(session, lock) &*& session_data(session, data) &*& [1/2]tlock(lock, datainv(data));
  };

@*/


void run(void *sessionv) //@ : thread_run_joinable
    //@ requires thread_run_pre(run)(sessionv, ?info) &*& lockset(currentThread, nil);
    //@ ensures thread_run_post(run)(sessionv, info) &*& lockset(currentThread, nil);
{
    struct session *session = sessionv;
    //@ open thread_run_pre(run)(session, _);
    struct tlock *lock = session->lock;
    int *data = session->data;
  
    tlock_acquire(lock);
  
    // do something with locked data
    //@ open datainv (data)();
    int tmp = *data;
    //@ produce_limits(tmp); 
    if(tmp < 100) tmp++; 
    *data = tmp;
    //@ close datainv (data)();

    tlock_release(lock);
    //@ close thread_run_post(run)(session, myinfo(lock,data));
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

    //@ close create_tlock_ghost_arg(datainv(d));
    //@ close datainv(d)();
    struct tlock * ml = mylock_create();
    s -> lock = ml;

    // start thread
    //@ close thread_run_pre(run)(s, myinfo(ml,d));
    struct thread * t = thread_start_joinable(run, s);
    
    tlock_acquire(ml);
    
    //@ open datainv (d)();
    // do something with locked data
    int tmp = *d;
    //@ produce_limits(tmp); 
    if(tmp < 100) tmp++; 
    *d = tmp;
    //@ close datainv (d)();

    tlock_release(ml);

    thread_join(t);
    //@ open thread_run_post(run)(s, myinfo(ml,d));
    free(s);
    mylock_dispose(ml);
    //@ open datainv (d)();
    free (d);
    return 0;
}
