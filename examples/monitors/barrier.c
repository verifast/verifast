/*
  A Barrier Program Synchronized Using Monitors: Verification of Deadlock-Freedom
*/

#include "stdlib.h"
#include "monitors.h"

struct barrier {
   struct mutex *m;
   struct condvar *v;
   int r;
};

/*@
predicate_ctor barrier(struct barrier *b)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  b->r |-> ?r &*& 
  [_]b->v |-> ?v &*& 
  [_]b->m |-> ?m &*& 
  r >= 0 &*& 
  mutex_of(v)==m &*& 
  Trn(v) == no_transfer &*&
  P(v)==false &*&
  Wt(v) <= 0 || 0 < r &*& 
  r <= Ot(v);
@*/
  
/*@  
predicate_family_instance thread_run_data(wait_barrier_thread)(list<void*> tobs, struct barrier *b) =
   [_]b->m |-> ?m &*& 
   [_]b->v |-> ?v &*& 
   [_]mutex(m) &*& 
   inv(m) == barrier(b) &*& 
   !eXc(v) &*& 
   no_cycle(m,(cons(v,nil))) == true &*&
   tobs == cons(v,nil);
@*/

void wait_barrier(struct barrier *b)
  /*@ requires [_]b->m |-> ?m &*&
               [_]b->v |-> ?v &*& 
               [_]mutex(m) &*& 
               inv(m) ==  barrier(b) &*&
               !eXc(v) &*&
               obs(cons(v,?O)) &*&
               no_cycle(v,O) == true &*&
               no_cycle(m,(cons(v,O))) == true; @*/    
  /*@ ensures [_]b->m |-> m &*& 
              [_]b->v |-> v &*& 
              [_]mutex(m) &*& 
              obs(O); @*/
{
  //@ close mutex_inv(m,barrier(b));
  mutex_acquire(b->m);
  //@ open barrier(b)(?Wt1,?Ot1);
  if (b->r <= 0)
    abort();
  b->r = b->r - 1;
  if (b->r==0){
    //@ close condvar_trn(v,no_transfer);
    //@ n_times_no_transfer(Wt1(v));
    condvar_broadcast(b->v);
    //@ g_dischl(v);
  }
  else {
    //@ g_dischl(v);
    while (b->r > 0)
      /*@ invariant [_]b->m |-> m &*& 
                    [_]b->v |-> v &*&  
                    b->r |-> ?r &*& 
                    r>=0 &*& 
                    mutex_held(m, _, ?Wt, ?Ot) &*&
                    obs(cons(m,O)) &*&
                    Wt(v) <= 0 || 0 < r &*&
                    r <= Ot(v); @*/
    {
      //@ close barrier(b)(finc(Wt,v),Ot);
      //@ close mutex_inv(m,barrier(b));
      //@ close condvar_trn(v,no_transfer);
      condvar_wait(b->v, b->m);
      //@ open barrier(b)(_,_); 
      //@ open no_transfer();   
    }
}
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close barrier(b)(Wte,Ote);
  //@ close mutex_inv(m,barrier(b));  
  mutex_release(b->m);
  //@ leak [_]mutex(m);
}

void wait_barrier_thread(struct barrier *b)  //@ : thread_run
  //@ requires thread_run_data(wait_barrier_thread)(?tobs,b) &*& obs(tobs);
  //@ ensures obs(nil);
{
  //@ open thread_run_data(wait_barrier_thread)(_,_);
  wait_barrier(b);
}

int main() //@ : custom_main_spec
  //@ requires obs(nil);
  //@ ensures obs(nil);
{
  //@ close create_mutex_ghost_args(0,nil);
  struct mutex *m = create_mutex();
  //@ close create_condvar_ghost_args(m,1,false,no_transfer);
  struct condvar *v = create_condvar();
  struct barrier *b = malloc(sizeof(struct barrier));
  if (b==0)
    abort();      
  b->r = 3;
  b->m = m;
  b->v = v;
  //@ leak [_]barrier_m(_,_);
  //@ leak [_]barrier_v(_,_);
  //@ leak [_]malloc_block_barrier(_);
  //@ close init_mutex_ghost_args(barrier(b));
  //@ close barrier(b)(empb,finc(finc(finc(empb,v),v),v));
  //@ g_chrgu(v); 
  //@ g_chrgu(v);    
  //@ g_chrgu(v);     
  //@ init_mutex(m);
  //@ leak [_]mutex(m);
  
  //@ close thread_run_data(wait_barrier_thread)(cons(b->v,nil),b);   
  thread_start(wait_barrier_thread, b);
  //@ close thread_run_data(wait_barrier_thread)(cons(b->v,nil),b);
  thread_start(wait_barrier_thread, b);
  //@ close thread_run_data(wait_barrier_thread)(cons(b->v,nil),b);
  thread_start(wait_barrier_thread, b);

  return 0;
}
