/*
  A Barrier Program Implemented by Condition Variables: Deadlock-free Verification
*/

#include "stdlib.h"
#include "monitors.h"

struct barrier {
   struct mutex *m;
   struct mutex_cond *v;
   int r;
};

/*@
predicate_ctor barrier(struct barrier *b)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  b->r |-> ?r &*& [_]b->v |-> ?v &*& [_]b->m |-> ?m &*& r >= 0 &*& mutex_of(v)==m &*& Trn(v) == vtrn &*&
  P(v)==false &*&
  Wt(v) <= 0 || 0 < r &*& 
  r  <= Ot(v);
@*/
  
/*@  
predicate_family_instance thread_run_data(wait_barrier_thread)(list<void*> tobs, struct barrier *b) =
   [_]b->m |-> ?m &*& [_]b->v |-> ?v &*& [_]mutex(m) &*& inv(m) == barrier(b)  &*& !eXc(v)
   &*& no_cycle(m,(cons(v,nil))) == true
   &*& tobs == cons(v,nil);
   
predicate vtrn() = true;

lemma void vtrn_lem(int n,struct mutex_cond *cond);
  requires true;
  ensures cond_trns(n,vtrn);

@*/

void wait_barrier(struct barrier *b)
    /*@ requires [_]b->m |-> ?m &*& [_]b->v |-> ?v &*& [_]mutex(m) &*& inv(m) ==  barrier(b)
          &*& !eXc(v) 
          &*& obs(cons(v,?O))
          &*& no_cycle(v,O) == true 
          &*& no_cycle(m,(cons(v,O))) == true;
    @*/    
    //@ ensures [_]b->m |-> m &*& [_]b->v |-> v &*& [_]mutex(m) &*& obs(O);
{
  //@ close mutex_inv(m,barrier(b));
  mutex_acquire(b->m);
  //@ open barrier(b)(?Wt1,?Ot1);
  if (b->r <= 0)
    abort();
  b->r = b->r - 1;
  if (b->r==0){
    //@ close cond_trn(v,vtrn);
    //@ vtrn_lem(Wt1(v),v);
    mutex_cond_broadcast(b->v);
    //@ g_dischl(v);
  }
  else {
    //@ g_dischl(v);
    while (b->r > 0)
      /*@ invariant [_]b->m |-> m &*& [_]b->v |-> v &*&  b->r |-> ?r &*& r>=0 &*& mutex_held(m, _, ?Wt, ?Ot) 
            &*& obs(cons(m,O)) 
            &*& Wt(v) <= 0 || 0 < r
            &*& r <= Ot(v);
      @*/
    {
      //@ close barrier(b)(finc(Wt,v),Ot);
      //@ close mutex_inv(m,barrier(b));
      //@ close cond_trn(v,vtrn);
      mutex_cond_wait(b->v, b->m);
      //@ open barrier(b)(_,_); 
      //@ open vtrn();   
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

void main()
    //@ requires obs(nil);
    //@ ensures obs(nil);
{
    //@ close create_mutex_ghost_args(0,nil);
    struct mutex *m = create_mutex();
    //@ close create_mutex_cond_ghost_args(m,1,false,vtrn);
    struct mutex_cond *v = create_mutex_cond();
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
}
