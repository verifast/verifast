/*
  A Buffer Program Synchronized Using Monitors: Verification of Deadlock-Freedom
*/

#include "stdlib.h"
#include "monitors.h"
#include "queues.h"
//@ #include "ghost_counters.gh"

struct buffer {
   struct queue *q;
   struct mutex *m;
   struct condvar *v;
   //@ int gid;
};

/*@
predicate_ctor vtrn(int gid)() = tic(gid);

predicate_ctor buffer(struct buffer *b)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) =
  b->q |-> ?q &*& 
  [_]b->v |-> ?v &*& 
  queue(q,?s) &*& 
  s >= 0 &*& 
  [_]b->m |-> ?m &*& 
  [_]b->gid |-> ?gid &*& 
  Trn(v) == vtrn(gid) &*&
  mutex_of(v)==m &*&
  P(v)==false &*&
  ctr(gid,?Ct) &*&
  Wt(v) + Ct <= Ot(v) + s &*&
  Wt(v) <= Ot(v);
@*/

/*@
predicate_family_instance thread_run_data(consumer_thread)(list<void*> tobs, struct buffer *b) =
   [_]b->m |-> ?m &*&
   [_]b->v |-> ?v &*&
   [_]b->gid |-> ?gid &*& 
   [_]mutex(m) &*& 
   inv(m) == buffer(b) &*& 
   tic(gid) &*& 
   tobs == nil;

predicate_family_instance thread_run_data(producer_thread)(list<void*> tobs, struct buffer *b) =
   [_]b->m |-> ?m &*&
   [_]b->v |-> ?v &*& 
   [_]b->gid |-> ?gid &*&
   [_]mutex(m) &*& 
   inv(m) == buffer(b) &*& 
   no_cycle(m,cons(v,nil))== true &*& 
   tobs == cons(v,nil);
@*/

void consumer(struct buffer *b)
  /*@ requires [_]b->m |-> ?m &*&
               [_]b->v |-> ?v &*& 
               [_]mutex(m) &*& 
               inv(m) == buffer(b) &*& 
               [_]b->gid |-> ?gid &*&
               obs(?O) &*&
               tic(gid) &*&
               no_cycle(v,O) == true &*&
               no_cycle(m,O) == true; @*/
  /*@ ensures  [_]b->m |-> m &*&
               [_]b->v |-> v &*& 
               [_]mutex(m) &*& 
               obs(O); @*/
{
  //@ close mutex_inv(m,buffer(b));
  mutex_acquire(b->m);
  //@ open buffer(b)(?Wt1,?Ot1);
  //@ leak [_]b->v |-> v;
  
  while (size_of(b->q)==0)
  /*@ invariant [_]b->m |-> m &*& 
                [_]b->v |-> v &*& 
                b->q |-> ?q &*& 
                [_]b->gid |-> gid &*& 
                queue(q,?s) &*& 
                s>=0 &*& 
                mutex_held(m, _, ?Wt, ?Ot) &*& 
                ctr(gid,?Ct) &*&
                Wt(v) + Ct <= Ot(v) + s &*&
                Wt(v) <= Ot(v) &*&
                obs(cons(m,O)) &*&
                tic(gid); @*/
  {
    //@ dec_ctr(gid);
    //@ close buffer(b)(finc(Wt,v),Ot);
    //@ close mutex_inv(m,buffer(b));
    //@ close condvar_trn(v,vtrn(gid));
    condvar_wait(b->v, b->m);
    //@ open buffer(b)(_,_);
    //@ open vtrn(gid)();
  }
  dequeue(b->q);
  //@ dec_ctr(gid);
  //@ close buffer(b)(Wt, Ot);
  //@ close mutex_inv(m,buffer(b));
  mutex_release(b->m);
  //@ leak [_]mutex(m);
}

void producer(struct buffer *b)
  /*@ requires [_]b->m |-> ?m &*&
               [_]b->v |-> ?v &*&
               [_]b->gid |-> ?gid &*& 
               [_]mutex(m) &*& 
               inv(m) == buffer(b) &*& 
               obs(cons(v,?O)) &*& 
               no_cycle(m,cons(v,O))== true; @*/
  /*@ ensures  [_]b->m |-> m &*& 
               [_]b->v |-> v &*& 
               [_]mutex(m) &*& 
               obs(O); @*/
{
  //@ close mutex_inv(m,buffer(b));
  mutex_acquire(b->m);
  //@ open buffer(b)(?Wt,_);
  //@ close condvar_trn(v,vtrn(gid));
  /*@ if (Wt(v)>0){
        inc_ctr(gid);
        close vtrn(gid)();
      }
  @*/

  condvar_signal(b->v);
  enqueue(b->q,12);
  //@ g_dischl(v);
  //@ assert mutex_held(m,_,?Wt1,?Ot1);
  //@ close buffer(b)(Wt1,Ot1);
  //@ close mutex_inv(m,buffer(b));
  mutex_release(b->m);
}

void consumer_thread(struct buffer *b)  //@ : thread_run
  //@ requires thread_run_data(consumer_thread)(?tobs,b) &*& obs(tobs);
  //@ ensures obs(nil);
{
  //@ open thread_run_data(consumer_thread)(_,_);
  consumer(b);
}

void producer_thread(struct buffer *b)  //@ : thread_run
  //@ requires thread_run_data(producer_thread)(?tobs,b) &*& obs(tobs);
  //@ ensures obs(nil);
{
  //@ open thread_run_data(producer_thread)(_,_);
  producer(b);
}

int main() //@ : custom_main_spec
  //@ requires obs(nil);
  //@ ensures obs(nil);
{
  struct queue *q = create_queue();
    
  //@ close create_mutex_ghost_args(0,nil);
  struct mutex *m = create_mutex();
    
  //@ int gid = new_ctr();
  //@ close create_condvar_ghost_args(m,1,false,vtrn(gid));
  struct condvar *v = create_condvar();

  struct buffer *b = malloc(sizeof(struct buffer));
  if (b==0)
    abort();    
  b->q = q;
  b->m = m;
  b->v = v;
  //@ b->gid = gid;
    
  //@ leak [_]b->v |-> _;
  //@ leak [_]b->m |-> _;
  //@ leak [_]b->gid |-> _;
  //@ leak [_]malloc_block_buffer(_);

  //@ g_chrgu(v);
  //@ inc_ctr(gid);    
  //@ close init_mutex_ghost_args(buffer(b));
  //@ close buffer(b)(empb,finc(empb,v));
  //@ init_mutex(m);
  //@ leak [_]mutex(m);

  //@ close thread_run_data(producer_thread)(cons(v,nil),b);
  thread_start(producer_thread, b);
    
  //@ close thread_run_data(consumer_thread)(nil,b);
  thread_start(consumer_thread, b);

  return 0;
}
