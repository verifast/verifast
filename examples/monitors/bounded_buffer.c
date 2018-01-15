/*
  A Bounded Buffer Program Implemented by Condition Variables: Deadlock-free Verification
*/

#include "stdlib.h"
#include "monitors.h"
#include "queues.h"
#include "auth_monoid.h"

struct buffer {
   struct queue *q;
   struct mutex *m;
   struct mutex_cond *ve;
   struct mutex_cond *vf;
   int max;
   //@ int ge;
   //@ int gf;
};

/*@
predicate_ctor buffer(struct buffer *b)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  b->q |-> ?q &*& [_]b->max |-> ?max &*& [_]b->ve |-> ?ve &*& [_]b->vf |-> ?vf &*& [_]b->ge |-> ?ge &*& [_]b->gf |-> ?gf &*& ve != vf &*&
  queue(q,?s) &*& s >= 0 &*& [_]b->m |-> ?m &*& mutex_of(ve)==m &*& mutex_of(vf)==m &*&
  P(ve) == false &*& 
  Trn(ve) == vtrn(ge) &*& Trn(vf) == vtrn(gf) &*&
  authfull(ge,?Ce) &*& authfull(gf,?Cf) &*&
  Wt(ve) + Ce <= Ot(ve) + s &*&
  Wt(ve) <= Ot(ve) &*&
  Wt(vf) + Cf + s < Ot(vf) + max &*&
  (Wt(vf) == 0 ? true : Wt(vf) < Ot(vf));
@*/

/*@
predicate_family_instance thread_run_data(consumer_thread)(list<void*> tobs, struct buffer *b) =
   [_]b->m |-> ?m &*& [_]b->ve |-> ?ve &*& [_]b->vf |-> ?vf &*& [_]mutex(m) &*& inv(m) == buffer(b) 
   &*& no_cycle(ve,cons(vf,nil)) == true 
   &*& no_cycle(m,cons(vf,nil)) == true
   &*& [_]b->ge |-> ?ge &*& [_]b->gf |-> ?gf
   &*& P(ve)==false &*& P(vf)==true &*& authfrag(ge,1) &*& authfrag(gf,0) &*& tobs == cons(vf,nil);

predicate_family_instance thread_run_data(producer_thread)(list<void*> tobs, struct buffer *b) =
   [_]b->m |-> ?m &*& [_]b->ve |-> ?ve &*& [_]b->vf |-> ?vf &*& [_]mutex(m) &*& inv(m) ==  buffer(b)
   &*& [_]b->gf |-> ?gf &*& [_]b->ge |-> ?ge
   &*& no_cycle(vf,cons(ve,nil))== true &*& no_cycle(m,cons(ve,nil))== true &*& tobs == cons(ve,nil) &*& authfrag(gf,1) &*& authfrag(ge,0);
   
predicate_ctor vtrn(int i)() = authfrag(i,1);

@*/

void consumer(struct buffer *b)
    /*@ requires [_]b->m |-> ?m &*& [_]b->ve |-> ?ve &*& [_]b->vf |-> ?vf &*& [_]mutex(m) &*& inv(m) ==  buffer(b)
          &*& [_]b->ge |-> ?ge &*& [_]b->gf |-> ?gf
          &*& obs(cons(vf,?O)) &*& authfrag(ge,1) &*& authfrag(gf,0)
          &*& no_cycle(ve,cons(vf,O)) == true 
          &*& no_cycle(m,cons(vf,O)) == true;
    @*/    
    //@ ensures [_]b->m |-> m &*& [_]b->ve |-> ve &*& [_]mutex(m) &*& obs(O);
{
  //@ close mutex_inv(m,buffer(b));
  mutex_acquire(b->m);
  //@ open buffer(b)(_,_);
  while (size_of(b->q)==0)
  /*@ invariant [_]b->m |-> m &*& [_]b->max |-> ?max &*& [_]b->ve |-> ve &*& [_]b->vf |-> vf &*&  b->q |-> ?q &*& queue(q,?s) &*& s>=0 &*& mutex_held(m, _, ?Wt, ?Ot) &*& ve != vf
                &*& [_]b->ge |-> ge &*& [_]b->gf |-> gf &*& authfull(gf,?Cf) &*& authfull(ge,?Ce)
                &*& Wt(ve) + Ce <= Ot(ve) + s
                &*& Wt(ve) <= Ot(ve)
                &*& Wt(vf) + Cf + s < Ot(vf) + max
                &*& (Wt(vf) == 0 ? true : Wt(vf) < Ot(vf))
                &*& obs(cons(m,cons((void*)vf,O))) &*& authfrag(ge,1) &*& authfrag(gf,0);
  @*/
  {
    //@ upd_ghost(ge,-1);
    //@ close buffer(b)(finc(Wt,ve),Ot);
    //@ close mutex_inv(m,buffer(b));  
    //@ close cond_trn(ve,vtrn(ge));
    mutex_cond_wait(b->ve, b->m);
    //@ open buffer(b)(_,_);  
    //@ open vtrn(ge)();
    //@ leak authfrag(ge,0);
  }
  dequeue(b->q);
  //@ close cond_trn(vf,vtrn(gf));
  /*@ if (Wt(vf)>0){
        upd_ghost(gf,1);
        close vtrn(gf)();
      }
      else
        leak authfrag(gf,0);

  @*/
  mutex_cond_signal(b->vf); 
  //@ g_Ot_isbag(m,vf);
  //@ g_dischl(vf);  
  //@ upd_ghost(ge,-1); 
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close buffer(b)(Wte,Ote);
  //@ close mutex_inv(m,buffer(b));
  //@ leak authfrag(ge,0);
  mutex_release(b->m);
  //@ leak [_]mutex(m);
}

void producer(struct buffer *b)
    /*@ requires [_]b->m |-> ?m &*& [_]b->ve |-> ?ve &*& [_]b->vf |-> ?vf &*& [_]mutex(m) &*& inv(m) == buffer(b) 
          &*& [_]b->ge |-> ?ge &*& [_]b->gf |-> ?gf
          &*& obs(cons(ve,?O)) &*& authfrag(gf,1) &*& authfrag(ge,0)
          &*& no_cycle(m,cons(ve,O))== true
          &*& no_cycle(vf,cons(ve,O))== true;          
    @*/    
    //@ ensures [_]b->m |-> m &*& [_]b->ve |-> ve &*& [_]mutex(m) &*& obs(O);
{
  //@ close mutex_inv(m,buffer(b));
  mutex_acquire(b->m);
  //@ open buffer(b)(_,_);
  int maximum = b -> max;
  while (size_of(b->q) == maximum)
  /*@ invariant [_]b->m |-> m &*& [_]b->max |-> ?max &*& maximum == max &*& [_]b->ve |-> ve &*& [_]b->vf |-> vf &*&  b->q |-> ?q &*& queue(q,?s) &*& s>=0 &*& mutex_held(m, _, ?Wt, ?Ot) 
                &*& [_]b->ge |-> ge &*& [_]b->gf |-> gf &*& authfull(gf,?Cf) &*& authfull(ge,?Ce)
                &*& Wt(ve) + Ce <= Ot(ve) + s
                &*& Wt(ve) <= Ot(ve)
                &*& Wt(vf) + Cf + s < Ot(vf) + max
                &*& (max == s || Wt(vf) == 0 ? true : Wt(vf) < Ot(vf))
                &*& obs(cons(m,cons((void*)ve,O))) &*& authfrag(gf,1) &*& authfrag(ge,0);
  @*/
  {
    //@ upd_ghost(gf,-1);
    //@ close buffer(b)(finc(Wt,vf),Ot);
    //@ close mutex_inv(m,buffer(b));
    //@ close cond_trn(vf,vtrn(gf));
    mutex_cond_wait(b->vf, b->m);
    //@ open buffer(b)(_,_);   
    //@ assert mutex_held(m,_,?Wt11,?Ot11);
    //@ open vtrn(gf)();
    //@ g_inbag(Wt11,vf);
    //@ leak authfrag(gf,0);
  }  
  //@ assert mutex_held(m,_,?Wt1,?Ot1);
  enqueue(b->q,12);
  //@ close cond_trn(ve,vtrn(ge)); 
  /*@ if (Wt(ve)>0){
        upd_ghost(ge,1);
        close vtrn(ge)();
      }
      else
        leak authfrag(ge,0);
  @*/
  mutex_cond_signal(b->ve);
  //@ g_dischl(ve);
  //@ close mutex_inv(m,buffer(b)); 
  //@ upd_ghost(gf,-1);
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close buffer(b)(Wte,Ote);
  //@ leak authfrag(gf,0);
  mutex_release(b->m);
  //@ leak [_]mutex(m);    
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

void main()
    //@ requires obs(nil);
    //@ ensures obs(nil);
{
    struct queue *q = create_queue();
    //@ close create_mutex_ghost_args(0,cons(1,nil));    
    struct mutex *m = create_mutex();
    
    //@ int ge = ghost_create2(0,1);
    //@ close create_mutex_cond_ghost_args(m,1,false,vtrn(ge));
    struct mutex_cond *ve = create_mutex_cond();
    
    //@ int gf = ghost_create2(0,1);
    //@ close create_mutex_cond_ghost_args(m,2,true,vtrn(gf));
    struct mutex_cond *vf = create_mutex_cond();
    struct buffer *b = malloc(sizeof(struct buffer));
    if (b==0)
      abort();
    b->q = q;
    b->m = m;
    b->ve = ve;
    b->vf = vf;
    b->max = 1;
    //@ b->ge = ge;
    //@ b->gf = gf;    
    //@ leak [_]b->ve |-> _;
    //@ leak [_]b->vf |-> _;     
    //@ leak [_]b->m |-> _;    
    //@ leak [_]b->max |-> _; 
    //@ leak [_]b->ge |-> _;
    //@ leak [_]b->gf |-> _;               
    //@ leak [_]malloc_block_buffer(_);
    
    //@ g_chrgu(vf);    
    //@ g_chrgu(ve);    

    //@ close init_mutex_ghost_args(buffer(b));
    //@ close buffer(b)(empb,finc(finc(empb,vf),ve));
    //@ init_mutex(m);
    //@ leak [_]mutex(m);
    
    //@ close thread_run_data(producer_thread)(cons(ve,nil),b);
    thread_start(producer_thread, b);
    //@ close thread_run_data(consumer_thread)(cons(vf,nil),b);
    thread_start(consumer_thread, b);   
}
