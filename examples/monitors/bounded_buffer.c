/*
  A Bounded Buffer Program Synchronized Using Monitors: Verification of Deadlock-Freedom
*/

#include "stdlib.h"
#include "monitors.h"
#include "queues.h"
//@ #include "ghost_counters.gh"

struct buffer {
   struct queue *q;
   struct mutex *m;
   struct condvar *ve;
   struct condvar *vf;
   int max;
   //@ int ge;
   //@ int gf;
};

/*@
predicate_ctor vtrn(int i)() = tic(i);

predicate_ctor buffer(struct buffer *b)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  b->q |-> ?q &*& 
  [_]b->max |-> ?max &*& 
  [_]b->ve |-> ?ve &*& 
  [_]b->vf |-> ?vf &*& 
  [_]b->ge |-> ?ge &*& 
  [_]b->gf |-> ?gf &*& 
  queue(q,?s) &*& 
  s >= 0 &*& 
  [_]b->m |-> ?m &*& 
  mutex_of(ve)==m &*& 
  mutex_of(vf)==m &*&
  P(ve) == false &*& 
  Trn(ve) == vtrn(ge) &*& 
  Trn(vf) == vtrn(gf) &*&
  ctr(ge,?Ce) &*& 
  ctr(gf,?Cf) &*&
  Wt(ve) + Ce <= Ot(ve) + s &*&
  Wt(ve) <= Ot(ve) &*&
  Wt(vf) + Cf + s < Ot(vf) + max &*&
  (Wt(vf) == 0 ? true : Wt(vf) < Ot(vf));
@*/

/*@
predicate_family_instance thread_run_data(consumer_thread)(list<void*> tobs, struct buffer *b) =
   [_]b->m |-> ?m &*&
   [_]b->ve |-> ?ve &*& 
   [_]b->vf |-> ?vf &*& 
   [_]mutex(m) &*& 
   inv(m) == buffer(b) &*&
   no_cycle(ve,cons(vf,nil)) == true &*&
   no_cycle(m,cons(vf,nil)) == true &*&
   [_]b->ge |-> ?ge &*& 
   [_]b->gf |-> ?gf &*&
   P(ve)==false &*& 
   P(vf)==true &*& 
   tic(ge) &*& 
   tobs == cons(vf,nil);

predicate_family_instance thread_run_data(producer_thread)(list<void*> tobs, struct buffer *b) =
   [_]b->m |-> ?m &*& 
   [_]b->ve |-> ?ve &*& 
   [_]b->vf |-> ?vf &*& 
   [_]mutex(m) &*& 
   inv(m) ==  buffer(b) &*&
   [_]b->gf |-> ?gf &*& 
   [_]b->ge |-> ?ge &*&
   no_cycle(vf,cons(ve,nil)) == true &*& 
   no_cycle(m,cons(ve,nil))== true &*& 
   tobs == cons(ve,nil) &*& 
   tic(gf);
@*/

void consumer(struct buffer *b)
  /*@ requires [_]b->m |-> ?m &*& 
               [_]b->ve |-> ?ve &*& 
               [_]b->vf |-> ?vf &*& 
               [_]mutex(m) &*& 
               [_]b->ge |-> ?ge &*& 
               [_]b->gf |-> ?gf &*&
               inv(m) == buffer(b) &*&
               obs(cons(vf,?O)) &*& 
               tic(ge) &*&
               no_cycle(ve,cons(vf,O)) == true &*&
               no_cycle(m,cons(vf,O)) == true;
    @*/    
  /*@ ensures [_]b->m |-> m &*& 
              [_]b->ve |-> ve &*& 
              [_]mutex(m) &*& 
              obs(O); @*/
{
  //@ close mutex_inv(m,buffer(b));
  mutex_acquire(b->m);
  //@ open buffer(b)(_,_);
  while (size_of(b->q)==0)
  /*@ invariant [_]b->m |-> m &*& 
                [_]b->max |-> ?max &*& 
                [_]b->ve |-> ve &*& 
                [_]b->vf |-> vf &*&  
                b->q |-> ?q &*& 
                queue(q,?s) &*& 
                s>=0 &*& 
                mutex_held(m, _, ?Wt, ?Ot) &*& 
                [_]b->ge |-> ge &*&
                [_]b->gf |-> gf &*& 
                ctr(gf,?Cf) &*& 
                ctr(ge,?Ce) &*&
                Wt(ve) + Ce <= Ot(ve) + s &*&
                Wt(ve) <= Ot(ve) &*&
                Wt(vf) + Cf + s < Ot(vf) + max &*&
                (Wt(vf) == 0 ? true : Wt(vf) < Ot(vf)) &*&
                obs(cons(m,cons((void*)vf,O))) &*& 
                tic(ge); @*/
  {
    //@ dec_ctr(ge);
    //@ close buffer(b)(finc(Wt,ve),Ot);
    //@ close mutex_inv(m,buffer(b));  
    //@ close condvar_trn(ve,vtrn(ge));
    condvar_wait(b->ve, b->m);
    //@ open buffer(b)(_,_);  
    //@ open vtrn(ge)();
  }
  dequeue(b->q);
  //@ close condvar_trn(vf,vtrn(gf));
  /*@ if (Wt(vf)>0){
        inc_ctr(gf);
        close vtrn(gf)();
      }
  @*/
  condvar_signal(b->vf); 
  //@ g_Ot_isbag(m,vf);
  //@ g_dischl(vf);  
  //@ dec_ctr(ge); 
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close buffer(b)(Wte,Ote);
  //@ close mutex_inv(m,buffer(b));
  mutex_release(b->m);
  //@ leak [_]mutex(m);
}

void producer(struct buffer *b)
  /*@ requires [_]b->m |-> ?m &*& 
               [_]b->ve |-> ?ve &*& 
               [_]b->vf |-> ?vf &*& 
               [_]mutex(m) &*& 
               [_]b->ge |-> ?ge &*& 
               [_]b->gf |-> ?gf &*&
               inv(m) == buffer(b) &*& 
               obs(cons(ve,?O)) &*& 
               tic(gf) &*&
               no_cycle(m,cons(ve,O))== true &*&
               no_cycle(vf,cons(ve,O))== true; @*/    
  /*@ ensures [_]b->m |-> m &*& 
              [_]b->ve |-> ve &*& 
              [_]mutex(m) &*& obs(O); @*/
{
  //@ close mutex_inv(m,buffer(b));
  mutex_acquire(b->m);
  //@ open buffer(b)(_,_);
  int maximum = b -> max;
  while (size_of(b->q) == maximum)
  /*@ invariant [_]b->m |-> m &*& 
                [_]b->max |-> ?max &*& 
                maximum == max &*& 
                [_]b->ve |-> ve &*& 
                [_]b->vf |-> vf &*& 
                b->q |-> ?q &*& 
                queue(q,?s) &*& 
                s>=0 &*& 
                mutex_held(m, _, ?Wt, ?Ot) &*&
                [_]b->ge |-> ge &*& [_]b->gf |-> gf &*& ctr(gf,?Cf) &*& ctr(ge,?Ce) &*&
                Wt(ve) + Ce <= Ot(ve) + s &*&
                Wt(ve) <= Ot(ve) &*&
                Wt(vf) + Cf + s < Ot(vf) + max &*&
                (max == s || Wt(vf) == 0 ? true : Wt(vf) < Ot(vf)) &*&
                obs(cons(m,cons((void*)ve,O))) &*& tic(gf); @*/
  {
    //@ dec_ctr(gf);
    //@ close buffer(b)(finc(Wt,vf),Ot);
    //@ close mutex_inv(m,buffer(b));
    //@ close condvar_trn(vf,vtrn(gf));
    condvar_wait(b->vf, b->m);
    //@ open buffer(b)(_,_);   
    //@ assert mutex_held(m,_,?Wt11,?Ot11);
    //@ open vtrn(gf)();
  }  
  //@ assert mutex_held(m,_,?Wt1,?Ot1);
  enqueue(b->q,12);
  //@ close condvar_trn(ve,vtrn(ge)); 
  /*@ if (Wt(ve)>0){
        inc_ctr(ge);
        close vtrn(ge)();
      }
  @*/
  condvar_signal(b->ve);
  //@ g_dischl(ve);
  //@ close mutex_inv(m,buffer(b)); 
  //@ dec_ctr(gf);
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close buffer(b)(Wte,Ote);
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

int main() //@ : custom_main_spec
    //@ requires obs(nil);
    //@ ensures obs(nil);
{
    struct queue *q = create_queue();
    
    //@ close create_mutex_ghost_args(0,cons(1,cons(2,nil)));    
    struct mutex *m = create_mutex();
    
    //@ int ge = new_ctr();
    //@ close create_condvar_ghost_args(m,1,false,vtrn(ge));
    struct condvar *ve = create_condvar();
    
    //@ int gf = new_ctr();
    //@ close create_condvar_ghost_args(m,2,true,vtrn(gf));
    struct condvar *vf = create_condvar();
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
    
    //@ inc_ctr(gf);
    //@ inc_ctr(ge);
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

    return 0;
}
