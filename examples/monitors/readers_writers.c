/*
  A Readers-Writers Lock Program Synchronized Using Monitors: Verification of Deadlock-Freedom
  (arithmetic overflows are not checked)
*/

#include "stdlib.h"
#include "monitors.h"
#include "queues.h"
//@ #include "ghost_counters.gh"

struct read_write {
   int aw;
   int ar;
   int ww;
   struct mutex *m;   
   condvar vr;
   condvar vw;
   //@ int gw;  
};

/*@
predicate_ctor vwtrn(int i)() = tic(i);

predicate_ctor read_write(struct read_write *b)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  b->aw |-> ?aw &*& 
  b->ar |-> ?ar &*& 
  b->ww |-> ?ww &*& 
  [_]b->m |-> ?m &*& 
  [_]b->gw |-> ?gw &*&
  aw >= 0 &*& 
  ar >= 0 &*& 
  ww >= 0 &*&
  [_]b->vr |-> ?vr &*& 
  [_]b->vw |-> ?vw &*& 
  vr != vw &*& 
  mutex_of(vr)==m &*& 
  mutex_of(vw)==m &*&
  P(vr)==false &*& 
  Trn(vw) == vwtrn(gw) &*& 
  Trn(vr) == no_transfer &*&
  ctr(gw,?Cw) &*&
  (Wt(vr) <= 0 || 0 < aw + ww) &*&
  aw + ww <= Ot(vr) &*&
  Wt(vw) + Cw + aw + ar <= Ot(vw) &*&
  Wt(vw) < 1 || Wt(vw) < Ot(vw)  ;
@*/

/*@
predicate_family_instance thread_run_data(reader_thread)(list<void*> tobs, struct read_write *b) =
   [_]b->m |-> ?m &*& 
   [_]b->vr |-> ?vr &*& 
   [_]b->vw |-> ?vw &*& 
   [_]mutex(m) &*& 
   [_]b->gw |-> ?gw &*& 
   inv(m) == read_write(b) &*& 
   P(vr)==false &*& 
   !eXc(vr) &*&
   tobs == nil &*&
   no_cycle(vr,nil) == true &*& 
   no_cycle(m,cons(vw,nil)) == true;

predicate_family_instance thread_run_data(writer_thread)(list<void*> tobs, struct read_write *b) =
   [_]b->m |-> ?m &*& 
   [_]b->vr |-> ?vr &*& 
   [_]b->vw |-> ?vw &*& 
   [_]mutex(m) &*& 
   [_]b->gw |-> ?gw &*& 
   inv(m) == read_write(b) &*&   tobs == nil &*& 
   !eXc(vr) &*&
   no_cycle(vw,cons(vw,cons(vr,nil))) == true &*& 
   no_cycle(m,cons(vw,cons(vr,nil))) == true;   
@*/

void writer(struct read_write *b)
  /*@ requires [_]b->m |-> ?m &*& 
               [_]b->vr |-> ?vr &*& 
               [_]b->vw |-> ?vw &*& 
               [_]mutex(m) &*& 
               [_]b->gw |-> ?gw &*&
               inv(m) == read_write(b) &*&
	       !eXc(vr) &*&
               obs(?O) &*&
               no_cycle(vw,cons(vw,cons(vr,O))) == true &*& 
               no_cycle(m,cons(vw,cons(vr,O))) == true; @*/    
  /*@ ensures [_]b->m |-> m &*& 
              [_]b->vr |-> vr &*& 
              [_]b->vw |-> vw &*& 
              [_]mutex(m) &*& obs(O); @*/
{
  //@ close mutex_inv(m,read_write(b));
  mutex_acquire(b->m);
  //@ open read_write(b)(_,_);
  //@ g_chrgl(vr);  
  //@ g_chrgl(vw);
  //@ inc_ctr(gw);
  while (b->aw + b->ar > 0)
  /*@ invariant b->aw |-> ?aw &*& 
                b->ar |-> ?ar &*& 
                b->ww |-> ?ww &*& 
                [_]b->m |-> m &*&
                aw >= 0 &*& 
                ar >= 0 &*& 
                ww >= 0 &*&
                [_]b->vr |-> vr &*& 
                [_]b->vw |-> vw &*& 
                mutex_held(m, _, ?Wt, ?Ot) &*&
                [_]b->gw |-> gw &*&
                ctr(gw,?Cw) &*&
                Wt(vr) <= 0 || 0 < aw + ww + 1 &*&
                aw + ww + 1 <= Ot(vr) &*&
                Wt(vw) + Cw + aw + ar <= Ot(vw) &*& 
                Wt(vw) < 1 || Wt(vw) < Ot(vw) &*&
                obs(cons((void*)vw,cons((void*)vr,cons(m,O)))) &*& 
                tic(gw);
  @*/
  {
    b->ww = b->ww + 1;
    //@ dec_ctr(gw);
    //@ close read_write(b)(finc(Wt,vw),Ot);
    //@ close mutex_inv(m,read_write(b));
    //@ close condvar_trn(vw,vwtrn(gw));
    condvar_wait(b->vw, b->m);
    //@ open read_write(b)(_,_);
    if (b->ww == 0)
      abort();
    b->ww = b->ww - 1;
    //@ open vwtrn(gw)();
   }
   
  b->aw = b->aw + 1;
  //@ dec_ctr(gw);
  //@ close read_write(b)(Wt,Ot);  
  //@ close mutex_inv(m,read_write(b));  
  mutex_release(b->m);

  // Perform writing ...

  //@ close mutex_inv(m,read_write(b));
  mutex_acquire(b->m);
  //@ open read_write(b)(?Wt2,?Ot2);

  if (b->aw != 1)
    abort(); 
  b->aw = b->aw - 1;
   
  /*@ if (Wt2(vw)>0){
        inc_ctr(gw);
        close vwtrn(gw)();
      }
  @*/
  //@ close condvar_trn(vw,vwtrn(gw));
  condvar_signal(b->vw); 
  //@ inc_ctr(gw);  
  //@ dec_ctr(gw);  
  //@ g_dischl(vw);   
  if (b->ww == 0){   
    //@ close condvar_trn(vr,no_transfer);
    //@ n_times_no_transfer(Wt2(vr));
    condvar_broadcast(b->vr);
  }
  //@ g_dischl(vr);
  //@ assert mutex_held(m,_,?Wte,?Ote);  
  //@ close read_write(b)(Wte,Ote);       
  //@ close mutex_inv(m,read_write(b));  
  mutex_release(b->m);     
  //@ leak [_]mutex(m);
}

void reader(struct read_write *b)
  /*@ requires [_]b->m |-> ?m &*& 
               [_]b->vr |-> ?vr &*& 
               [_]b->vw |-> ?vw &*& 
               [_]mutex(m) &*& 
               inv(m) == read_write(b) &*& 
               [_]b->gw |-> ?gw &*& 
               !eXc(vr) &*&
               obs(?O) &*&
               no_cycle(vr,O) == true &*& 
               no_cycle(m,cons(vw,O)) == true;
    @*/    
  /*@ ensures [_]b->m |-> m &*& 
              [_]b->vr |-> vr &*& 
              [_]b->vw |-> vw &*& 
              [_]mutex(m) &*& 
              obs(O); @*/
{
  //@ close mutex_inv(m,read_write(b));
  mutex_acquire(b->m);
  //@ open read_write(b)(?Wt1,?Ot1);
  //@ leak [_]b->vr |-> vr;
  //@ leak [_]b->vw |-> vw;
  while (b->aw + b->ww > 0)
  /*@ invariant b->aw |-> ?aw &*& 
                b->ar |-> ?ar &*& 
                b->ww |-> ?ww &*& 
                [_]b->m |-> m &*&
                aw >= 0 &*& 
                ar >= 0 &*& 
                ww >= 0 &*&   
                [_]b->vr |-> vr &*& 
                [_]b->vw |-> vw &*& 
                mutex_held(m, _, ?Wt, ?Ot) &*&
                [_]b->gw |-> gw &*&
                ctr(gw,?Cw) &*&
                Wt(vr) <= 0 || 0 < aw + ww &*&
                aw + ww <= Ot(vr) &*&
                Wt(vw) + Cw + aw + ar  <= Ot(vw) &*&
                Wt(vw) < 1 || Wt(vw) < Ot(vw) &*&
                obs(cons(m,O));
  @*/
  {
    //@ close read_write(b)(finc(Wt,vr),Ot);
    //@ close mutex_inv(m,read_write(b));
    //@ close condvar_trn(vr,no_transfer);
    condvar_wait(b->vr, b->m);
    //@ open read_write(b)(_,_);        
    //@ open no_transfer();
  }
  b->ar = b->ar + 1;
  //@ g_chrgl(vw);
  //@ close read_write(b)(Wt,finc(Ot,vw));
  //@ close mutex_inv(m,read_write(b));  
  mutex_release(b->m);
  
  // Perform reading ...
  
  //@ close mutex_inv(m,read_write(b));  
  mutex_acquire(b->m); 
  //@ open read_write(b)(?Wt2,?Ot2);
  if (b->ar<1)
    abort();    
  b->ar = b->ar - 1;
  //@ close condvar_trn(vw,vwtrn(gw));
  /*@ if (Wt2(vw)>0){
        inc_ctr(gw);
        close vwtrn(gw)();
      }
  @*/
  condvar_signal(b->vw);
  //@ inc_ctr(gw);  
  //@ dec_ctr(gw);  
  //@ g_dischl(vw);
  //@ assert mutex_held(m,_,?Wte,?Ote); 
  //@ close read_write(b)(Wte,Ote);
  //@ close mutex_inv(m,read_write(b));  
  mutex_release(b->m);     
  //@ leak [_]mutex(m);
}

void reader_thread(struct read_write *b)  //@ : thread_run
    //@ requires thread_run_data(reader_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(reader_thread)(_,_);
  reader(b);
}

void writer_thread(struct read_write *b)  //@ : thread_run
    //@ requires thread_run_data(writer_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(writer_thread)(_,_);
  writer(b);
}

int main() //@ : custom_main_spec
    //@ requires obs(nil); 
    //@ ensures obs(nil);
{
    //@ close create_mutex_ghost_args(0,cons(1,nil));    
    struct mutex *m = create_mutex();
    
    //@ int gw = new_ctr();
    //@ close create_condvar_ghost_args(m,1,true,vwtrn(gw));    
    condvar vw = create_condvar();

    //@ close create_condvar_ghost_args(m,2,false,no_transfer);    
    condvar vr = create_condvar();
   
    struct read_write *b = malloc(sizeof(struct read_write));
    if (b==0)
      abort();
    b->ww = 0;
    b->aw = 0;
    b->ar = 0;
    b->m = m;
    b->vw = vw;
    b->vr = vr;
    //@ b->gw = gw;
    //@ leak [_]b->vw |-> _;
    //@ leak [_]b->vr |-> _;
    //@ leak [_]b->m |-> _;    
    //@ leak [_]b->gw |-> _;    
    //@ leak [_]malloc_block_read_write(_);
    //@ close init_mutex_ghost_args(read_write(b));
    //@ close read_write(b)(empb,empb);
    //@ init_mutex(m);
    //@ leak [_]mutex(m);

    //@ close thread_run_data(reader_thread)(nil,b);
    thread_start(reader_thread, b);

    //@ close thread_run_data(reader_thread)(nil,b);
    thread_start(reader_thread, b);

    //@ close thread_run_data(writer_thread)(nil,b);    
    while (true)
    /*@ invariant obs(nil) &*& thread_run_data(writer_thread)(nil,b) &*& [_]b->m |-> m &*& [_]b->vr |-> vr &*& [_]b->vw |-> vw &*& [_]b->gw |-> gw &*& [_]mutex(m);
    @*/
    {
      thread_start(writer_thread, b);
      //@ close thread_run_data(writer_thread)(nil,b);    
    }

    return 0;
}
