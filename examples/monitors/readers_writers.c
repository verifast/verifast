/*
  A Readers-Writers Lock Program Implemented by Condition Variables: Deadlock-free Verification
  (Arithmetic overflows are not checked)
*/

#include "stdlib.h"
#include "monitors.h"
#include "queues.h"
#include "auth_monoid.h"

struct read_write {
   int aw;
   int ar;
   int ww;
   struct mutex *m;   
   struct mutex_cond *vr;
   struct mutex_cond *vw;
   //@ int gr;
   //@ int gw;  
};

/*@
predicate_ctor read_write(struct read_write *b)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  b->aw |-> ?aw &*& b->ar |-> ?ar &*& b->ww |-> ?ww &*& [_]b->m |-> ?m &*& [_]b->gr |-> ?gr &*& [_]b->gw |-> ?gw
  &*& aw >= 0 &*& ar >= 0 &*& ww >= 0     
  &*& [_]b->vr |-> ?vr &*& [_]b->vw |-> ?vw &*& vr != vw &*& mutex_of(vr)==m &*& mutex_of(vw)==m 
  &*& vr != vw &*& P(vr)==false &*& Trn(vw) == vwtrn(gw) &*& Trn(vr) == vrtrn &*&
  authfull(gr,?Cr) &*& authfull(gw,?Cw) &*&
  (Wt(vr) <= 0 || 0 < aw + ww + Cr) &*&
  aw + ww + Cr <= Ot(vr) &*&
  Wt(vw) + Cw + aw + ar  <= Ot(vw) &*&
  Wt(vw) < 1 || Wt(vw) < Ot(vw)
  ;
@*/

/*@
predicate_family_instance thread_run_data(reader_thread)(list<void*> tobs, struct read_write *b) =
   [_]b->m |-> ?m &*& [_]b->vr |-> ?vr &*& [_]b->vw |-> ?vw &*& [_]mutex(m) &*& inv(m) ==  read_write(b) 
   &*& [_]b->gr |-> ?gr &*& [_]b->gw |-> ?gw &*& authfrag(gr,0) &*& authfrag(gw,0) &*& authfrag(gw,0)
   &*& P(vr)==false &*& !eXc(vr)
   &*& tobs == nil
   &*& no_cycle(vr,nil) == true 
   &*& no_cycle(m,cons(vw,nil)) == true;

predicate_family_instance thread_run_data(writer_thread)(list<void*> tobs, struct read_write *b) =
   [_]b->m |-> ?m &*& [_]b->vr |-> ?vr &*& [_]b->vw |-> ?vw &*& [_]mutex(m) &*& inv(m) == read_write(b)
   &*& [_]b->gr |-> ?gr &*& [_]b->gw |-> ?gw &*& authfrag(gr,0) &*& authfrag(gw,0) &*& authfrag(gw,0)
   &*& tobs == nil &*& !eXc(vr)
   &*& no_cycle(vw,cons(vw,cons(vr,nil))) == true 
   &*& no_cycle(m,cons(vw,cons(vr,nil))) == true;
   
predicate_ctor vwtrn(int i)() = authfrag(i,1);
predicate vrtrn() = true;

lemma void vperms(int n,struct mutex_cond *cond);
  requires true;
  ensures cond_trns(n,vrtrn);
@*/

void writer(struct read_write *b)
    /*@ requires [_]b->m |-> ?m &*& [_]b->vr |-> ?vr &*& [_]b->vw |-> ?vw &*& [_]mutex(m) &*& inv(m) == read_write(b)
          &*& [_]b->gr |-> ?gr &*& [_]b->gw |-> ?gw &*& authfrag(gr,0) &*& authfrag(gw,0) &*& authfrag(gw,0)
	  &*& !eXc(vr)    
          &*& obs(?O)
          &*& no_cycle(vw,cons(vw,cons(vr,O))) == true 
          &*& no_cycle(m,cons(vw,cons(vr,O))) == true;
    @*/    
    //@ ensures [_]b->m |-> m &*& [_]b->vr |-> vr &*& [_]b->vw |-> vw &*& [_]mutex(m) &*& obs(O);// &*& false;
{
  //@ close mutex_inv(m,read_write(b));
  mutex_acquire(b->m);
  //@ open read_write(b)(?Wt1,?Ot1);
  //@ g_chrgl(vr);  
  //@ upd_ghost(gr,1);  
  //@ g_chrgl(vw);
  //@ upd_ghost(gw,1);
  while (b->aw + b->ar > 0)
  /*@ invariant b->aw |-> ?aw &*& b->ar |-> ?ar &*& b->ww |-> ?ww &*& [_]b->m |-> m
        &*& aw >= 0 &*& ar >= 0 &*& ww >= 0    
        &*& [_]b->vr |-> vr &*& [_]b->vw |-> vw &*& mutex_held(m, _, ?Wt, ?Ot)
        &*& [_]b->gr |-> gr &*& [_]b->gw |-> gw
        &*& authfull(gr,?Cr) &*& authfull(gw,?Cw)
        &*& Wt(vr) <= 0 || 0 < aw + ww + Cr
        &*& aw + ww + Cr <= Ot(vr)
        &*& Wt(vw) + Cw + aw + ar  <= Ot(vw) 
        &*& Wt(vw) < 1 || Wt(vw) < Ot(vw)
        &*& obs(cons((void*)vw,cons((void*)vr,cons(m,O)))) &*& authfrag(gr,1) &*& authfrag(gw,1);
  @*/
  {
    b->ww = b->ww + 1;
    //@ upd_ghost(gr,-1);
    //@ upd_ghost(gw,-1);
    //@ close read_write(b)(finc(Wt,vw),Ot);
    //@ close mutex_inv(m,read_write(b));
    //@ close cond_trn(vw,vwtrn(gw));
    mutex_cond_wait(b->vw, b->m);
    //@ open read_write(b)(_,_);
    if (b->ww<=0)
      abort();
    b->ww = b->ww - 1;
    //@ upd_ghost(gr,1);
    //@ open vwtrn(gw)();
    //@ leak authfrag(gw,0);
   }
  b->aw = b->aw + 1;
  //@ upd_ghost(gr,-1);
  //@ upd_ghost(gw,-1);
  //@ close read_write(b)(Wt,Ot);  
  //@ close mutex_inv(m,read_write(b));  
  mutex_release(b->m);

  // Perform writing ...

  //@ close mutex_inv(m,read_write(b));
  mutex_acquire(b->m);
  //@ open read_write(b)(?Wt2,?Ot2);

  if (b->aw != 1 || b->ar > 0)
    abort(); 
  b->aw = b->aw - 1;
   
  /*@ if (Wt2(vw)>0){
        upd_ghost(gw,1);
        close vwtrn(gw)();
      }
      else 
        leak authfrag(gw,0);
  @*/
  //@ close cond_trn(vw,vwtrn(gw));
  mutex_cond_signal(b->vw); 
  //@ upd_ghost(gw,0);
  //@ g_dischl(vw);
   
  if (b->ww == 0){   
    //@ close cond_trn(vr,vrtrn);
    //@ vperms(Wt2(vr),vr);
    mutex_cond_broadcast(b->vr);
  }
  //@ upd_ghost(gr,0);
  //@ g_dischl(vr);
  //@ assert mutex_held(m,_,?Wte,?Ote);  
  //@ close read_write(b)(Wte,Ote);       
  //@ close mutex_inv(m,read_write(b));  
  //@ leak authfrag(gw,0);
  //@ leak authfrag(gr,0);
  mutex_release(b->m);     
  //@ leak [_]mutex(m);
}

void reader(struct read_write *b)
    /*@ requires [_]b->m |-> ?m &*& [_]b->vr |-> ?vr &*& [_]b->vw |-> ?vw &*& [_]mutex(m) &*& inv(m) == read_write(b) 
          &*& [_]b->gr |-> ?gr &*& [_]b->gw |-> ?gw &*& authfrag(gr,0) &*& authfrag(gw,0) &*& authfrag(gw,0)
          &*& !eXc(vr)
          &*& obs(?O)
          &*& no_cycle(vr,O) == true 
          &*& no_cycle(m,cons(vw,O)) == true;
    @*/    
    //@ ensures [_]b->m |-> m &*& [_]b->vr |-> vr &*& [_]b->vw |-> vw &*& [_]mutex(m) &*& obs(O);
{
  //@ close mutex_inv(m,read_write(b));
  mutex_acquire(b->m);
  //@ open read_write(b)(?Wt1,?Ot1);
  //@ leak [_]b->vr |-> vr;
  //@ leak [_]b->vw |-> vw;
  while (b->aw + b->ww > 0)
  /*@ invariant b->aw |-> ?aw &*& b->ar |-> ?ar &*& b->ww |-> ?ww &*& [_]b->m |-> m
        &*& aw >= 0 &*& ar >= 0 &*& ww >= 0    
        &*& [_]b->vr |-> vr &*& [_]b->vw |-> vw &*& mutex_held(m, _, ?Wt, ?Ot)
        &*& [_]b->gr |-> gr &*& [_]b->gw |-> gw
        &*& authfull(gr,?Cr) &*& authfull(gw,?Cw)
        &*& Wt(vr) <= 0 || 0 < aw + ww + Cr
        &*& aw + ww + Cr <= Ot(vr)
        &*& Wt(vw) + Cw + aw + ar  <= Ot(vw) 
        &*& Wt(vw) < 1 || Wt(vw) < Ot(vw)
        &*& obs(cons(m,O)) &*& authfrag(gr,0);
  @*/
  {
    //@ upd_ghost(gr,0);
    //@ close read_write(b)(finc(Wt,vr),Ot);
    //@ close mutex_inv(m,read_write(b));
    //@ close cond_trn(vr,vrtrn);
    mutex_cond_wait(b->vr, b->m);
    //@ open read_write(b)(_,_);        
    //@ open vrtrn();
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
  //@ close cond_trn(vw,vwtrn(gw));
    /*@ if (Wt2(vw)>0){
        upd_ghost(gw,1);
        close vwtrn(gw)();
      }
      else 
        leak authfrag(gw,0);
  @*/
   mutex_cond_signal(b->vw);
  //@ upd_ghost(gw,0);
  //@ g_dischl(vw);
  //@ assert mutex_held(m,_,?Wte,?Ote); 
  //@ close read_write(b)(Wte,Ote);
  //@ close mutex_inv(m,read_write(b));  
  //@ leak authfrag(gr,0);
  //@ leak authfrag(gw,0);
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

void main()
    //@ requires obs(nil); 
    //@ ensures obs(nil);
{
    //@ close create_mutex_ghost_args(1,cons(1,nil));    
    struct mutex *m = create_mutex();
    
    //@ int gw = ghost_create1(0);
    //@ close create_mutex_cond_ghost_args(m,1,true,vwtrn(gw));    
    struct mutex_cond *vw = create_mutex_cond();

    //@ int gr = ghost_create1(0);
    //@ close create_mutex_cond_ghost_args(m,2,false,vrtrn);    
    struct mutex_cond *vr = create_mutex_cond();
   
    struct read_write *b = malloc(sizeof(struct read_write));
    if (b==0)
      abort();
    b->ww = 0;
    b->aw = 0;
    b->ar = 0;
    b->m = m;
    b->vw = vw;
    b->vr = vr;
    //@ b->gr = gr;
    //@ b->gw = gw;
    //@ leak [_]b->vw |-> _;
    //@ leak [_]b->vr |-> _;
    //@ leak [_]b->m |-> _;    
    //@ leak [_]b->gr |-> _;   
    //@ leak [_]b->gw |-> _;    
    //@ leak [_]malloc_block_read_write(_);
    //@ close init_mutex_ghost_args(read_write(b));
    //@ close read_write(b)(empb,empb);
    //@ init_mutex(m);
    //@ leak [_]mutex(m);

    //@ ghost_split(gr,0,0);
    //@ ghost_split(gr,0,0);
    //@ ghost_split(gr,0,0);
    //@ ghost_split(gw,0,0);
    //@ ghost_split(gw,0,0);
    //@ ghost_split(gw,0,0);
    //@ ghost_split(gw,0,0);
    //@ ghost_split(gw,0,0);
    //@ ghost_split(gw,0,0);
    //@ ghost_split(gw,0,0);
        
    //@ close thread_run_data(reader_thread)(nil,b);
    thread_start(reader_thread, b);

    //@ close thread_run_data(reader_thread)(nil,b);
    thread_start(reader_thread, b);

    //@ close thread_run_data(writer_thread)(nil,b);    
    while (true)
    /*@ invariant obs(nil) &*& thread_run_data(writer_thread)(nil,b) &*& [_]b->m |-> m &*& [_]b->vr |-> vr &*& [_]b->vw |-> vw 
                  &*& [_]b->gr |-> gr &*& [_]b->gw |-> gw &*& [_]mutex(m)
                  &*& authfrag(gr,0) &*& authfrag(gw,0) &*& authfrag(gw,0);
    @*/
    {
      //@ ghost_split(gr,0,0);
      //@ ghost_split(gw,0,0);
      //@ ghost_split(gw,0,0);
      thread_start(writer_thread, b);
      //@ close thread_run_data(writer_thread)(nil,b);    
    }
}


