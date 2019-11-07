/*
  A Sleeping Barber Program Synchronized Using Monitors: Verification of Deadlock-Freedom
*/

#include "stdlib.h"
#include "monitors.h"
//@ #include "ghost_counters.gh"

struct barbershop {
   int barber;
   int chair;
   int door;
   struct mutex *m;
   struct condvar *cbarber;
   struct condvar *cchair;
   struct condvar *cdoor;
   struct condvar *ccustomer;
   //@ int gba;
   //@ int gch;
   //@ int gdo;
   //@ int gcu;
};

/*@
predicate protected_permissions(struct barbershop *b; int barber, int chair, int door, struct condvar *cbarber, struct condvar *cchair, struct condvar *cdoor, struct condvar *ccustomer, struct mutex *m) =
  b->barber |-> barber &*& b->chair |-> chair &*& b->door |-> door
  &*& [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer &*& [_]b->m |-> m
  &*& mutex_of(cbarber) == m &*& mutex_of(cchair) == m &*& mutex_of(cdoor) == m &*& mutex_of(ccustomer) == m  
  &*& cbarber != cchair &*& cbarber != cdoor &*&  cbarber != ccustomer &*& cchair != cdoor &*& cchair != ccustomer &*& cdoor != ccustomer
  &*& barber >= 0 &*& chair >= 0 &*& door >= 0
  &*& P(cbarber) == false &*& P(cchair) == false &*& P(cdoor) == false &*& P(ccustomer) == false; 

predicate_ctor barbershop(struct barbershop *b)(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) = 
  protected_permissions(b,?barber,?chair,?door,?cbarber,?cchair,?cdoor,?ccustomer,?m)
  &*& [_]b->gba |-> ?gba &*& [_]b->gch |-> ?gch &*& [_]b->gdo |-> ?gdo &*& [_]b->gcu |-> ?gcu
  &*& ctr(gba,?Cba) &*& ctr(gch,?Cch) &*& ctr(gdo,?Cdo) &*& ctr(gcu,?Ccu)
  &*& Wt(cbarber) + Cba <= Ot(cbarber) + barber
  &*& Wt(cbarber) <= Ot(cbarber)
  &*& Wt(cdoor) + Cdo <= Ot(cdoor) + door
  &*& Wt(cdoor) <= Ot(cdoor)
  &*& Wt(cchair) + Cch <= Ot(cchair) + chair
  &*& Wt(cchair) <= Ot(cchair)
  &*& Wt(ccustomer) + Ccu + door <= Ot(ccustomer) + 1
  &*& Wt(ccustomer) <= Ot(ccustomer);

predicate unprotected_permissions(struct barbershop *b, struct condvar *cbarber, struct condvar *cchair, struct condvar *cdoor, struct condvar *ccustomer, int gba, int gch, int gdo, int gcu, struct mutex *m) =
  [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer &*& [_]b->m |-> m
  &*& inv(m) == barbershop(b) &*& mutex_of(cbarber) == m &*& mutex_of(cchair) == m &*& mutex_of(cdoor) == m &*& mutex_of(ccustomer) == m
  &*& [_]b->gba |-> gba &*& [_]b->gch |-> gch &*& [_]b->gdo |-> gdo &*& [_]b->gcu |-> gcu
  &*& Trn(cbarber) == vtrn(gba) &*& Trn(cchair) == vtrn(gch) &*& Trn(cdoor) == vtrn(gdo) &*& Trn(ccustomer) == vtrn(gcu);

predicate_ctor vtrn(int i)() = tic(i);
    
@*/
  
/*@
predicate_family_instance thread_run_data(get_haircut_thread)(list<void*> tobs, struct barbershop *b) =
  unprotected_permissions(b,?cbarber,?cchair,?cdoor,?ccustomer,?gba,?gch,?gdo,?gcu,?m)
  &*& [_]mutex(m)
  &*& no_cycle(m,cons(cchair,cons(ccustomer,nil)))==true 
  &*& no_cycle(cbarber,cons(cchair,cons(ccustomer,nil)))==true   
  &*& no_cycle(cdoor,cons(ccustomer,nil))==true
  &*& tobs == cons(cchair,cons(ccustomer,nil)) &*& tic(gba) &*& tic(gdo);
  
predicate_family_instance thread_run_data(finished_cut_customer_thread)(list<void*> tobs, struct barbershop *b) =
  unprotected_permissions(b,?cbarber,?cchair,?cdoor,?ccustomer,?gba,?gch,?gdo,?gcu,?m)
  &*& [_]mutex(m)
  &*& no_cycle(m,cons(cdoor,nil))==true 
  &*& no_cycle(ccustomer,nil)==true
  &*& tobs == cons(cdoor,nil) &*& tic(gcu) &*& tic(gcu);

predicate_family_instance thread_run_data(get_next_customer_thread)(list<void*> tobs, struct barbershop *b) =
  unprotected_permissions(b,?cbarber,?cchair,?cdoor,?ccustomer,?gba,?gch,?gdo,?gcu,?m)
  &*& [_]mutex(m)
  &*& no_cycle(m,cons(cbarber,nil))==true 
  &*& no_cycle(cchair,nil)==true
  &*& tobs == cons(cbarber,nil) &*& tic(gch);
@*/

void get_haircut1(struct barbershop *b)
  /*@ requires unprotected_permissions(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer, ?gba, ?gch, ?gdo, ?gcu, ?m) &*& [_]mutex(m)
    &*& obs(cons(cchair,cons(ccustomer,?O))) &*& tic(gba) &*& tic(gdo)
    &*& no_cycle(m,cons(cchair,cons(ccustomer,O)))==true 
    &*& no_cycle(cbarber,cons(cchair,cons(ccustomer,O)))==true   
    &*& no_cycle(cdoor,cons(ccustomer,O))==true;
  @*/
  //@ ensures unprotected_permissions(b, cbarber, cchair, cdoor, ccustomer, gba, gch, gdo, gcu, m) &*& [_]mutex(m) &*& obs(O);
{
  //@ open unprotected_permissions(_,_,_,_,_,_,_,_,_,_);
  //@ close mutex_inv(m, barbershop(b));
  mutex_acquire(b->m);
  //@ open barbershop(b)(_,_);
  while (b->barber==0)
    /*@ invariant [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer
          &*& [_]b->m |-> m &*& b->barber |-> ?barber &*& b->chair |-> ?chair &*& b->door |-> ?door
          &*& barber >= 0 &*& chair >= 0 &*& door >= 0 &*& mutex_held(m, _, ?Wt, ?Ot)
          &*& [_]b->gba |-> gba &*& [_]b->gch |-> gch &*& [_]b->gdo |-> gdo &*& [_]b->gcu |-> gcu
          &*& ctr(gba,?Cba) &*& ctr(gch,?Cch) &*& ctr(gdo,?Cdo) &*& ctr(gcu,?Ccu)
          &*& Wt(cbarber) + Cba <= Ot(cbarber) + barber
          &*& Wt(cbarber) <= Ot(cbarber)
          &*& Wt(cdoor) + Cdo <= Ot(cdoor) + door
          &*& Wt(cdoor) <= Ot(cdoor)
          &*& Wt(cchair) + Cch <= Ot(cchair) + chair
          &*& Wt(cchair) <= Ot(cchair)
          &*& Wt(ccustomer) + Ccu + door <= Ot(ccustomer) + 1
          &*& Wt(ccustomer) <= Ot(ccustomer)     
          &*& obs(cons(m,cons((void*)cchair,cons(ccustomer,O)))) &*& tic(gba) &*& tic(gdo);
    @*/
  {
    //@ dec_ctr(gba);
    //@ close barbershop(b)(finc(Wt,cbarber),Ot);
    //@ close mutex_inv(m,barbershop(b));
    //@ close condvar_trn(cbarber,vtrn(gba));
    condvar_wait(b->cbarber, b->m);
    //@ open barbershop(b)(_,_); 
    //@ open vtrn(gba)();  
  }
  b->barber = b->barber - 1;
  b->chair = b->chair + 1;
  //@ close condvar_trn(cchair,vtrn(gch));
  /*@ if (Wt(cchair)>0){
        inc_ctr(gch);
        close vtrn(gch)();
      }
  @*/
  condvar_signal(b->cchair);
  //@ g_dischl(cchair);
  //@ dec_ctr(gba);
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close barbershop(b)(Wte,Ote);
  //@ close mutex_inv(m, barbershop(b));
  mutex_release(b->m);
  //@ leak [_]mutex(m);
  //@ close unprotected_permissions(b,cbarber,cchair,cdoor,ccustomer,gba,gch,gdo,gcu,m); 
  get_haircut2(b);
  //@ leak [_]mutex(m);
}


void get_haircut2(struct barbershop *b)
  /*@ requires unprotected_permissions(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer, ?gba, ?gch, ?gdo, ?gcu, ?m) &*& [_]mutex(m)
    &*& obs(cons(ccustomer,?O)) &*& tic(gdo)
    &*& no_cycle(m,cons(cchair,cons(ccustomer,O)))==true 
    &*& no_cycle(cbarber,cons(cchair,cons(ccustomer,O)))==true   
    &*& no_cycle(cdoor,cons(ccustomer,O))==true;
  @*/
  //@ ensures unprotected_permissions(b, cbarber, cchair, cdoor, ccustomer, gba, gch, gdo, gcu, m) &*& [_]mutex(m) &*& obs(O);
{
  //@ open unprotected_permissions(_,_,_,_,_,_,_,_,_,_);
  //@ close mutex_inv(m, barbershop(b));
  mutex_acquire(b->m);
  //@ open barbershop(b)(_,_);
  while (b->door==0)
    /*@ invariant [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer
          &*& [_]b->m |-> m &*& b->barber |-> ?barber &*& b->chair |-> ?chair &*& b->door |-> ?door
          &*& barber >= 0 &*& chair >= 0 &*& door >= 0 &*& mutex_held(m, _, ?Wt, ?Ot)
          &*& [_]b->gba |-> gba &*& [_]b->gch |-> gch &*& [_]b->gdo |-> gdo &*& [_]b->gcu |-> gcu
          &*& ctr(gba,?Cba) &*& ctr(gch,?Cch) &*& ctr(gdo,?Cdo) &*& ctr(gcu,?Ccu)
          &*& Wt(cbarber) + Cba <= Ot(cbarber) + barber
          &*& Wt(cbarber) <= Ot(cbarber)
          &*& Wt(cdoor) + Cdo <= Ot(cdoor) + door
          &*& Wt(cdoor) <= Ot(cdoor)
          &*& Wt(cchair) + Cch <= Ot(cchair) + chair
          &*& Wt(cchair) <= Ot(cchair)
          &*& Wt(ccustomer) + Ccu + door <= Ot(ccustomer) + 1
          &*& Wt(ccustomer) <= Ot(ccustomer)     
          &*& obs(cons(m,cons((void*)ccustomer,O))) &*& tic(gdo);
    @*/
  {
    //@ dec_ctr(gdo);
    
    //@ close barbershop(b)(finc(Wt,cdoor),Ot);
    //@ close mutex_inv(m,barbershop(b));
    //@ close condvar_trn(cdoor,vtrn(gdo));
    condvar_wait(b->cdoor, b->m);
    //@ open barbershop(b)(_,_);  
    //@ open vtrn(gdo)();
  }
  b->door = b->door - 1;
  //@ close condvar_trn(ccustomer,vtrn(gcu));
  /*@ if (Wt(ccustomer)>0){
        inc_ctr(gcu);
        close vtrn(gcu)();
      }
  @*/
  condvar_signal(b->ccustomer);
  //@ g_dischl(ccustomer);
  //@ dec_ctr(gdo);
  //@ assert mutex_held(m,_,?Wte,?Ote);
  //@ close barbershop(b)(Wte,Ote);
  //@ close mutex_inv(m, barbershop(b));
  mutex_release(b->m);
  //@ leak [_]mutex(m);
  //@ close unprotected_permissions(_,_,_,_,_,_,_,_,_,_);  
}  

void get_next_customer(struct barbershop *b)
  /*@ requires unprotected_permissions(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer, ?gba, ?gch, ?gdo, ?gcu, ?m) &*& [_]mutex(m)
    &*& obs(cons(cbarber,?O)) &*& tic(gch)
    &*& no_cycle(m,cons(cbarber,O))==true 
    &*& no_cycle(cchair,O)==true;
  @*/
  /*@
  ensures unprotected_permissions(b, cbarber, cchair, cdoor, ccustomer, gba, gch, gdo, gcu, m) &*& [_]mutex(m) &*& obs(O);
@*/
{
  //@ open unprotected_permissions(_,_,_,_,_,_,_,_,_,_);
  //@ close mutex_inv(m, barbershop(b));
  mutex_acquire(b->m);
  //@ open barbershop(b)(?Wt0,?Ot0);
  if (b->barber <= 0)
    abort();
  b->barber = b->barber + 1;
  //@ close condvar_trn(cbarber,vtrn(gba));
  /*@ if (Wt0(cbarber)>0){
        inc_ctr(gba);
        close vtrn(gba)();
      }
  @*/
  condvar_signal(b->cbarber);   
  //@ g_dischl(cbarber);
  while (b->chair==0)
    /*@ invariant [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer
          &*& [_]b->m |-> m &*& b->barber |-> ?barber &*& b->chair |-> ?chair &*& b->door |-> ?door
          &*& barber >= 0 &*& chair >= 0 &*& door >= 0 &*& mutex_held(m, _, ?Wt, ?Ot)
          &*& [_]b->gba |-> gba &*& [_]b->gch |-> gch &*& [_]b->gdo |-> gdo &*& [_]b->gcu |-> gcu
          &*& ctr(gba,?Cba) &*& ctr(gch,?Cch) &*& ctr(gdo,?Cdo) &*& ctr(gcu,?Ccu)
          &*& Wt(cbarber) + Cba <= Ot(cbarber) + barber
          &*& Wt(cbarber) <= Ot(cbarber)
          &*& Wt(cdoor) + Cdo <= Ot(cdoor) + door
          &*& Wt(cdoor) <= Ot(cdoor)
          &*& Wt(cchair) + Cch <= Ot(cchair) + chair
          &*& Wt(cchair) <= Ot(cchair)
          &*& Wt(ccustomer) + Ccu + door <= Ot(ccustomer) + 1
          &*& Wt(ccustomer) <= Ot(ccustomer)     
          &*& obs(cons(m,O)) &*& tic(gch);
    @*/
  {
    //@ dec_ctr(gch);
    //@ close barbershop(b)(finc(Wt,cchair),Ot);
    //@ close mutex_inv(m,barbershop(b));
    //@ close condvar_trn(cchair,vtrn(gch));
    condvar_wait(b->cchair, b->m);
    //@ open barbershop(b)(_,_);  
    //@ open vtrn(gch)();
  }    
  b->chair = b->chair - 1;
  //@ dec_ctr(gch);
  //@ close barbershop(b)(Wt,Ot);
  //@ close mutex_inv(m, barbershop(b));
  mutex_release(b->m);
  //@ leak [_]mutex(m);  
  //@ close unprotected_permissions(_,_,_,_,_,_,_,_,_,_);
}

void finished_cut_customer(struct barbershop *b)
  /*@ requires unprotected_permissions(b, ?cbarber, ?cchair, ?cdoor, ?ccustomer, ?gba, ?gch, ?gdo, ?gcu, ?m) &*& [_]mutex(m)
    &*& obs(cons(cdoor,?O)) &*& tic(gcu) &*& tic(gcu)
    &*& no_cycle(m,cons(cdoor,O))==true 
    &*& no_cycle(ccustomer,O)==true;
  @*/
  //@ ensures unprotected_permissions(b, cbarber, cchair, cdoor, ccustomer, gba, gch, gdo, gcu, m) &*& [_]mutex(m) &*& obs(O);
{
  //@ open unprotected_permissions(_,_,_,_,_,_,_,_,_,_);
  //@ close mutex_inv(m, barbershop(b));  
  mutex_acquire(b->m);
  //@ open barbershop(b)(?Wt0,?Ot0);
  b->door = b->door + 1;
  //@ close condvar_trn(cdoor,vtrn(gdo));
  /*@ if (Wt0(cdoor)>0){
        inc_ctr(gdo);
        close vtrn(gdo)();
      }
  @*/
  condvar_signal(b->cdoor);
  //@ g_dischl(cdoor);
  //@ dec_ctr(gcu);
  while (b->door>0)
    /*@ invariant [_]b->cbarber |-> cbarber &*& [_]b->cchair |-> cchair &*& [_]b->cdoor |-> cdoor &*& [_]b->ccustomer |-> ccustomer
          &*& [_]b->m |-> m &*& b->barber |-> ?barber &*& b->chair |-> ?chair &*& b->door |-> ?door
          &*& barber >= 0 &*& chair >= 0 &*& door >= 0 &*& mutex_held(m, _, ?Wt, ?Ot)
          &*& [_]b->gba |-> gba &*& [_]b->gch |-> gch &*& [_]b->gdo |-> gdo &*& [_]b->gcu |-> gcu
          &*& ctr(gba,?Cba) &*& ctr(gch,?Cch) &*& ctr(gdo,?Cdo) &*& ctr(gcu,?Ccu)
          &*& Wt(cbarber) + Cba <= Ot(cbarber) + barber
          &*& Wt(cbarber) <= Ot(cbarber)
          &*& Wt(cdoor) + Cdo <= Ot(cdoor) + door
          &*& Wt(cdoor) <= Ot(cdoor)
          &*& Wt(cchair) + Cch <= Ot(cchair) + chair
          &*& Wt(cchair) <= Ot(cchair)
          &*& Wt(ccustomer) + Ccu + door <= Ot(ccustomer) + 1
          &*& Wt(ccustomer) <= Ot(ccustomer)     
          &*& obs(cons(m,O)) &*& tic(gcu);
    @*/
  {
    //@ dec_ctr(gcu);   
    //@ close barbershop(b)(finc(Wt,ccustomer),Ot);
    //@ close mutex_inv(m,barbershop(b));
    //@ close condvar_trn(ccustomer,vtrn(gcu));
    condvar_wait(b->ccustomer, b->m);
    //@ open barbershop(b)(_,_); 
    //@ open vtrn(gcu)(); 
  }
  //@ close barbershop(b)(Wt,Ot);
  //@ close mutex_inv(m, barbershop(b));
  mutex_release(b->m);
  //@ leak [_]mutex(m);
  //@ close unprotected_permissions(_,_,_,_,_,_,_,_,_,_);
  //@ leak tic(gcu);
}

void get_haircut_thread(struct barbershop *b)  //@ : thread_run
    //@ requires thread_run_data(get_haircut_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(get_haircut_thread)(_,_);
  get_haircut1(b);
  //@ open unprotected_permissions(_,_,_,_,_,_,_,_,_,_);  
}

void finished_cut_customer_thread(struct barbershop *b)  //@ : thread_run
    //@ requires thread_run_data(finished_cut_customer_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(finished_cut_customer_thread)(_,_);
  finished_cut_customer(b);
  //@ open unprotected_permissions(_,_,_,_,_,_,_,_,_,_);  
}

void get_next_customer_thread(struct barbershop *b)  //@ : thread_run
    //@ requires thread_run_data(get_next_customer_thread)(?tobs,b) &*& obs(tobs);
    //@ ensures obs(nil);
{
  //@ open thread_run_data(get_next_customer_thread)(_,_);
  get_next_customer(b);
  //@ open unprotected_permissions(_,_,_,_,_,_,_,_,_,_);  
}

int main() //@ : custom_main_spec
    //@ requires obs(nil);
    //@ ensures obs(nil);
{
    //@ close create_mutex_ghost_args(0,nil);
    struct mutex *m = create_mutex();
    
    //@ int gba = new_ctr();
    //@ close create_condvar_ghost_args(m,1,false,vtrn(gba));
    struct condvar *cbarber = create_condvar();

    //@ int gch = new_ctr();
    //@ close create_condvar_ghost_args(m,2,false,vtrn(gch));
    struct condvar *cchair = create_condvar();

    //@ int gdo = new_ctr();
    //@ close create_condvar_ghost_args(m,3,false,vtrn(gdo));
    struct condvar *cdoor = create_condvar();
    
    //@ int gcu = new_ctr();
    //@ close create_condvar_ghost_args(m,4,false,vtrn(gcu));
    struct condvar *ccustomer = create_condvar();
    
    struct barbershop *b = malloc(sizeof(struct barbershop));
    if (b==0)
      abort();
    b->m = m;
    b->barber = 0;
    b->chair = 0;
    b->door = 0;
    b->cbarber = cbarber;
    b->cchair = cchair;
    b->cdoor = cdoor;
    b->ccustomer = ccustomer;
    //@ b->gba = gba;
    //@ b->gch = gch;
    //@ b->gdo = gdo;
    //@ b->gcu = gcu;
    
    //@ leak [_]b->cbarber |-> _;
    //@ leak [_]b->cchair |-> _;
    //@ leak [_]b->cdoor |-> _;
    //@ leak [_]b->ccustomer |-> _;            
    //@ leak [_]b->m |-> _;  
    //@ leak [_]b->gba |-> _;               
    //@ leak [_]b->gch |-> _;               
    //@ leak [_]b->gdo |-> _;               
    //@ leak [_]b->gcu |-> _;               
    //@ leak [_]malloc_block_barbershop(_);
    
    //@ close init_mutex_ghost_args(barbershop(b));
    //@ g_chrgu(cbarber);    
    //@ g_chrgu(cchair);    
    //@ g_chrgu(cdoor);    
    //@ g_chrgu(ccustomer);    
    //@ inc_ctr(gba);
    //@ inc_ctr(gch);
    //@ inc_ctr(gdo);
    //@ inc_ctr(gcu);
    //@ inc_ctr(gcu);
    //@ close barbershop(b)(empb,finc(finc(finc(finc(empb,cbarber),cchair),cdoor),ccustomer));    
    //@ init_mutex(m);
    //@ leak [_]mutex(m);
    
    //@ close unprotected_permissions(b,_,_,_,_,_,_,_,_,_);
    //@ close thread_run_data(get_haircut_thread)(cons(cchair,(cons(ccustomer,nil))),b);
    thread_start(get_haircut_thread, b);

    //@ close unprotected_permissions(b,_,_,_,_,_,_,_,_,_);
    //@ close thread_run_data(get_next_customer_thread)(cons(cbarber,nil),b);
    thread_start(get_next_customer_thread, b);

    //@ close unprotected_permissions(b,_,_,_,_,_,_,_,_,_);
    //@ close thread_run_data(finished_cut_customer_thread)(cons(cdoor,nil),b);
    thread_start(finished_cut_customer_thread, b);

    return 0;
}
