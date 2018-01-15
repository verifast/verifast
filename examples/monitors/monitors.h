/*
  This module provieds two synchronization constructs, including mutexes and condition variables, in order to verifiy deadlock-freedom of programs using these synchronizers.
*/


#ifndef MONITORS_H
#define MONITORS_H

struct mutex;
struct mutex_cond;

/*@
predicate umutex(struct mutex *mutex; fixpoint(void*, int) Wt, fixpoint(void*, unsigned int) Ot);

predicate mutex(struct mutex *mutex);

predicate mutex_held(struct mutex *mutex; real frac, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot);

predicate create_mutex_ghost_args(int wlevel, list<int> eXclusives) = true;

predicate init_mutex_ghost_args(predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) lockinv) = true;

predicate create_mutex_cond_ghost_args(struct mutex *mutex, int wlevel, bool spare, predicate() condp) = emp;

predicate obs(list<void*> O);

predicate_family thread_run_data(void *thread_run)(list<void*> tobs, void *data);

predicate mutex_inv(struct mutex *mutex, predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) lockinv) = inv(mutex) == lockinv;

predicate cond_trn(struct mutex_cond *cond, predicate() condp) = Trn(cond) == condp;

predicate cond_trns(int n, predicate() p) =
  n<=0 ? true : p() &*& cond_trns(n-1,p);
@*/

/*@
fixpoint unsigned int w_level(void* x);

fixpoint struct mutex* mutex_of (void* cond);

fixpoint list<int> X (struct mutex *mutex);

fixpoint bool P (struct mutex_cond *cond);

fixpoint predicate() Trn (struct mutex_cond *cond);

fixpoint predicate(fixpoint(void*, unsigned int), fixpoint(void*, unsigned int)) inv (struct mutex *mutex);
@*/

/*@

fixpoint int inc(fixpoint(void*, int) f, void* x, void* y){
    return x==y ? f(x)+1 : f(y);
}

fixpoint fixpoint(void*, unsigned int) finc(fixpoint(void*, int) f, void* x){
    return (inc)(f)(x);
}

fixpoint int dec1(int x){
  return x > 0 ? x-1 : x;
}

fixpoint int dec(fixpoint(void*, int) f, void* x, void* y){
    return x==y ? dec1(f(x)) : f(y);
}

fixpoint fixpoint(void*, int) fdec(fixpoint(void*, int) f, void* x){
    return (dec)(f)(x);
}

fixpoint int empb(void* x){
    return 0;
}

fixpoint int rma(fixpoint(void*, int) f, void* x, void* y){
    return x==y ? 0 : f(y);
}

fixpoint fixpoint(void*, int) removeAll<t>(fixpoint(void*, int) f, void* x) {
    return (rma)(f)(x); 
}

lemma void init_mutex(struct mutex *mutex);
    requires umutex(mutex, ?Wt, ?Ot) &*& init_mutex_ghost_args(?p) &*& p(Wt,Ot);
    ensures mutex(mutex) &*& inv(mutex)==p;

lemma void g_chrgu(struct mutex_cond *cond);
    requires umutex(mutex_of(cond), ?Wt, ?Ot) &*& obs(?O);
    ensures umutex(mutex_of(cond), Wt, finc(Ot,cond)) &*& obs(cons(cond,O));

lemma void g_chrgl(struct mutex_cond *cond);
    requires mutex_held(mutex_of(cond), ?f, ?Wt, ?Ot) &*& obs(?O);
    ensures mutex_held(mutex_of(cond), f, Wt, finc(Ot,cond)) &*& obs(cons(cond,O));

lemma void g_dischu(struct mutex_cond *cond);
    requires umutex(mutex_of(cond), ?Wt, ?Ot) &*& obs(?O) &*& safe_obs(cond,Wt,fdec(Ot,cond)) == true;
    ensures umutex(mutex_of(cond), Wt, fdec(Ot,cond)) &*& obs(remove(cond,O));

lemma void g_dischl(struct mutex_cond *cond);
    requires mutex_held(mutex_of(cond), ?f, ?Wt, ?Ot) &*& obs(?O) &*& safe_obs(cond,Wt,fdec(Ot,cond)) == true;
    ensures mutex_held(mutex_of(cond), f, Wt, fdec(Ot,cond)) &*& obs(remove(cond,O));

lemma void g_Ot_isbag(struct mutex *mutex, struct mutex_cond *cond);
    requires mutex_held(mutex, ?f, ?Wt, ?Ot);
    ensures mutex_held(mutex, f, Wt, Ot) &*& Ot(cond) >= 0;
@*/

/*@
fixpoint bool id (void* o1, void* o2){
  return o1==o2 ? true : false;
}

fixpoint bool eXc(void* o){ return mem(w_level(o),X(mutex_of(o)));}

fixpoint bool one_obs(struct mutex_cond *cond, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return Wt(cond) < 1 || Ot(cond) > 0;
}

fixpoint bool spr_obs(struct mutex_cond *cond, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return Wt(cond) < 1 || Wt(cond) < Ot(cond);
}

fixpoint bool own_obs(struct mutex_cond *cond, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return Wt(cond) <= Ot(cond);
}

fixpoint bool safe_obs(struct mutex_cond *cond, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return one_obs(cond,Wt,Ot) 
  &&         (!P(cond) || spr_obs(cond,Wt,Ot)) &&
         (!eXc(cond) || own_obs(cond,Wt,Ot))
  ;
}
@*/

/*@
fixpoint bool w_level_below(void* l1, void* l2){
  return w_level(l1) < w_level(l2);
}

fixpoint bool w_level_below_all(void* r, list<void*> os) {
    switch (os) {
        case nil: return true;
        case cons(o, os0): return w_level_below(r, o) && w_level_below_all(r, os0);
    }
}

fixpoint bool w_level_below_eq_1(void* l1, void* l2){
  return w_level(l1) <= w_level(l2) + 1;
}

fixpoint bool w_level_below_eq_all_1(void* r, list<void*> os) {
    switch (os) {
        case nil: return true;
        case cons(o, os0): return (w_level_below(r, o) || 
                                  (
                                  eXc(o) &&
                                  w_level_below_eq_1(r, o))) 
                                  && w_level_below_eq_all_1(r, os0);
    }
}

fixpoint bool eXc'(void* v, void* o){
  return mem(w_level(o),X(mutex_of(v)));
}

fixpoint bool slock(void* v, void* o){
  return !mem(w_level(o),X(mutex_of(v))) || mutex_of(v) == mutex_of(o);
}

fixpoint bool le_defined (void* v, list<void*> O){
  return !eXc(v) || (count(O,(eXc')(v))<=1 && forall(O,(slock)(v)));
}

fixpoint bool no_cycle(void* v, list<void*> O){
    return le_defined(v,O) && (w_level_below_all(v,O) || w_level_below_eq_all_1(v,O));
} 
@*/

/*@
fixpoint int app(fixpoint(void*, int) f, void* x){
    return f(x);
}

lemma void g_inbag<t>(fixpoint(void*, unsigned int) B, void* b);
  requires true;
  ensures app(finc(B,b),b) > 0;
@*/            
struct mutex *create_mutex();
    //@ requires create_mutex_ghost_args(?w,?Xs);
    //@ ensures result != 0 &*& umutex(result, empb ,empb) &*& mutex_of(result)==result &*& w_level(result) == w &*& X(result) == Xs;
    
void mutex_acquire(struct mutex *mutex);
    //@ requires [?f]mutex(mutex) &*& obs(?os) &*& mutex_inv(mutex, ?p) &*& no_cycle(mutex,os)==true ;//no_cycle(mutexId,os,mutexId)==true;
    //@ ensures mutex_held(mutex, f, ?Wt, ?Ot) &*& p(Wt,Ot) &*& obs(cons(mutex,os));

void mutex_release(struct mutex *mutex);
    //@ requires mutex_held(mutex, ?f, ?Wt, ?Ot) &*& mutex_inv(mutex,?p) &*& p(Wt, Ot) &*& obs(?os);
    //@ ensures [f]mutex(mutex) &*& obs(remove(mutex,os));

struct mutex_cond *create_mutex_cond();
    //@ requires create_mutex_cond_ghost_args(?mutex,?w,?hasSpare,?condp); 
    //@ ensures result != 0 &*& w_level(result) == w &*& mutex_of(result) == mutex &*& P(result) == hasSpare &*& Trn(result) == condp;

void mutex_cond_wait(struct mutex_cond *cond, struct mutex *mutex);
    /*@ requires mutex_held(mutex, ?f, ?Wt, ?Ot) &*& mutex_inv(mutex,?p) &*& p(finc(Wt,cond), Ot) &*& obs(?O) 
          &*& no_cycle(cond,remove(mutex,O))==true &*& no_cycle(mutex,remove(mutex,O))==true &*& safe_obs(cond,finc(Wt,cond),Ot)==true
          &*& cond_trn(cond,?pr);
    @*/
    //@ ensures mutex_held(mutex, f, ?Wt', ?Ot') &*& p(Wt', Ot') &*& obs(O) &*& pr();// &*& resume();

void mutex_cond_signal(struct mutex_cond *cond);
    //@ requires mutex_held(?mutex, ?f, ?Wt, ?Ot) &*& cond_trn(cond,?pr) &*& (Wt(cond) <= 0 ? true : pr());
    //@ ensures mutex_held(mutex, f, fdec(Wt,cond), Ot);

void mutex_cond_broadcast(struct mutex_cond *cond);
    //@ requires mutex_held(?mutex, ?f, ?Wt, ?Ot) &*& cond_trn(cond,?pr) &*& cond_trns(Wt(cond),pr);
    //@ ensures mutex_held(mutex, f, removeAll(Wt,cond), Ot);

typedef void thread_run(void *data);
    //@ requires thread_run_data(this)(?tobs, data) &*& obs(tobs);
    //@ ensures obs(nil);

/*@
fixpoint list<void*> minus (list<void*> obs1, list<void*> obs2){
    switch (obs1){
        case nil: return nil;
        case cons(h,t): return mem(h,obs2)==true ? minus(t,remove(h,obs2)) : cons(h, minus(t,obs2));
    }
}

@*/

void thread_start(void *run, void *data);
    //@ requires is_thread_run(run) == true &*& thread_run_data(run)(?tobs, data) &*& obs(?obs);
    //@ ensures obs(minus(obs,tobs));
            
#endif    
