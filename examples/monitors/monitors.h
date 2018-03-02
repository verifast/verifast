/*
  This module provides two synchronization constructs, mutexes and condition variables, in order to verify deadlock-freedom of programs using these synchronizers.
*/

#ifndef MONITORS_H
#define MONITORS_H

struct mutex;
struct condvar;

typedef struct mutex *mutex;
typedef struct condvar *condvar;

/*@
fixpoint unsigned int w_level(void* x);

fixpoint mutex mutex_of(void* condvar);

fixpoint list<int> X(mutex mutex);

fixpoint bool P(condvar condvar);

fixpoint predicate() Trn(condvar condvar);

fixpoint predicate(fixpoint(void*, unsigned int), fixpoint(void*, unsigned int)) inv(struct mutex* mutex);
@*/

/*@
predicate umutex(mutex mutex; fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot);

predicate mutex(mutex mutex);

predicate mutex_held(mutex mutex; real frac, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot);

predicate create_mutex_ghost_args(int wlevel, list<int> eXclusives) = true;

predicate init_mutex_ghost_args(predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) lockinv) = true;

predicate create_condvar_ghost_args(mutex mutex, int wlevel, bool spare, predicate() transfer) = emp;

predicate obs(list<void*> O);

predicate_family thread_run_data(void* thread_run)(list<void*> O, void *data);

predicate mutex_inv(mutex mutex, predicate(fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot) lockinv) = inv(mutex) == lockinv;

predicate condvar_trn(condvar condvar, predicate() condvarp) = Trn(condvar) == condvarp;
@*/

/*@
predicate no_transfer() = true;

predicate n_times(int n, predicate() p) =
  n <= 0 ? true : p() &*& n_times(n-1,p);

lemma void n_times_no_transfer(int n);
  requires true;
  ensures n_times(n,no_transfer);  
@*/

/*@
fixpoint int inc(fixpoint(void*, int) f, void* x, void* y){
    return x==y ? f(x)+1 : f(y);
}

fixpoint fixpoint(void*, unsigned int) finc(fixpoint(void*, unsigned int) f, void* x){
    return (inc)(f)(x);
}

fixpoint int dec1(int x){
  return x > 0 ? x-1 : x;
}

fixpoint int dec(fixpoint(void*, unsigned int) f, void* x, void* y){
    return x==y ? dec1(f(x)) : f(y);
}

fixpoint fixpoint(void*, int) fdec(fixpoint(void*, unsigned int) f, void* x){
    return (dec)(f)(x);
}

fixpoint int empb(void* x){
    return 0;
}

fixpoint int rma(fixpoint(void*, unsigned int) f, void* x, void* y){
    return x==y ? 0 : f(y);
}

fixpoint fixpoint(void*, int) removeAll<t>(fixpoint(void*, unsigned int) f, void* x) {
    return (rma)(f)(x); 
}
@*/

/*@
fixpoint bool eXc(void* o){ 
  return mem(w_level(o),X(mutex_of(o)));
}

fixpoint bool one_obs(condvar condvar, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return Wt(condvar) < 1 || Ot(condvar) > 0;
}

fixpoint bool spr_obs(condvar condvar, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return Wt(condvar) < 1 || Wt(condvar) < Ot(condvar);
}

fixpoint bool own_obs(condvar condvar, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return Wt(condvar) <= Ot(condvar);
}

fixpoint bool safe_obs(condvar condvar, fixpoint(void*, unsigned int) Wt, fixpoint(void*, unsigned int) Ot){ 
  return one_obs(condvar,Wt,Ot) &&
         (!P(condvar) || spr_obs(condvar,Wt,Ot)) &&
         (!eXc(condvar) || own_obs(condvar,Wt,Ot));
}
@*/

/*@
fixpoint bool w_level_below(void* o1, void* o2){
  return w_level(o1) < w_level(o2);
}

fixpoint bool w_level_below_all(void* o, list<void*> O) {
    switch (O) {
        case nil: return true;
        case cons(o1, Os): return w_level_below(o, o1) && w_level_below_all(o, Os);
    }
}

fixpoint bool w_level_below_eq_plus1(void* o1, void* o2){
  return w_level(o1) <= w_level(o2) + 1;
}

fixpoint bool w_level_below_eq_all_plus1(void* v, list<void*> O) {
    switch (O) {
        case nil: return true;
        case cons(o1, Os): return (w_level_below(v, o1) || 
                                  (eXc(o1) &&
                                   mutex_of(o1) == mutex_of(v) &&
                                   w_level_below_eq_plus1(v, o1))) && 
                                   w_level_below_eq_all_plus1(v, Os);
    }
}

fixpoint bool eXc'(void* v, void* o){
  return mem(w_level(o),X(mutex_of(v)));
}

fixpoint bool same_lock(void* v, void* o){
  return !eXc'(v,o) || mutex_of(v) == mutex_of(o);
}

fixpoint bool le_defined (void* v, list<void*> O){
  return !eXc(v) || (count(O,(eXc')(v))<=1 && forall(O,(same_lock)(v)));
}

fixpoint bool no_cycle(void* v, list<void*> O){
    return le_defined(v,O) && (w_level_below_all(v,O) || (P(v)==true && eXc(v) && w_level_below_eq_all_plus1(v,O)));
} 
@*/

/*@
lemma void init_mutex(mutex mutex);
    requires umutex(mutex, ?Wt, ?Ot) &*& init_mutex_ghost_args(?p) &*& p(Wt,Ot);
    ensures mutex(mutex) &*& inv(mutex)==p;

lemma void g_chrgu(condvar condvar);
    requires umutex(mutex_of(condvar), ?Wt, ?Ot) &*& obs(?O);
    ensures umutex(mutex_of(condvar), Wt, finc(Ot,condvar)) &*& obs(cons(condvar,O));

lemma void g_chrgl(condvar condvar);
    requires mutex_held(mutex_of(condvar), ?f, ?Wt, ?Ot) &*& obs(?O);
    ensures mutex_held(mutex_of(condvar), f, Wt, finc(Ot,condvar)) &*& obs(cons(condvar,O));

lemma void g_dischu(condvar condvar);
    requires umutex(mutex_of(condvar), ?Wt, ?Ot) &*& obs(?O) &*& safe_obs(condvar,Wt,fdec(Ot,condvar)) == true;
    ensures umutex(mutex_of(condvar), Wt, fdec(Ot,condvar)) &*& obs(remove(condvar,O));

lemma void g_dischl(condvar condvar);
    requires mutex_held(mutex_of(condvar), ?f, ?Wt, ?Ot) &*& obs(?O) &*& safe_obs(condvar,Wt,fdec(Ot,condvar)) == true;
    ensures mutex_held(mutex_of(condvar), f, Wt, fdec(Ot,condvar)) &*& obs(remove(condvar,O));
    
lemma void g_Ot_isbag(mutex mutex, condvar condvar);
    requires mutex_held(mutex, ?f, ?Wt, ?Ot);
    ensures mutex_held(mutex, f, Wt, Ot) &*& Ot(condvar) >= 0;
@*/

mutex create_mutex();
    //@ requires create_mutex_ghost_args(?wlevel,?Xs) &*& mem(wlevel,Xs) == false;
    //@ ensures result != 0 &*& umutex(result, empb ,empb) &*& mutex_of(result)==result &*& w_level(result) == wlevel &*& X(result) == Xs;
    
void mutex_acquire(mutex mutex);
    //@ requires [?f]mutex(mutex) &*& obs(?O) &*& mutex_inv(mutex, ?p) &*& no_cycle(mutex,O) == true;
    //@ ensures mutex_held(mutex, f, ?Wt, ?Ot) &*& p(Wt,Ot) &*& obs(cons(mutex,O));

void mutex_release(mutex mutex);
    //@ requires mutex_held(mutex, ?f, ?Wt, ?Ot) &*& mutex_inv(mutex,?p) &*& p(Wt, Ot) &*& obs(?O);
    //@ ensures [f]mutex(mutex) &*& obs(remove(mutex,O));

condvar create_condvar();
    //@ requires create_condvar_ghost_args(?mutex,?wlevel,?hasSpare,?transfer); 
    //@ ensures result != 0 &*& w_level(result) == wlevel &*& mutex_of(result) == mutex &*& P(result) == hasSpare &*& Trn(result) == transfer;

void condvar_wait(condvar condvar, mutex mutex);
    /*@ requires mutex_held(mutex, ?f, ?Wt, ?Ot) &*& mutex_inv(mutex,?inv) &*& inv(finc(Wt,condvar), Ot) &*& condvar_trn(condvar,?transfer) &*& obs(?O) &*&
                 no_cycle(condvar,remove(mutex,O))==true &*& no_cycle(mutex,remove(mutex,O))==true &*& safe_obs(condvar,finc(Wt,condvar),Ot)==true;@*/
    //@ ensures mutex_held(mutex, f, ?Wt', ?Ot') &*& inv(Wt', Ot') &*& obs(O) &*& transfer();

void condvar_signal(condvar condvar);
    //@ requires mutex_held(?mutex, ?f, ?Wt, ?Ot) &*& condvar_trn(condvar,?transfer) &*& (Wt(condvar) <= 0 ? true : transfer());
    //@ ensures mutex_held(mutex, f, fdec(Wt,condvar), Ot);

void condvar_broadcast(condvar condvar);
    //@ requires mutex_held(?mutex, ?f, ?Wt, ?Ot) &*& condvar_trn(condvar,?transfer) &*& n_times(Wt(condvar),transfer);
    //@ ensures mutex_held(mutex, f, removeAll(Wt,condvar), Ot);

typedef void thread_run(void* data);
    //@ requires thread_run_data(this)(?O, data) &*& obs(O);
    //@ ensures obs(nil);

/*@
fixpoint list<void*> minus (list<void*> O1, list<void*> O2){
    switch (O1){
        case nil: return nil;
        case cons(o,Os): return mem(o,O2)==true ? minus(Os,remove(o,O2)) : cons(o, minus(Os,O2));
    }
}
@*/

void thread_start(void* run, void* data);
    //@ requires is_thread_run(run) == true &*& thread_run_data(run)(?tobs, data) &*& obs(?obs);
    //@ ensures obs(minus(obs,tobs));
            
#endif    
