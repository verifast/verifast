// Tobias Reinhard and Bart Jacobs. Ghost signals: verifying termination of busy-waiting. 2020.

#include "mutex.h"

mutex m;
int producerNext = 100;
int consumerNext = 100;

/*@

fixpoint int N() { return 1 + mutex_nb_level_dims; }
fixpoint level L(int level) { return level(main, {N, level}); }

predicate wait_perms(list<void *> ss, int level, void *f) =
  switch (ss) {
    case nil: return true;
    case cons(s, ss0): return
      wait_perm({}, s, L(level), f) &*&
      wait_perms(ss0, level + 1, f);
  };

predicate_ctor mutex_inv(list<void *> sps, list<void *> scs)(;) = mutex_inv_aux(sps, scs, _, _);

predicate mutex_inv_aux(list<void *> sps, list<void *> scs; int cp, int cc) =
  [1/2]producerNext |-> cp &*&
  [1/2]consumerNext |-> cc &*&
  0 <= cp &*& cp <= cc &*& cc <= 100 &*&
  (
    cp == 0 ?
      true
    :
      signal(nth(100 - cp, sps), L(101 - cp), false)
  ) &*&
  (
    cc <= 10 ?
      true
    :
      signal(nth(100 - cc, scs), L(102 - cc), false)
  );

@*/

void producer()
//@ requires exists(pair(?sps, ?scs)) &*& [_]m |-> ?mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(sps, scs)) &*& [1/2]producerNext |-> 100 &*& obs({Forkee}, {pair(nth(0, sps), L(1))}) &*& foreachp(drop(1, sps), signal_uninit) &*& length(sps) == 100 &*& length(scs) == 90 &*& wait_perms(scs, 2, producer);
//@ ensures obs({Forkee}, {});
//@ terminates;
{
  //@ open exists(_);
  for (;;)
  //@ invariant [1/2]producerNext |-> ?cp &*& 0 < cp &*& cp <= 100 &*& obs({Forkee}, {pair(nth(100 - cp, sps), L(101 - cp))}) &*& [_]m |-> mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(sps, scs)) &*& foreachp(drop(101 - cp, sps), signal_uninit) &*& wait_perms(scs, 2, producer);
  //@ decreases cp; // For this loop, we don't consume call_perms
  {
    //@ void *sp = nth(100 - cp, sps);
    for (;;)
    //@ invariant [1/2]producerNext |-> cp &*& obs({Forkee}, {pair(sp, L(101 - cp))}) &*& [_]m |-> mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(sps, scs)) &*& foreachp(drop(101 - cp, sps), signal_uninit) &*& wait_perms(scs, 2, producer);
    {
      acquire(m);
      //@ open mutex_inv(sps, scs)();
      //@ open mutex_inv_aux(sps, scs, _, ?cc);
      if (consumerNext - producerNext < 10) {
        producerNext--;
        //@ set_signal(sp);
        //@ leak signal(sp, L(101 - cp), true);
        //@ open foreachp(drop(101 - cp, sps), signal_uninit);
        if (producerNext == 0) {
          //@ close mutex_inv_aux(sps, scs, cp - 1, cc);
          //@ close mutex_inv(sps, scs)();
          release(m);
          //@ leak wait_perms(scs, 2, producer) &*& [1/2]producerNext |-> _ &*& [1/2]mutex(mutex, L(0), mutex_inv(sps, scs));
          return;
        } else {
          //@ drop_n_plus_one(101 - cp, sps);
          //@ void *new_sp = nth(101 - cp, sps);
          //@ init_signal(new_sp, L(101 - producerNext));
          //@ close mutex_inv_aux(sps, scs, cp - 1, cc);
          //@ close mutex_inv(sps, scs)();
          release(m);
          break;
        }
      } else {
        /*@
        predicate pre() = mutex_inv_aux(sps, scs, cp, cc) &*& wait_perms(scs, 2, producer);
        predicate post() = call_perm_(currentThread, producer) &*& wait_perms(scs, 2, producer);
        @*/
        /*@
        produce_lemma_function_pointer_chunk release_ghost_op(currentThread, {Forkee}, {pair(sp, L(101 - cp))}, mutex_inv(sps, scs), pre, post)() {
          open pre();
          open mutex_inv_aux(sps, scs, cp, cc);
          void *sc = nth(100 - cc, scs);
          {
            lemma void iter(int i)
              requires wait_perms(drop(100 - i, scs), 102 - i, producer) &*& obs({Forkee}, {pair(sp, L(101 - cp))}) &*& signal(sc, L(102 - cc), false) &*& cc <= i &*& i <= 100;
              ensures wait_perms(drop(100 - i, scs), 102 - i, producer) &*& obs({Forkee}, {pair(sp, L(101 - cp))}) &*& signal(sc, L(102 - cc), false) &*& call_perm_(currentThread, producer);
            {
              open wait_perms(drop(100 - i, scs), 102 - i, producer);
              drop_n_plus_one(100 - i, scs);
              if (i == cc) {
                wait(sc);
              } else {
                iter(i - 1);
              }
              close wait_perms(drop(100 - i, scs), 102 - i, producer);
            }
            iter(100);
          }
          close post();
          close mutex_inv_aux(sps, scs, cp, cc);
          close mutex_inv(sps, scs)();
        };
        @*/
        //@ close mutex_inv_aux(sps, scs, cp, cc);
        //@ close pre();
        release_with_ghost_op(m);
        //@ open post();
      }
    }
  }
}

void consumer()
//@ requires [1/2]consumerNext |-> 100 &*& [_]m |-> ?mutex &*& exists(pair(?sps, ?scs)) &*& [1/2]mutex(mutex, L(0), mutex_inv(sps, scs)) &*& foreachp(drop(1, scs), signal_uninit) &*& length(sps) == 100 &*& length(scs) == 90 &*& wait_perms(sps, 1, consumer) &*& obs({Forker}, {pair(nth(0, scs), L(2))});
//@ ensures obs(_, {});
//@ terminates;
{
  for (;;)
  //@ invariant [1/2]consumerNext |-> ?cc &*& 0 < cc &*& cc <= 100 &*& obs({Forker}, cc <= 10 ? {} : {pair(nth(100 - cc, scs), L(102 - cc))}) &*& [_]m |-> mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(sps, scs)) &*& wait_perms(sps, 1, consumer) &*& cc <= 10 ? true : foreachp(drop(101 - cc, scs), signal_uninit);
  //@ decreases cc;
  {
    //@ void *sc = nth(100 - cc, scs);
    //@ assert obs(_, ?obs);
    for (;;)
    //@ invariant [1/2]consumerNext |-> cc &*& obs({Forker}, obs) &*& [_]m |-> mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(sps, scs)) &*& wait_perms(sps, 1, consumer) &*& cc <= 10 ? true : foreachp(drop(101 - cc, scs), signal_uninit);
    {
      acquire(m);
      //@ open mutex_inv(sps, scs)();
      //@ open mutex_inv_aux(sps, scs, ?cp, _);
      if (producerNext < consumerNext) {
        /*@
        if (cc > 10) {
          set_signal(sc);
          leak signal(sc, L(102 - cc), true);
        }
        @*/
        consumerNext--;
        if (consumerNext == 0) {
          //@ close mutex_inv_aux(sps, scs, cp, _);
          //@ close mutex_inv(sps, scs)();
          release(m);
          //@ leak wait_perms(sps, 1, consumer) &*& [1/2]consumerNext |-> 0 &*& [1/2]mutex(mutex, L(0), mutex_inv(sps, scs));
          return;
        } else {
          /*@
          {
            if (cc <= 11) {
            } else {
              open foreachp(drop(101 - cc, scs), signal_uninit);
              drop_n_plus_one(101 - cc, scs);
              void *new_sc = nth(101 - cc, scs);
              init_signal(new_sc, L(102 - consumerNext));
            }
            close mutex_inv_aux(sps, scs, cp, cc - 1);
            close mutex_inv(sps, scs)();
          }
          @*/
          release(m);
          break;
        }
      } else {
        /*@
        predicate pre() = mutex_inv_aux(sps, scs, cp, cc) &*& wait_perms(sps, 1, consumer);
        predicate post() = call_perm_(currentThread, consumer) &*& wait_perms(sps, 1, consumer);
        @*/
        /*@
        produce_lemma_function_pointer_chunk release_ghost_op(currentThread, {Forker}, obs, mutex_inv(sps, scs), pre, post)() {
          open pre();
          open mutex_inv_aux(sps, scs, cp, cc);
          void *sp = nth(100 - cp, sps);
          {
            lemma void iter(int i)
              requires wait_perms(drop(100 - i, sps), 101 - i, consumer) &*& obs({Forker}, obs) &*& signal(sp, L(101 - cp), false) &*& cp <= i &*& i <= 100;
              ensures wait_perms(drop(100 - i, sps), 101 - i, consumer) &*& obs({Forker}, obs) &*& signal(sp, L(101 - cp), false) &*& call_perm_(currentThread, consumer);
            {
              open wait_perms(drop(100 - i, sps), 101 - i, consumer);
              drop_n_plus_one(100 - i, sps);
              if (i == cp) {
                wait(sp);
              } else {
                iter(i - 1);
              }
              close wait_perms(drop(100 - i, sps), 101 - i, consumer);
            }
            iter(100);
          }
          close post();
          close mutex_inv_aux(sps, scs, cp, cc);
        };
        @*/
        //@ close mutex_inv_aux(sps, scs, cp, cc);
        //@ close pre();
        release_with_ghost_op(m);
        //@ open post();
      }
    }
  }
}

int main() //@ : custom_main_spec
//@ requires obs({}, {}) &*& module(bounded_fifo, true);
//@ ensures obs(_, {});
//@ terminates;
{
  //@ open_module();
  
  //@ close foreachp(nil, signal_uninit);
  //@ close wait_perms(nil, 101, consumer);
  /*@
  for (int i = 0; i < 100; i++)
    invariant obs({}, {}) &*& foreachp(?sps, signal_uninit) &*& length(sps) == i &*& wait_perms(sps, 101 - i, consumer) &*& i <= 100;
    decreases 100 - i;
  {
    void *s = create_signal();
    close foreachp(cons(s, sps), signal_uninit);
    produce_call_below_perm_();
    pathize_call_below_perm_();
    create_wait_perm(s, L(100 - i), consumer);
    close wait_perms(cons(s, sps), 100 - i, consumer);
  }
  @*/
  //@ assert foreachp(?sps, signal_uninit) &*& length(sps) == 100;
  
  //@ close wait_perms(nil, 92, producer);
  //@ close foreachp(nil, signal_uninit);
  //@ list<void *> scs = nil;
  /*@
  for (int i = 0; i < 90; i++)
    invariant obs({}, {}) &*& foreachp(scs, signal_uninit) &*& length(scs) == i &*& wait_perms(scs, 92 - i, producer) &*& i <= 90;
    decreases 90 - i;
  {
    void *s = create_signal();
    close foreachp(cons(s, scs), signal_uninit);
    produce_call_below_perm_();
    pathize_call_below_perm_();
    create_wait_perm(s, L(91 - i), producer);
    close wait_perms(cons(s, scs), 91 - i, producer);
    scs = cons(s, scs);
  }
  @*/
  //@ assert foreachp(scs, signal_uninit) &*& length(scs) == 90;
  
  //@ void *sp0 = nth(0, sps);
  //@ open foreachp(sps, signal_uninit);
  //@ init_signal(sp0, L(1));
  //@ void *sc0 = nth(0, scs);
  //@ open foreachp(scs, signal_uninit);
  //@ init_signal(sc0, L(2));
  //@ close mutex_inv_aux(sps, scs, 100, 100);
  //@ close mutex_inv(sps, scs)();
  //@ close exists(L(0));
  //@ close exists<predicate()>(mutex_inv(sps, scs));
  m = create_mutex();
  //@ leak m |-> _;
  {
    /*@
    predicate producer_pre() =
      [1/2]producerNext |-> 100 &*& [_]m |-> ?mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(sps, scs)) &*& foreachp(tail(sps), signal_uninit) &*& wait_perms(scs, 2, producer);
    @*/
    /*@
    produce_function_pointer_chunk thread_run(producer)({}, {pair(sp0, L(1))}, producer_pre)() {
      open producer_pre();
      close exists(pair(sps, scs));
      call();
    }
    @*/
    //@ close producer_pre();
    fork(producer);
  }
  //@ close exists(pair(sps, scs));
  consumer();
  return 0;
}
