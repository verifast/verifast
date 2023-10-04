// Tobias Reinhard and Bart Jacobs. Ghost signals: verifying termination of busy-waiting. 2020.

#include "../mutex.h"

struct message;
typedef struct message *message;

//@ predicate message(message message; int id);

//@ predicate receive_(predicate() P, int messageId, predicate() Q);
//@ predicate send_(predicate() P, int messageId, predicate() Q);

message receive();
//@ requires receive_(?P, ?id, ?Q) &*& P();
//@ ensures message(result, id) &*& Q() &*& result != 0;
//@ terminates;

void send(message message);
//@ requires message(message, ?id) &*& send_(?P, id, ?Q) &*& P();
//@ ensures Q();
//@ terminates;

/*@

copredicate receive_all(predicate() P, int i) =
  receive_(P, i, ?Q) &*&
  receive_all(Q, i + 1);
  
predicate False() = false;

copredicate send_all(predicate() P, int i, int k) =
  send_(P, i, ?Q) &*& k == i ? Q == False : send_all(Q, i + 1, k);

@*/

message buffer;
struct g { // TODO: Support global ghost variables. This is a workaround.
  //@ int nextToEnqueue;
  //@ int nextToDequeue;
};
struct g g;
mutex mut;

/*@

fixpoint int N() { return 1 + mutex_nb_level_dims; }
fixpoint level L(int level) { return level(main, {N, level}); }

predicate wait_perms(list<void *> ss, int level, void *f) =
  switch (ss) {
    case nil: return true;
    case cons(s, ss0): return
      wait_perm({}, s, L(level), f) &*&
      wait_perms(ss0, level + 2, f);
  };

predicate mutex_inv_aux(int k, list<void *> ses, list<void *> sds; int ne, int nd) =
  [1/2]g.nextToEnqueue |-> ne &*& ne <= k + 2 &*&
  [1/2]g.nextToDequeue |-> nd &*& 0 <= nd &*& nd <= ne &*& nd <= k + 1 &*&
  signal(nth(ne, ses), L(2*ne+1), false) &*&
  signal(nth(nd, sds), L(2*nd+2), false) &*&
  buffer |-> ?m &*& 
  m == 0 ?
    nd == ne
  :
    message(m, nd) &*& ne == nd + 1;

predicate_ctor mutex_inv(int k, list<void *> ses, list<void *> sds)() =
  mutex_inv_aux(k, ses, sds, ?ne, ?nd);

@*/

void sender()
/*@
requires
    [1/2]g.nextToDequeue |-> 0 &*&
    send_all(?P0, 0, ?k) &*& P0() &*& 0 <= k &*&
    exists<pair<list<void *>, list<void *> > >(pair(?ses, ?sds)) &*&
    [_]mut |-> ?mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(k, ses, sds)) &*&
    length(ses) == k + 3 &*& length(sds) == k + 2 &*&
    wait_perms(ses, 1, sender) &*&
    foreachp(drop(1, sds), signal_uninit) &*&
    obs({Forkee}, {pair(nth(0, sds), L(2))});
@*/
//@ ensures false;
//@ terminates;
{
  for (;;)
  /*@
  invariant
      [1/2]g.nextToDequeue |-> ?i &*& i <= k &*&
      send_all(?P, i, k) &*& 0 <= i &*& P() &*&
      [_]mut |-> mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(k, ses, sds)) &*&
      wait_perms(drop(i, ses), 1 + 2*i, sender) &*&
      obs({Forkee}, {pair(nth(i, sds), L(2 + 2 * i))}) &*&
      foreachp(drop(i + 1, sds), signal_uninit);
  @*/
  //@ decreases k - i;
  {
    for (;;)
    /*@
    invariant
        [1/2]g.nextToDequeue |-> i &*&
        send_all(P, i, k) &*& P() &*&
        [_]mut |-> mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(k, ses, sds)) &*&
        wait_perms(drop(i, ses), 1 + 2*i, sender) &*&
        obs({Forkee}, {pair(nth(i, sds), L(2 + 2 * i))}) &*&
        foreachp(drop(i + 1, sds), signal_uninit);
    @*/
    {
      acquire(mut);
      //@ open mutex_inv(k, ses, sds)();
      //@ open mutex_inv_aux(k, ses, sds, ?ne, ?nd);
      message message = buffer;
      if (message == 0) {
        /*@
        predicate pre() = mutex_inv_aux(k, ses, sds, ne, nd) &*& wait_perms(drop(i, ses), 1 + 2 * i, sender);
        predicate post() = call_perm_(currentThread, sender) &*& wait_perms(drop(i, ses), 1 + 2 * i, sender);
        @*/
        /*@
        produce_lemma_function_pointer_chunk release_ghost_op(
            currentThread, {Forkee}, {pair(nth(i, sds), L(2 + 2 * i))}, mutex_inv(k, ses, sds), pre, post)() {
          open pre();
          open mutex_inv_aux(k, ses, sds, ne, nd);
          open wait_perms(drop(i, ses), 1 + 2 * i, sender);
          drop_n_plus_one(i, ses);
          wait(nth(i, ses));
          close wait_perms(drop(i, ses), 1 + 2 * i, sender);
          close mutex_inv(k, ses, sds)();
          close post();
        };
        @*/
        //@ close pre();
        release_with_ghost_op(mut);
        //@ open post();
      } else {
        buffer = 0;
        //@ set_signal(nth(i, sds));
        //@ leak signal(nth(i, sds), L(2 + 2 * i), true);
        //@ g.nextToDequeue++;
        //@ open foreachp(drop(i + 1, sds), signal_uninit);
        //@ drop_n_plus_one(i + 1, sds);
        //@ init_signal(nth(i + 1, sds), L(4 + 2 * i));
        //@ close mutex_inv(k, ses, sds)();
        release(mut);
        //@ open send_all(P, i, k);
        send(message);
        //@ if (k == i) open False();
        //@ drop_n_plus_one(i, ses);
        //@ open wait_perms(drop(i, ses), 1 + 2 * i, sender);
        //@ leak wait_perm({}, nth(i, ses), L(1 + 2 * i), sender);
        break;
      }
    }
  }
}

void receiver()
/*@
requires
    [1/2]g.nextToEnqueue |-> 0 &*&
    receive_all(?P0, 0) &*& P0() &*&
    exists<int>(?k) &*& 0 <= k &*&
    exists<pair<list<void *>, list<void *> > >(pair(?ses, ?sds)) &*&
    length(ses) == k + 3 &*& length(sds) == k + 2 &*&
    [_]mut |-> ?mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(k, ses, sds)) &*&
    wait_perms(sds, 2, receiver) &*&
    obs({Forker}, {pair(nth(0, ses), L(1))}) &*&
    foreachp(drop(1, ses), signal_uninit);
@*/
//@ ensures false;
//@ terminates;
{
  for (;;)
  /*@
  invariant
      [1/2]g.nextToEnqueue |-> ?i &*&
      receive_all(?P, i) &*& 0 <= i &*& P() &*&
      [_]mut |-> mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(k, ses, sds)) &*&
      (i == 0 ? wait_perms(sds, 2, receiver) : wait_perms(drop(i - 1, sds), 2 * i, receiver)) &*&
      obs({Forker}, {pair(nth(i, ses), L(1 + 2 * i))}) &*&
      foreachp(drop(i + 1, ses), signal_uninit);
  @*/
  //@ decreases k + 3 - i;
  {
    //@ open receive_all(P, i);
    message m = receive();
    for (;;)
    /*@
    invariant
        [1/2]g.nextToEnqueue |-> i &*& message(m, i) &*&
        [_]mut |-> mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(k, ses, sds)) &*&
        (i == 0 ? wait_perms(sds, 2, receiver) : wait_perms(drop(i - 1, sds), 2 * i, receiver)) &*&
        obs({Forker}, {pair(nth(i, ses), L(1 + 2 * i))}) &*&
        foreachp(drop(i + 1, ses), signal_uninit);
    @*/
    {
      acquire(mut);
      //@ open mutex_inv(k, ses, sds)();
      //@ open mutex_inv_aux(k, ses, sds, ?ne, ?nd);
      if (buffer == 0) {
        buffer = m;
        //@ set_signal(nth(i, ses));
        //@ leak signal(nth(i, ses), L(1 + 2 * i), true);
        //@ g.nextToEnqueue++;
        //@ open foreachp(drop(i + 1, ses), signal_uninit);
        //@ drop_n_plus_one(i + 1, ses);
        //@ init_signal(nth(i + 1, ses), L(3 + 2 * i));
        //@ close mutex_inv(k, ses, sds)();
        release(mut);
        /*@
        if (i != 0) {
          open wait_perms(drop(i - 1, sds), 2 * i, receiver);
          drop_n_plus_one(i - 1, sds);
          leak wait_perm({}, nth(i - 1, sds), L(2 * i), receiver);
        }
        @*/
        break;
      } else {
        /*@
        predicate pre() =
          mutex_inv_aux(k, ses, sds, ne, nd) &*& wait_perms(drop(i - 1, sds), 2 * i, receiver);
        predicate post() =
          call_perm_(currentThread, receiver) &*& wait_perms(drop(i - 1, sds), 2 * i, receiver);
        @*/
        /*@
        produce_lemma_function_pointer_chunk release_ghost_op(
            currentThread, {Forker}, {pair(nth(i, ses), L(1 + 2 * i))}, mutex_inv(k, ses, sds), pre, post)() {
          open pre();
          open mutex_inv_aux(k, ses, sds, ne, nd);
          open wait_perms(drop(i - 1, sds), 2 * i, receiver);
          drop_n_plus_one(i - 1, sds);
          wait(nth(i - 1, sds));
          close wait_perms(drop(i - 1, sds), 2 * i, receiver);
          close mutex_inv(k, ses, sds)();
          close post();
        };
        @*/
        //@ close pre();
        release_with_ghost_op(mut);
        //@ open post();
      }
    }
  }
}

int main() //@ : custom_main_spec
/*@
requires
    module(echo_live_mt, true) &*&
    obs({}, {}) &*&
    receive_all(?Pr, 0) &*& send_all(?Ps, 0, ?k) &*& Pr() &*& Ps() &*& 0 <= k;
@*/
//@ ensures false;
//@ terminates;
{
  //@ open_module();
  //@ g.nextToEnqueue = 0;
  //@ g.nextToDequeue = 0;
  
  //@ close foreachp(nil, signal_uninit);
  //@ close wait_perms(nil, 7 + 2 * k, sender);
  /*@
  for (int n = 0; n < k + 3; n++)
    invariant
      n <= k + 3 &*&
      obs({}, {}) &*&
      foreachp(?ses, signal_uninit) &*&
      wait_perms(ses, 7 + 2 * (k - n), sender) &*&
      length(ses) == n;
    decreases k + 3 - n;
  {
    int i = k + 3 - n - 1;
    void *s = create_signal();
    close foreachp(cons(s, ses), signal_uninit);
    produce_call_below_perm_();
    pathize_call_below_perm_();
    create_wait_perm(s, L(1 + 2 * i), sender);
    close wait_perms(cons(s, ses), 1 + 2 * i, sender);
  }
  @*/
  //@ assert foreachp(?ses, signal_uninit);
  //@ list<void *> sds = nil;
  //@ close foreachp(sds, signal_uninit);
  //@ close wait_perms(sds, 6 + 2 * k, receiver);
  /*@
  for (int n = 0; n < k + 2; n++)
    invariant
      n <= k + 2 &*&
      obs({}, {}) &*&
      foreachp(sds, signal_uninit) &*&
      wait_perms(sds, 2 + 2 * (k + 2 - n), receiver) &*&
      length(sds) == n;
    decreases k + 2 - n;
  {
    int i = k + 2 - n - 1;
    void *s = create_signal();
    sds = cons(s, sds);
    close foreachp(sds, signal_uninit);
    produce_call_below_perm_();
    pathize_call_below_perm_();
    create_wait_perm(s, L(2 + 2 * i), receiver);
    close wait_perms(sds, 2 + 2 * i, receiver);
  }
  @*/
  
  //@ open foreachp(ses, signal_uninit);
  //@ init_signal(nth(0, ses), L(1));
  //@ open foreachp(sds, signal_uninit);
  //@ init_signal(nth(0, sds), L(2));
  //@ close mutex_inv_aux(k, ses, sds, 0, 0);
  //@ close mutex_inv(k, ses, sds)();
  //@ close exists(mutex_inv(k, ses, sds));
  //@ close exists(L(0));
  mut = create_mutex();
  {
    /*@
    predicate sender_pre() =
      [1/2]g.nextToDequeue |-> 0 &*&
      send_all(Ps, 0, k) &*& Ps() &*&
      [_]mut |-> ?mutex &*& [1/2]mutex(mutex, L(0), mutex_inv(k, ses, sds)) &*&
      wait_perms(ses, 1, sender) &*&
      foreachp(drop(1, sds), signal_uninit);
    @*/
    /*@
    produce_function_pointer_chunk thread_run(sender)({}, {pair(nth(0, sds), L(2))}, sender_pre)() {
      open sender_pre();
      close exists(pair(ses, sds));
      call();
    }
    @*/
    //@ leak mut |-> _;
    //@ close exists(pair(ses, sds));
    //@ close sender_pre();
    fork(sender);
  }
  //@ close exists(k);
  receiver();
}
